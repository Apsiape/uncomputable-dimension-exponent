"""Single-threaded finite-history and scaling checks for the proposed calibrator."""
import os
for name in ['OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS']:
    os.environ[name]='1'
import json
import math
from pathlib import Path
import numpy as np

ROOT=Path(__file__).resolve().parent

def rotate(mask,n):
    return ((mask<<1)&((1<<n)-1))|(mask>>(n-1))

def unrotate(mask,n):
    return (mask>>1)|((mask&1)<<(n-1))

def clock_check(n):
    size=1<<n
    P=np.diag([x&1 for x in range(size)]).astype(float)
    U=np.zeros((size,size));T=U.copy();X=U.copy()
    for x in range(size):
        U[(x+1)%size,x]=1
        T[rotate(x,n),x]=1
        X[x^1,x]=1
    error=U-X@(np.eye(size)-P+(T@U@T.T)@P)
    actual=np.linalg.norm(error,'fro')/math.sqrt(size)
    expected=math.sqrt(2/size)
    assert abs(actual-expected)<1e-14
    A=np.diag([sum(3*4**(-j-1)*((x>>j)&1) for j in range(n)) for x in range(size)])
    assert np.linalg.norm(T@A@T.T-4*A+3*P-3*4**(-n)*P)<1e-14
    return {'clock_bits':n,'unguarded_flat_defect':actual,'formula':expected}

def scalar_history(m,q,lam):
    if lam==0:
        return None,0.
    j=0
    while m**(j+1)*lam<=1+1e-15:
        j+=1
    S=q**(-j-1)
    return j,S

def finite_model(m,q,n):
    eigenvalues=[0.,m**(-8),0.007,0.03,0.1,0.27,0.5,1.]
    size=1<<n
    maximum=0.
    for lam in eigenvalues:
        j,S=scalar_history(m,q,lam)
        for fuel in range(size):
            k=next((i for i in range(n) if not (fuel>>i&1)),n)
            period=1<<k
            def state(time):
                h=time%period
                stop=(j is not None and h==j)
                run=(j is None or h<=j)
                count=h if j is None else min(h,j)
                return (m**count*lam,q**count*S,float(run),float(stop))
            for time in range(size):
                C,D,H,P=state(time)
                Cn,Dn,Hn,Pn=state((time+1)%size)
                Z=float(time%period==0)
                Zn=float((time+1)%period==0)
                errors=[Z*(C-lam),Z*(D-S),Z*(H-1),
                        Cn-Zn*lam-(1-Zn)*C*(1+(m-1)*(H-P)),
                        Dn-Zn*S-(1-Zn)*D*(1+(q-1)*(H-P)),
                        Hn-Zn-(1-Zn)*(H-P),(D-1/q)*P]
                assert 0<=C<=1+1e-14 and 0<=D<=1+1e-14 and P<=H
                maximum=max(maximum,max(abs(x) for x in errors))
                # Check the actual finite reset recursion, including all-one fuel.
                tailfuel=unrotate(fuel,n);tailtime=unrotate(time,n)
                ktail=next((i for i in range(n) if not (tailfuel>>i&1)),n)
                Ztail=float(tailtime%(1<<ktail)==0)
                rhs=1-(fuel&1)+(fuel&1)*(1-(time&1))*Ztail
                assert Z==rhs
        if lam:
            beta=math.log(m)/math.log(q)
            assert S<=lam**(1/beta)+1e-13
            assert lam<=m*S**beta+1e-13
    assert maximum<1e-12
    return {'m':m,'q':q,'beta':math.log(m)/math.log(q),'clock_bits':n,
            'input_eigenvalues':eigenvalues,'max_new_equation_error':maximum}

def noncommuting_state_checks():
    rng=np.random.default_rng(20261028)
    records=[]
    for m,q in [(2,3),(2,5),(3,5),(3,7)]:
        beta=math.log(m)/math.log(q)
        values=np.array([0.,m**(-8),0.03,0.17,0.5,1.])
        S=np.array([scalar_history(m,q,x)[1] for x in values])
        Z=rng.normal(size=(len(values),len(values)))+1j*rng.normal(size=(len(values),len(values)))
        rho=Z@Z.conj().T;rho/=np.trace(rho)
        tnorm=math.sqrt(float(np.trace(rho@np.diag(values**2)).real))
        snorm=math.sqrt(float(np.trace(rho@np.diag(S**2)).real))
        assert tnorm<=m*snorm**beta+1e-12
        records.append({'m':m,'q':q,'T_weighted_norm':tnorm,'S_weighted_norm':snorm,
                        'Holder_bound':m*snorm**beta,
                        'state_input_commutator':float(np.linalg.norm(rho@np.diag(values)-np.diag(values)@rho))})
    return records

if __name__=='__main__':
    binary_stop=[{'n':n,'time_zero_stop_residual':abs(1/n-0.5)} for n in (2,3,4,8)]
    assert binary_stop[0]['time_zero_stop_residual']==0
    assert all(row['time_zero_stop_residual']>0 for row in binary_stop[1:])
    data={'clocks':[clock_check(n) for n in [2,3,4,5]],
          'finite_models':[finite_model(m,q,n) for m,q in [(2,3),(2,5),(3,5)] for n in [3,4]],
          'noncommuting_states':noncommuting_state_checks(),
          'binary_time_zero_stop':binary_stop,
          'greater_than_one_obstruction':[
              {'mass':w,'T_norm':math.sqrt(w),'S_norm':math.sqrt(w)/2,
               'ratio_to_S_power_1_5':math.sqrt(w)/(math.sqrt(w)/2)**1.5}
              for w in [1e-2,1e-4,1e-6]]}
    (ROOT/'calibrator-checks.json').write_text(json.dumps(data,indent=2),encoding='utf-8')
    print(json.dumps(data,indent=2))
