"""Small matrix attack on the held-tuple and initialized-corner identities with nonstationary data and a selector mixture."""
import os
for k in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[k]='1'
import numpy as np,json
from pathlib import Path
O=Path(__file__).resolve().parent;rng=np.random.default_rng(20261027)
T=8;rv=np.array([1,.5,.25,.125,0]);ns=len(rv);d=2;n=T*ns*d
I2=np.eye(2);Z=np.diag([1.,0.]);X=np.array([[1,1],[1,1]])/2;Y=np.array([[1,-1j],[1j,1]])/2
projs=[Z,Z,X,X,X,Y,Y,Y]
unitaries=[2*P-I2 for P in projs]
def bd(blocks):
    out=np.zeros((sum(b.shape[0] for b in blocks),)*2,dtype=complex);off=0
    for b in blocks:out[off:off+len(b),off:off+len(b)]=b;off+=len(b)
    return out
G=bd([np.linalg.qr(rng.normal(size=(d,d))+1j*rng.normal(size=(d,d)))[0] for t in range(T) for s in range(ns)])
shift=np.roll(np.eye(T),1,axis=0);U0=np.kron(shift,np.eye(ns*d));U=G@U0@G.conj().T
R=np.kron(np.eye(T),np.kron(np.diag(rv),I2))
At=np.kron(np.diag([sum(3*((t>>j)&1)/4**(j+1) for j in range(3)) for t in range(T)]),np.eye(ns*d))
Q0=np.kron(np.diag([1.]+[0.]*(T-1)),np.eye(ns*d))
LOAD=np.kron(np.diag([0.,1.,0.,0.,1.,0.,0.,0.]),np.eye(ns*d))
Zplus=np.kron(np.diag([0.]*(T-1)+[1.]),np.eye(ns*d));eye=np.eye(n)
matrices=[G@bd([projs[t] for t in range(T) for s in range(ns)])@G.conj().T,
          G@bd([I2-projs[t] for t in range(T) for s in range(ns)])@G.conj().T,
          G@bd([unitaries[t] for t in range(T) for s in range(ns)])@G.conj().T]
norm=lambda a:float(np.linalg.norm(a,2))
results={'dimension':n,'data_do_not_commute_with_U':[],'data_guard_residuals':[],'shifted_Q0_commutators':[],'same_tuple_residuals':[]}
assert norm(U.conj().T@U-eye)<1e-12
for A in matrices:
    assert norm(A@At-At@A)<1e-12 and norm(A@R-R@A)<1e-12
    results['data_do_not_commute_with_U'].append(norm(U@A-A@U))
    residual=(U.conj().T@A@U-A)@(eye-Zplus)@(eye-LOAD)
    results['data_guard_residuals'].append(norm(residual));assert norm(residual)<1e-12
    shifts=[np.linalg.matrix_power(U.conj().T,h)@A@np.linalg.matrix_power(U,h) for h in range(T)]
    for h,A_h in enumerate(shifts):
        err=norm(A_h@Q0-Q0@A_h);results['shifted_Q0_commutators'].append(err);assert err<1e-12
        if h<T-1 and h not in (1,4):
            err=norm((shifts[h+1]-A_h)@Q0);results['same_tuple_residuals'].append(err);assert err<1e-12
    assert norm(U@A-A@U)>.1
# Stop-sector identity (16.12) on the survivor corner after previous STOP sectors are removed.
j=2;survive=np.kron(np.eye(T),np.kron(np.diag([0.,0.,1.,1.,1.]),I2))
cvals=np.where(rv==0,0,np.minimum(1,4*rv));c=np.kron(np.eye(T),np.kron(np.diag(cvals),I2))
z=np.kron(np.eye(T),np.kron(np.diag(cvals==1),I2));target=np.kron(np.eye(T),np.kron(np.diag(rv==.25),I2))
assert norm((c-4*R)@survive)==0 and norm(survive@z-survive@target)==0
for A in matrices:assert norm(A@survive@target-survive@target@A)<1e-12
results['selector_eigenvalues']=rv.tolist();results['counter_on_survivors']=norm((c-4*R)@survive);results['stop_sector']=norm(survive@z-survive@target)
# Negative control: data mixing distinct time-coordinate eigenspaces loses Q0 reduction.
bad=np.kron(np.roll(np.eye(T),1,axis=0),np.eye(ns*d));results['dropped_coordinate_commutation']=norm(bad@Q0-Q0@bad);assert results['dropped_coordinate_commutation']>.1
results['max_guard_residual']=max(results['data_guard_residuals']);results['max_shifted_commutator']=max(results['shifted_Q0_commutators']);results['max_fixed_tuple_residual']=max(results['same_tuple_residuals']);results['passed']=True
(O/'matrix-interface-results.json').write_text(json.dumps(results,indent=2));print(json.dumps({k:v for k,v in results.items() if k not in ('shifted_Q0_commutators','same_tuple_residuals')},indent=2))
