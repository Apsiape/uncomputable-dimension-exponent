"""Independent, single-threaded attacks on the profile claim. No imported input code."""
import os
for key in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):
    os.environ[key] = '1'
from fractions import Fraction as F
from itertools import product
from math import log2, ceil, floor, sqrt
import json
from pathlib import Path
import numpy as np

out = {}

# A checker-state attack: remove its overflow point instead of repairing the carry.
# Diagonal sqrt(rho) makes permutation/state commutators directly computable.
rows = []
for N in range(2,13):
    d = 1 << N
    v = np.ones(d) / sqrt(d-1)
    v[-1] = 0
    flip_error = float(np.linalg.norm(v-v[np.arange(d)^1]))
    increment_error = float(np.linalg.norm(v-np.roll(v,1)))
    target = 4.0**(-N)
    assert abs(flip_error-sqrt(2/(d-1))) < 1e-12
    assert flip_error > target and increment_error > target
    rows.append(dict(N=N, flip_state_error=flip_error, target_precision=target))
out['overflow_point_removal_attack'] = rows

# Shared checker with genuinely noncommuting calibration inputs.
# Every checker label has a 2x2 source block; there is no tensor factor per calibrator.
N=3; d=1 << N; eye=np.eye(2)
proj0=np.diag([1.,0.]); proj1=np.array([[.5,.5],[.5,.5]])
inputs=[(.75,proj0),(.1875,proj1)]
f=[1,0,1,1,0,1]; g=[1,0,0,1,0,0]

def fg(h): return f[h%len(f)],g[h%len(g)]
def hist(t,h):
    if t==0: return 0.,0.,1.,0.,0.
    ell=floor(log2(1/t))
    j=k=hstop=0
    while k<ell:
        ff,gg=fg(hstop); j+=ff; k+=gg; hstop+=1
    penalty=2.**(-j-1)
    jh=kh=0
    for v in range(min(h,hstop)):
        ff,gg=fg(v); jh+=ff; kh+=gg
    return 2.**kh*t, 2.**jh*penalty, float(h<=hstop),float(h==hstop),penalty

def block(t,p,h):
    z=np.array(hist(0,h)); a=np.array(hist(t,h))
    return [z[i]*eye+(a[i]-z[i])*p for i in range(5)]

def trailing_ones(q):
    r=0
    while r<N and q&(1<<r): r+=1
    return r

worst=0.; cross=0.; equations=0; domain_min=1.; domain_max=0.
for fuel,time in product(range(d),repeat=2):
    period=1 << trailing_ones(fuel)
    h=time%period; hn=(time+1)%period; zp=float(hn==0)
    blocks=[]
    for t,p in inputs:
        C,D,R,P,S=block(t,p,h)
        Cn,Dn,Rn,Pn,Sn=block(t,p,hn)
        ff,gg=fg(h)
        residuals=[(eye-R)@P,(D-.5*eye)@P,
            Rn-zp*eye-(1-zp)*(R-P),
            Cn-zp*t*p-(1-zp)*C@(eye+gg*(R-P)),
            Dn-zp*S-(1-zp)*D@(eye+ff*(R-P))]
        if h==0: residuals += [C-t*p,R-eye]
        for left,right in product((C,D,R,P,S,t*p),repeat=2):
            residuals.append(left@right-right@left)
        for x in (C,D,R,P,S,t*p):
            ev=np.linalg.eigvalsh(x)
            domain_min=min(domain_min,float(ev.min())); domain_max=max(domain_max,float(ev.max()))
        for x in residuals:
            worst=max(worst,float(np.linalg.norm(x))); equations+=1
        blocks.append((C,D,R,P,S))
    cross=max(cross,float(np.linalg.norm(blocks[0][0]@blocks[1][0]-blocks[1][0]@blocks[0][0])))
assert worst<1e-12 and domain_min>=-1e-12 and domain_max<=1+1e-12 and cross>.01
out['noncommuting_shared_calibrators'] = dict(checker_labels=d*d, source_block_dimension=2,
    calibrators=2,equations_checked=equations,max_residual=worst,
    max_cross_calibrator_C_commutator=cross,domain_min=domain_min,domain_max=domain_max)

# Greedy tracking attacked with all 3^8 bounded-jitter target words.
worst=F(0); cases=0
for noise in product((-1,0,1),repeat=8):
    k=0
    for j,e in enumerate(noise,1):
        tau=F(j,2)+e
        k+=int(k<tau)
        worst=max(worst,abs(F(k)-tau))
        assert abs(F(k)-tau)<=3 # c=2 and tau(0)=0
    cases+=1
out['greedy_tracking'] = dict(target_words=cases,steps_per_word=8,max_error=str(worst),bound=3)

# Affine pair normalization, including very small L and large U.
pairs=[]
for L,U in [(F(1,1000),F(1,500)),(F(1,4),F(1,4)),(F(2,3),F(20)),(F(100),F(101))]:
    q=floor(1/(2*L))+1; m=ceil(4*q*U-2)
    lo=(4*q*L-2)/m; hi=(4*q*U-2)/m
    assert 0<lo<=hi<=1 and F(2+m*lo,4*q)==L and F(2+m*hi,4*q)==U
    pairs.append(dict(L=str(L),U=str(U),q=q,m=m,normalized=[str(lo),str(hi)]))
out['affine_parameters'] = pairs

# Independent hold-stage accounting, with adversarial readiness and denominator changes.
J=1; K=1; physical=1; max_ratio=1.; stages=[]
targets=[F(1,5),F(4,5),F(1,4),F(3,4),F(2,7),F(5,7),F(1,3)]
active=F(1); start=J
for s,new in enumerate(targets,1):
    p,q=active.numerator,active.denominator
    hold=(s+2)*J
    bg=(s%3+1)*new.denominator**2 + 17*s*s
    length=ceil(max(hold,bg)/q)*q
    end=J+length
    old_ratio=F(K,J)
    K+=p*(length//q)
    expected=F(J,end)*old_ratio+F(length,end)*active
    assert F(K,end)==expected
    assert abs(F(K,end)-active)<=F(1,s+3)
    assert end>=new.denominator**2
    physical+=10*length+3*(s+2)*J+3*(q+new.denominator+1)
    max_ratio=max(max_ratio,physical/(end+1)**2)
    stages.append(dict(s=s,J_start=J,J_end=end,active=str(active),density=str(F(K,end))))
    J=end; active=new
out['independent_hold_schedule'] = dict(stages=stages,max_time_over_J_squared=max_ratio)

# Decoder margin under bounded o(n)-sized endpoint errors.
checks=0
for i in range(2,30):
    n=4**i
    for b in (0,1):
        true_increment=F(3*n,4)*(1+2*b)
        for e1,e2 in product((-F(n,100),F(n,100)),repeat=2):
            decoded=int(true_increment+e2-e1>F(3*n,2))
            assert decoded==b;checks+=1
out['diagonal_decoder_margin'] = dict(cases=checks,max_endpoint_error_fraction='1/100')

path=Path(__file__).with_name('independent_checks.json')
path.write_text(json.dumps(out,indent=2),encoding='utf-8')
print(json.dumps({key: value if key not in ('overflow_point_removal_attack','affine_parameters','independent_hold_schedule') else 'PASS; details in JSON' for key,value in out.items()},indent=2))
print('ALL INDEPENDENT CHECKS PASSED')
