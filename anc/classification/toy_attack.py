"""Single-threaded stop-or-continue toy attack (Section 16). All output stays beside this script.
Scalar arithmetic is simulated at semantic instruction level, not as a compiled
universal Minsky machine. Gate registers use exact dyadic Gaussian matrices.
Full address/fuel/time matrices are never allocated; their blocks are checked.
"""
import os
for key in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):os.environ[key]='1'
os.environ['PYTHONDONTWRITEBYTECODE']='1'
from pathlib import Path
from fractions import Fraction as Q
from dataclasses import dataclass,replace
import json,math,time,hashlib
import numpy as np
import psutil
OUT=Path(__file__).resolve().parent
ALPHA=Q(11,20);DIM=16;I=np.eye(DIM,dtype=complex);ZERO=np.zeros_like(I)
COUNT={'blocks':0,'physical_time_points':0,'matrix_transition_checks':0,'checks':0,'stops':0,'loads':0,'reader_checks':0,'domain_checks':0,'cyclic_resets':0}
TEMPLATES={};DATA={};DECOMPOSE={};MAX={'unitary_error':0.,'reconstruction_error':0.,'contraction_norm':0.,'holding_residual':0.,'register_residual':0.}
def a(s):return ALPHA+Q(1 if s%2==0 else -1,5*(s+1))
def cont(j,p):
    even=j if j%2==0 else j+1
    return Q(p,2**j)<a(even)
def val(N,x):return sum((Q((x>>j)&1,2**(j+1)) for j in range(N)),Q(0))
def cantor(N,x):return sum((Q(3*((x>>j)&1),4**(j+1)) for j in range(N)),Q(0))
def address(N,v):
    n=int(v*2**N);return int(f'{n:0{N}b}'[::-1],2)
def norm(A):return float(np.max(np.abs(A))) if A.size else 0.
def equal(A,B):return np.array_equal(A,B)
def data_model(j,p,mode):
    if mode=='default':return (ZERO,I,I)
    key=(j+p)%24
    if key in DATA:return DATA[key]
    P=[np.array([[1,0],[0,0]],complex),np.array([[1,1],[1,1]],complex)/2,np.array([[1,-1j],[1j,1]],complex)/2][key%3]
    id2=np.eye(2);g=[P,id2-P,id2-P,P]*2
    m=8;anchor=key%m;D=np.zeros_like(I);E=np.zeros_like(I);W=np.zeros_like(I)
    E[2*anchor:2*anchor+2,2*anchor:2*anchor+2]=id2
    for k,G in enumerate(g):
        block=(anchor+k)%m;D[2*block:2*block+2,2*block:2*block+2]=G
    for block in range(m):
        target=(block+1)%m;sign=-1 if (block+key)%3==0 else 1
        W[2*target:2*target+2,2*block:2*block+2]=sign*id2
    assert equal(D@D,D) and equal(D.conj().T,D) and equal(E@E,E) and equal(W.conj().T@W,I)
    DATA[key]=(D,E,W);return DATA[key]
def packed_relations(truth):
    vertices=2 if truth else 3;m=4*vertices
    dj=lambda k:'w'*k+'D'+'W'*k
    hj=lambda k:'E'+dj(k)+'E'
    rel=[('pack',[(1,'W'*k+'E'+'w'*k) for k in range(m)]+[(-1,'')])]
    rel += [(f'comm{k}',[(1,'E'+dj(k)),(-1,dj(k)+'E')]) for k in range(m)]
    for family in range(2):
        for x in range(vertices):
            i=family*2*vertices+2*x
            rel.append((f'pvm{family},{x}',[(1,hj(i)),(1,hj(i+1)),(-1,'E')]))
            rel.append((f'orth{family},{x}',[(1,hj(i)+hj(i+1))]))
    for x in range(vertices):
        for y in range(vertices):
            for aa in range(2):
                for bb in range(2):
                    win=(aa==bb) if x==y else (aa!=bb)
                    if not win:rel.append((f'lose{x},{y},{aa},{bb}',[(1,hj(2*x+aa)+hj(2*vertices+2*y+bb))]))
    return rel
RELS={truth:packed_relations(truth) for truth in (False,True)}
OPS={}
for truth,rels in RELS.items():
    ops=[]
    for label,terms in rels:
        b=(len(terms)-1).bit_length();ops.append(('CLEAR',None,label))
        for sign,word in terms:
            ops.append(('ONE',None,label))
            ops.extend(('MUL',letter,label) for letter in word)
            ops.append(('ADD',(sign,b),label))
        ops.append(('CHECK',None,label))
    OPS[truth]=ops

def template(j,p,truth,mode):
    key=(truth,mode,(j+p)%24 if mode=='witness' else 0)
    if key in TEMPLATES:return TEMPLATES[key]
    D,E,W=data_model(j,p,mode);letters={'D':D,'E':E,'W':W,'w':W.conj().T}
    M=I;T=ZERO;trace=[(M,T)];check_rows=[]
    for kind,arg,label in OPS[truth]:
        if kind=='CLEAR':T=ZERO
        elif kind=='ONE':M=I
        elif kind=='MUL':M=M@letters[arg]
        elif kind=='ADD':sign,b=arg;T=T+sign*2.**(-b)*M
        elif kind=='CHECK':check_rows.append((label,norm(T)))
        trace.append((M,T))
    if truth and mode=='witness':assert all(r==0 for _,r in check_rows),check_rows
    TEMPLATES[key]=(trace,(D,E,W),check_rows)
    return TEMPLATES[key]

@dataclass(slots=True)
class State:
    j:int;p:int;c:Q;reader:Q;ctrl:str;truth:bool;pc:int;s:int;data:tuple;M:np.ndarray;T:np.ndarray

def initial(N,x,r):return State(0,0,r,cantor(N,x),'ZERO',True,0,0,(ZERO,I,I),I,ZERO)
def step(h,N,x,flag):
    n=replace(h);ctrl=h.ctrl
    if ctrl=='ZERO':n.ctrl='STOP' if h.c==1 else 'PREPARE'
    elif ctrl=='STOP':n.s=h.j;n.ctrl='VERIFY'
    elif ctrl=='PREPARE':n.truth=cont(h.j,h.p);n.ctrl='LOAD'
    elif ctrl=='LOAD':
        trace,data,_=template(h.j,h.p,h.truth,'default' if flag or not h.truth else 'witness')
        n.data=data;n.M=I;n.T=ZERO;n.pc=0;n.ctrl='OPS'
    elif ctrl=='OPS':
        trace,_,_=template(h.j,h.p,h.truth,'default' if flag or not h.truth else 'witness')
        n.M,n.T=trace[h.pc+1];n.pc=h.pc+1
        if n.pc==len(OPS[h.truth]):n.ctrl='READ'
    elif ctrl=='READ':
        bit=(x>>h.j)&1 if h.j<N else 0
        n.p=2*h.p+bit;n.j=h.j+1;n.reader=4*h.reader-3*bit;n.ctrl='DEC'
    elif ctrl=='DEC':n.c=2*h.c;n.ctrl='ZERO'
    elif ctrl=='VERIFY':
        if a(h.s)<=Q(h.p+1,2**h.j):n.ctrl='REJECT'
        else:n.s=h.s+1
    elif ctrl=='REJECT':pass
    else:raise AssertionError(ctrl)
    return n

def inspect(h,flag,r,strict=True):
    violations=[];z=1 if h.c==1 else 0;s=Q(0) if z else 2*h.c
    if not (0<=s<=1 and h.c==z+Q(1,2)*(1-z)*s):violations.append(('counter-domain',str(h.c)))
    if h.ctrl=='ZERO' and h.c!=2**h.j*r:violations.append(('stop-depth-identity',str(h.c)))
    bit=1 if h.reader>=Q(3,4) else 0;tail=4*h.reader-3*bit
    if not (0<=tail<=1):violations.append(('reader-domain',str(h.reader)))
    if h.ctrl=='REJECT' and not flag:violations.append(('REJECT',h.j))
    if h.ctrl=='OPS' and OPS[h.truth][h.pc][0]=='CHECK' and not flag and norm(h.T)!=0:violations.append(('CHECK',OPS[h.truth][h.pc][2],norm(h.T)))
    if strict:assert not violations,violations
    return violations

def check_transition(h,n,reset,N,x,r):
    if reset:
        assert n.ctrl=='ZERO' and n.j==0 and n.p==0 and n.c==r and n.reader==cantor(N,x)
        assert equal(n.M,I) and equal(n.T,ZERO)
        COUNT['cyclic_resets']+=1
        return
    # Independently evaluate the right-guarded data holding equation (16.6).
    if h.ctrl!='LOAD':
        for old,new in zip(h.data,n.data):assert equal(new,old)
    oldM,oldT=h.M,h.T;rhsM,rhsT=oldM,oldT
    if h.ctrl=='LOAD':rhsM,rhsT=I,ZERO
    elif h.ctrl=='OPS':
        kind,arg,_=OPS[h.truth][h.pc]
        if kind=='CLEAR':rhsT=ZERO
        elif kind=='ONE':rhsM=I
        elif kind=='MUL':
            D,E,W=h.data;rhsM=oldM@{'D':D,'E':E,'W':W,'w':W.conj().T}[arg]
        elif kind=='ADD':sign,b=arg;rhsT=oldT+sign*2.**(-b)*oldM
    assert equal(rhsM,n.M) and equal(rhsT,n.T)
    assert n.c==(2*h.c if h.ctrl=='DEC' else h.c)
    bit=1 if h.reader>=Q(3,4) else 0
    assert n.reader==(4*h.reader-3*bit if h.ctrl=='READ' else h.reader)
    COUNT['matrix_transition_checks']+=1

def run_upper(N,x,b,m):
    assert N>=m and (2**m*b).denominator==1
    assert ALPHA-Q(1,5*(m+1))>b  # analytic lower bound for every s>=m
    flag=not(val(N,x)<b);r=Q(1,2**m);period=2**N
    history=[initial(N,x,r)]
    for _ in range(period-1):history.append(step(history[-1],N,x,flag))
    # At every larger-fuel phase check the equations directly, including cyclic reset.
    for t,h in enumerate(history):
        inspect(h,flag,r)
        COUNT['reader_checks']+=1;COUNT['domain_checks']+=1
        if h.ctrl=='LOAD':COUNT['loads']+=1
        if h.ctrl=='STOP':COUNT['stops']+=1
        if h.ctrl=='OPS' and OPS[h.truth][h.pc][0]=='CHECK':COUNT['checks']+=1
        check_transition(h,history[t+1] if t+1<period else history[0],t+1==period,N,x,r)
    # Every fuel k uses the prefix history at t mod 2^k. Check each distinct phase.
    for k in range(N):
        q=2**k
        for t in range(q):
            inspect(history[t],flag,r)
            check_transition(history[t],history[(t+1)%q],t+1==q,N,x,r)
    COUNT['blocks']+=2**(N+1)-1
    COUNT['physical_time_points']+=(N+1)*period
    stop=next((t for t,h in enumerate(history) if h.ctrl=='STOP'),None)
    if stop is not None and not flag:assert Q(history[stop].p+1,2**m)<=b
    return {'N':N,'x':x,'v':str(val(N,x)),'b':str(b),'m':m,'flag':flag,'first_STOP':stop,'last_depth':history[-1].j,'last_control':history[-1].ctrl}

def windows():
    rows=[]
    for N in (2,4,6,8,10,12):
        size=2**N
        for b in (Q(0),Q(1,8),Q(1,4),Q(3,8),Q(1,2),Q(5,8),Q(7,8),Q(1)):
            mask=np.array([int(val(N,x)>=b) for x in range(size)],dtype=np.int64)
            cs=np.concatenate(([0],np.cumsum(np.concatenate((mask,mask[:N])))))
            counts=cs[N:N+size]-cs[:size];mean=Q(1)-b
            error=max(abs(Q(int(t))-N*mean) for t in counts)
            bound=4*math.ceil(math.log2(N+1))+4
            assert float(error)<=bound
            finite_mean=Q(int(mask.sum()),size)
            expected_mean=Q(1)-Q(math.ceil(b*size),size)
            assert finite_mean==expected_mean and abs(finite_mean-mean)<Q(1,size)+Q(1,10**30)
            rows.append({'N':N,'b':str(b),'max_error':str(error),'min_window':int(counts.min()),'max_window':int(counts.max()),'mean':str(mean),'finite_mean':str(finite_mean),'grid_error':str(abs(finite_mean-mean)),'bound':bound})
    return rows

def negative_cases():
    ans=[]
    for name,r in [('infinite',Q(0)),('STOP1',Q(1,2)),('STOP0',Q(1)),('nondyadic',Q(3,10))]:
        N=14;x=address(N,Q(7,8) if name!='nondyadic' else Q(0));h=initial(N,x,r)
        found=None
        for t in range(2**N):
            v=inspect(h,False,r,False)
            if v:found={'time':t,'violation':v,'depth':h.j};break
            h=step(h,N,x,False)
        assert found,(name,'attack escaped finite test')
        ans.append({'name':name,'R':str(r),**found})
    # Swapping a tuple one step before LOAD violates the holding equation (16.6) on a nonreset PREPARE transition.
    h=initial(6,0,Q(1,16));h=step(h,6,0,False);n=step(h,6,0,False)
    assert h.ctrl=='PREPARE' and n.ctrl=='LOAD'
    altered=replace(n,data=data_model(0,0,'witness'))
    residual=max(norm(a-b) for a,b in zip(h.data,altered.data));assert residual>0
    ans.append({'name':'LOAD off-by-one','holding_residual':residual})
    # A correct LOAD change is allowed by the holding equation (16.6), while erroneously removing its guard rejects it.
    post=step(n,6,0,False);assert n.ctrl=='LOAD'
    residual=max(norm(a-b) for a,b in zip(n.data,post.data));assert residual>0
    ans.append({'name':'removed LOAD guard','unguarded_residual':residual,'correct_guarded_residual':0})
    return ans

def unitary_extensions():
    worst=0.;checked=0
    for trace,data,_ in TEMPLATES.values():
        for M,T in trace:
            for S in (M,T):
                key=hashlib.sha256(S.tobytes()).digest()
                if key in DECOMPOSE:continue
                U,s,Vh=np.linalg.svd(S);assert s.max()<=1+1e-12
                s=np.clip(s,0,1);u=(U*(s+1j*np.sqrt(1-s*s)))@Vh;v=(U*(s-1j*np.sqrt(1-s*s)))@Vh
                err=max(norm(u.conj().T@u-I),norm(v.conj().T@v-I));rec=norm((u+v)/2-S)
                assert err<1e-12 and rec<1e-12
                MAX['unitary_error']=max(MAX['unitary_error'],err);MAX['reconstruction_error']=max(MAX['reconstruction_error'],rec);MAX['contraction_norm']=max(MAX['contraction_norm'],float(s.max()))
                DECOMPOSE[key]=True;checked+=1
    return checked

def main():
    start=time.monotonic();cases=[]
    for b,m in ((Q(1,4),2),(Q(3,8),3),(Q(1,2),4)):
        for N in (4,6,10,12):
            vs={Q(0),Q(1,8),Q(1,4),Q(3,8),Q(1,2),Q(5,8),Q(3,4),Q(7,8),Q(1)-Q(1,2**N),b-Q(1,2**N),b+Q(1,2**N)}
            for v in sorted(vs):cases.append(run_upper(N,address(N,v),b,m))
        for v in (Q(0),b-Q(1,2**14),Q(7,8)):cases.append(run_upper(14,address(14,v),b,m))
        print('UPPER PASS',str(b),m,flush=True)
    (OUT/'upper-checkpoint.json').write_text(json.dumps({'cases':cases,'counts':COUNT,'template_keys':[list(k) for k in TEMPLATES]},indent=2))
    wr=windows();neg=negative_cases();dc=unitary_extensions()
    mem=psutil.Process().memory_info();assert mem.peak_wset<1_500_000_000
    result={'sequence':'a_s=11/20+(-1)^s/(5(s+1))','alpha':str(ALPHA),'nonmonotone':a(0)>a(1)<a(2),'upper_cases':cases,'counts':COUNT,'gate_sizes':{str(k):{'generators':4*(2 if k else 3),'polynomials':len(RELS[k]),'microinstructions':len(OPS[k])} for k in RELS},'window_cases':wr,'negative_controls':neg,'unitary_extensions_checked':dc,'max_residuals':MAX,'dyadic_history_equalities':'exact bitwise equality; no nonzero residuals','two_unitary_extensions':'floating-point check, tolerance 1e-12; exact existence given by polar formula','memory_peak_bytes':mem.peak_wset,'seconds':time.monotonic()-start,'scope':'semantic scalar arithmetic and finite block histories; no universal-counter compilation, actual MIP* game, infinite trace or asymptotic lower bound executed','passed':True}
    (OUT/'toy-results.json').write_text(json.dumps(result,indent=2))
    print(json.dumps({k:v for k,v in result.items() if k not in ('upper_cases','window_cases')},indent=2),flush=True)
if __name__=='__main__':main()
