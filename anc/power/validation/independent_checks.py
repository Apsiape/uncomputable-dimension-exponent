import os
for name in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):
    os.environ[name]='1'
os.environ['PYTHONDONTWRITEBYTECODE']='1'
import ctypes, hashlib, json, math
from fractions import Fraction as F
from pathlib import Path
import numpy as np

ROOT=Path(__file__).resolve().parent
TABLE={0:('inc',0,1),1:('out',1,2),2:('test',0,6,3),3:('out',0,4),
       4:('test',0,5,2),5:('out',1,0),6:('inc',1,7),7:('test',1,0,0)}
LABELS=sorted(TABLE)
I=np.eye(4,dtype=complex)
def trajectory(length,control=0,counters=(0,0)):
    n=list(counters); result=[]; pulses=ones=0
    for h in range(length):
        ins=TABLE[control]; f=int(ins[0]=='out'); g=f*int(ins[1]==1)
        result.append(dict(control=control,n=n.copy(),j=pulses,k=ones,f=f,g=g))
        if ins[0]=='inc': n[ins[1]]+=1; control=ins[2]
        elif ins[0]=='test':
            if n[ins[1]]: n[ins[1]]-=1; control=ins[3]
            else: control=ins[2]
        else: control=ins[2]
        assert min(n)>=0
        pulses+=f; ones+=g
    return result

def independent_scalar_histories():
    histories=trajectory(2400)
    max_equation=F(0); blocks=0; checked=0; truncated=0
    inputs=[F(0),F(1),F(1,2),F(1,2)-F(1,2**54),F(1,2)+F(1,2**53),F(1,4),F(1,2**100),F(3,256)]
    def record(value):
        nonlocal max_equation,checked
        max_equation=max(max_equation,abs(value)); checked+=1
    for bits in (2,4,6):
        size=2**bits
        def tail(word): return (word>>1)|((word&1)<<(bits-1))
        def period(fuel):
            k=0
            while k<bits and (fuel>>k)&1: k+=1
            return 2**k
        for fuel in range(size):
            length=period(fuel)
            for time in range(size):
                age=time%length; nxt=((time+1)%size)%length
                reset=int(age==0); zr=int(nxt==0)
                recursion=1-(fuel&1)+(fuel&1)*(1-(time&1))*int(tail(time)%period(tail(fuel))==0)
                record(F(reset-recursion))
                current=histories[age]; future=histories[nxt]
                a=F(1,age+1); ap=F(1,nxt+1)
                record(ap*(1+a)-a-zr)
                increment=[0,0]; transitions={s:0 for s in LABELS}
                ins=TABLE[current['control']]
                if ins[0]=='inc': increment[ins[1]]=1; transitions[ins[2]]=1
                elif ins[0]=='test':
                    nz=int(current['n'][ins[1]]>0)
                    increment[ins[1]]=-nz; transitions[ins[3] if nz else ins[2]]=1
                else: transitions[ins[2]]=1
                for index in range(2):
                    y=current['n'][index]*a; yp=future['n'][index]*ap
                    e=int(current['n'][index]==0); w=max(current['n'][index]-1,0)*a
                    assert 0<=y<=1 and 0<=w<=1
                    record(y*e); record((y-a-w)*(1-e))
                    record(yp*(1+a)-(1-zr)*(y+a*increment[index]))
                for state in LABELS:
                    record(F(int(future['control']==state)-zr*int(state==0)-(1-zr)*transitions[state]))
                for t in inputs:
                    if not t: stop=100000; penalty=F(0)
                    else:
                        ell=0
                        while 2**(ell+1)*t<=1: ell+=1
                        stop=next(h for h,item in enumerate(histories) if item['k']==ell)
                        penalty=F(1,2**(histories[stop]['j']+1))
                    def values(h):
                        z=histories[min(h,stop)]
                        return t*2**z['k'],penalty*2**z['j'],int(h<=stop),int(h==stop)
                    c,d,r,p=values(age); cp,dp,rp,pp=values(nxt)
                    assert 0<=c<=1 and 0<=d<=F(1,2)
                    record(cp-zr*t-(1-zr)*c*(1+current['g']*(r-p)))
                    record(dp-zr*penalty-(1-zr)*d*(1+current['f']*(r-p)))
                    record(F(rp-zr-(1-zr)*(r-p)))
                    record((d-F(1,2))*p)
                    if stop>=length: truncated+=1
                blocks+=1
    assert max_equation==0
    return dict(program='independent 101 pulse program',clock_bits=[2,4,6],blocks=blocks,
                equations=checked,max_exact_fraction_residual=str(max_equation),reset_truncated_cases=truncated)

def hermitian_unitary(rng,theta):
    x=rng.normal(size=(4,4))+1j*rng.normal(size=(4,4)); x=(x+x.conj().T)/2
    x/=max(1,np.linalg.norm(x,2)); eigen,vectors=np.linalg.eigh(x)
    return (vectors*np.exp(1j*theta*eigen))@vectors.conj().T

def weighted_histories(depth,theta):
    rng=np.random.default_rng(16384+depth)
    truth=trajectory(depth+1)
    sectors=[truth,trajectory(depth+1,2,(2,0)),trajectory(depth+1,6,(0,1)),trajectory(depth+1,4,(0,0))]
    offsets=[1,4,3,2]
    xi=np.diag(np.sqrt([.51,.27,.15,.07])).astype(complex)
    phi=np.diag([1,0,0,0])@xi
    norm=lambda x:float(np.linalg.norm(x,'fro'))
    weight=lambda x:norm(x@xi)
    configurations=[]; delta=0.; maximum_cross=0.; maximum_current=0.
    for h in range(depth+1):
        u=hermitian_unitary(rng,theta); ue=hermitian_unitary(rng,theta)@u; up=hermitian_unitary(rng,theta)@u
        def op(values,basis=u): return (basis*np.array(values))@basis.conj().T
        age=op([1/(h+c) for c in offsets])
        y=[op([sectors[j][h]['n'][i]/(h+offsets[j]) for j in range(4)]) for i in range(2)]
        w=[op([max(sectors[j][h]['n'][i]-1,0)/(h+offsets[j]) for j in range(4)]) for i in range(2)]
        e=[op([int(sectors[j][h]['n'][i]==0) for j in range(4)],ue) for i in range(2)]
        q={s:op([int(sectors[j][h]['control']==s) for j in range(4)]) for s in LABELS}
        stop=op([0,int(h%3==1),int(h%4==2),int(h%5==3)],up)
        generators=[age,*y,*w,*e,*q.values(),stop]
        for x in generators:
            assert np.linalg.eigvalsh(x).min()>-2e-12 and np.linalg.eigvalsh(x).max()<1+2e-12
            delta=max(delta,norm(x@xi-xi@x))
        for i,x in enumerate(generators):
            for z in generators[i+1:]:
                comm=weight(x@z-z@x); maximum_current=max(maximum_current,comm); delta=max(delta,comm)
        for i in range(2): delta=max(delta,weight(y[i]@e[i]),weight((y[i]-age-w[i])@(I-e[i])))
        configurations.append(dict(a=age,y=y,w=w,e=e,q=q,p=stop))
    initial=configurations[0]
    delta=max(delta,norm((initial['a']-I)@phi),*(norm(y@phi) for y in initial['y']),
              norm((I-initial['q'][0])@phi))
    for h in range(depth):
        x,z=configurations[h:h+2]
        changes=[np.zeros((4,4),complex) for _ in range(2)]
        nextq={s:np.zeros((4,4),complex) for s in LABELS}
        for s,ins in TABLE.items():
            if ins[0]=='inc': changes[ins[1]]+=x['q'][s]; nextq[ins[2]]+=x['q'][s]
            elif ins[0]=='test':
                changes[ins[1]]-=x['q'][s]@(I-x['e'][ins[1]])
                nextq[ins[2]]+=x['q'][s]@x['e'][ins[1]]
                nextq[ins[3]]+=x['q'][s]@(I-x['e'][ins[1]])
            else: nextq[ins[2]]+=x['q'][s]
        delta=max(delta,weight(z['a']@(I+x['a'])-x['a']))
        for i in range(2): delta=max(delta,weight(z['y'][i]@(I+x['a'])-x['y'][i]-x['a']@changes[i]))
        for s in LABELS: delta=max(delta,weight(z['q'][s]-nextq[s]))
        maximum_cross=max(maximum_cross,weight(x['y'][0]@z['e'][0]-z['e'][0]@x['y'][0]))
    retained=I.copy(); total=np.zeros_like(I); bad_square=0.; stops=0.; age_errors=[]; counter_errors=[]
    ratios=[]
    for h,x in enumerate(configurations):
        v=retained@phi; a=1/(h+1)
        age_errors.append(norm((x['a']-a*I)@v))
        counter_errors.append(max(norm((x['y'][i]-truth[h]['n'][i]*a*I)@v) for i in range(2)))
        if h==depth: break
        q=x['q'][truth[h]['control']]; bad=(I-q)@retained
        total+=bad.conj().T@bad; bad_square+=norm(bad@phi)**2
        selected=q@retained; ins=TABLE[truth[h]['control']]
        if ins[0]=='test':
            e=x['e'][ins[1]] if truth[h]['n'][ins[1]]==0 else I-x['e'][ins[1]]
            bad=(I-e)@selected; total+=bad.conj().T@bad
            bad_square+=norm(bad@phi)**2; selected=e@selected
        stopped=x['p']@selected; total+=stopped.conj().T@stopped; stops+=norm(stopped@phi)**2
        retained=(I-x['p'])@selected
    total+=retained.conj().T@retained
    completeness=norm(total-I)
    assert completeness<2e-11
    normalized_age=max(error/((h+1)*delta) for h,error in enumerate(age_errors))
    normalized_counter=max(error/((h+1)**2*delta) for h,error in enumerate(counter_errors))
    assert normalized_age<50 and normalized_counter<50
    assert maximum_cross>theta*1e-5 and maximum_current>theta*1e-5
    return dict(depth=depth,theta=theta,measured_delta=delta,terminal_age_error=age_errors[-1],
                terminal_counter_error=counter_errors[-1],max_age_error=max(age_errors),max_counter_error=max(counter_errors),
                max_age_over_h_delta=normalized_age,max_counter_over_h2_delta=normalized_counter,
                bad_amplitude=math.sqrt(bad_square),stopped_amplitude=math.sqrt(stops),
                completeness_error=completeness,current_noncommutator=maximum_current,cross_time_noncommutator=maximum_cross)

def arbitrary_column_test():
    rng=np.random.default_rng(9001); total=np.zeros_like(I); keep=I.copy()
    for h in range(80):
        for rank in (1,2,1):
            u=hermitian_unitary(rng,1.7); p=(u*np.array([1]*rank+[0]*(4-rank)))@u.conj().T
            discard=p@keep; total+=discard.conj().T@discard; keep=(I-p)@keep
    total+=keep.conj().T@keep
    error=float(np.linalg.norm(total-I,'fro')); assert error<1e-12
    return error

def peak_memory():
    if os.name!='nt': return None
    from ctypes import wintypes
    class Counters(ctypes.Structure):
        _fields_=[('cb',wintypes.DWORD),('PageFaultCount',wintypes.DWORD)]+[(name,ctypes.c_size_t) for name in
            ('PeakWorkingSetSize','WorkingSetSize','QuotaPeakPagedPoolUsage','QuotaPagedPoolUsage','QuotaPeakNonPagedPoolUsage','QuotaNonPagedPoolUsage','PagefileUsage','PeakPagefileUsage')]
    counter=Counters(); counter.cb=ctypes.sizeof(counter)
    handle=ctypes.windll.kernel32.GetCurrentProcess
    handle.restype=wintypes.HANDLE
    measure=ctypes.windll.psapi.GetProcessMemoryInfo
    measure.argtypes=[wintypes.HANDLE,ctypes.POINTER(Counters),wintypes.DWORD]
    measure.restype=wintypes.BOOL
    assert measure(handle(),ctypes.byref(counter),counter.cb)
    return counter.PeakWorkingSetSize

def main():
    scalar=independent_scalar_histories()
    histories=[]; slopes=[]
    for depth in (8,16,32,64,128,256):
        rows=[weighted_histories(depth,theta) for theta in (1e-2,1e-3,1e-4,1e-5,1e-6)]
        for quantity in ('max_counter_error','bad_amplitude'):
            slope=float(np.polyfit(np.log([r['measured_delta'] for r in rows]),np.log([r[quantity] for r in rows]),1)[0])
            assert .97<slope<1.03,(depth,quantity,slope)
            slopes.append(dict(depth=depth,quantity=quantity,slope=slope))
        histories+=rows
    source=ROOT.parent/'claims'/'check_scaled_machine.py'
    copied=ROOT/'check_scaled_machine.py'
    assert source.read_bytes()==copied.read_bytes()
    result=dict(status='PASS',scalar=scalar,histories=histories,slopes=slopes,
                arbitrary_column_completeness=arbitrary_column_test(),peak_working_set_bytes=peak_memory(),
                supplied_script_sha256=hashlib.sha256(copied.read_bytes()).hexdigest(),
                thread_limits={name:os.environ[name] for name in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS')},
                scope='Finite-window weighted counter/zero-test models, not complete clock/compiler strategies; no numerical experiment proves uniform stability.')
    assert result['peak_working_set_bytes'] is None or result['peak_working_set_bytes']<1500000000
    (ROOT/'independent-results.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print('PASS independent tests',flush=True)
    print('Scalar blocks/equations:',scalar['blocks'],scalar['equations'],'exact maximum:',scalar['max_exact_fraction_residual'])
    print('Slope range:',min(x['slope'] for x in slopes),max(x['slope'] for x in slopes))
    print('Max normalized age/counter:',max(r['max_age_over_h_delta'] for r in histories),max(r['max_counter_over_h2_delta'] for r in histories))
    print('Max history completeness:',max(r['completeness_error'] for r in histories))
    print('Peak working set:',result['peak_working_set_bytes'])

if __name__=='__main__': main()
