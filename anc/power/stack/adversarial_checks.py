"""Independent small stress tests. The manuscript proves the mathematical estimates.
All arrays have dimension at most 8, or are diagonal history arrays below 1 MiB.
"""
import os
for key in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):
    os.environ[key]='1'
os.environ['PYTHONDONTWRITEBYTECODE']='1'
import json, math
from decimal import Decimal as D, getcontext, ROUND_FLOOR, ROUND_CEILING
from pathlib import Path
import numpy as np
getcontext().prec=110
OUT=Path(__file__).resolve().parent

def norm(a):
    return float(np.linalg.norm(a,'fro'))

def comm(a,b):
    return a@b-b@a

def rot(t):
    return np.array([[math.cos(t),-math.sin(t)],[math.sin(t),math.cos(t)]])

def projection(t):
    v=np.array([math.sin(t),math.cos(t)])
    return np.outer(v,v)

def weighted_carry_and_stop():
    ident=np.eye(2)
    beta=math.sqrt(2)/2
    records=[]
    # Good vector at t=0, independently rotated carry/stop/state for t>0.
    for h in (0,1,5,12):
        a=h*beta-math.floor(h*beta)
        b=math.floor((h+1)*beta)-math.floor(h*beta)
        cwrong=a+beta-(1-b)
        anext=a+beta-b
        gap=min(abs((h+1)*beta-round((h+1)*beta)),1.0)
        for theta in (1e-2,1e-3,1e-4,1e-5,1e-6,1e-7):
            q=projection(theta)
            g=b*ident+(1-2*b)*q
            p=projection(-1.7*theta)
            e=ident-q
            u=rot(0.31*theta)
            xi=u@np.diag([math.sqrt(1-theta*theta),theta])@u.T
            ah=a*ident
            ap=np.diag([anext,min(1,max(0,cwrong))])
            root=beta*ident
            source=np.diag([.8,.3])
            # Separate stop test: D=1/2 on good sector, different on bad sector.
            counter=np.diag([.5,.2])
            phase=ap-ah-root+g
            residuals=[norm(phase@xi),norm((counter-.5*ident)@p@xi)]
            generators=[ah,ap,root,g,p,counter,source]
            residuals += [norm(comm(x,xi)) for x in generators]
            residuals += [norm(comm(x,y)@xi) for x in (ah,root,g,p,counter,source) for y in (ah,root,g,p,counter,source)]
            delta=max(residuals)
            v=q@xi
            bad=norm(v)
            # Local spectral-distance estimate, with explicit error ledger.
            coercive=norm((ap-cwrong*ident)@v)
            phase_charge=norm(phase@q@xi)
            assert gap*bad <= coercive+2e-14
            assert abs(coercive-phase_charge)<2e-14
            assert bad <= 10*delta/gap
            assert delta <= 10*theta
            assert norm(comm(g,p)) > theta
            # Exact three-outcome completeness even when E and P do not commute.
            badcol=q
            stop=p@e
            cont=(ident-p)@e
            completeness=norm(badcol.T@badcol+stop.T@stop+cont.T@cont-ident)
            assert completeness<1e-13
            records.append({'h':h,'theta':theta,'delta':delta,'bad_norm':bad,
                            'bad_over_delta':bad/delta,'bad_over_sqrt_delta':bad/math.sqrt(delta),
                            'gap':gap,'coercivity_ratio':gap*bad/coercive,
                            'weighted_stop_residual':residuals[1],
                            'carry_stop_commutator':norm(comm(g,p)),
                            'state_carry_commutator':norm(comm(g,xi)),
                            'completeness_error':completeness})
    fits=[]
    for h in (0,1,5,12):
        rows=[r for r in records if r['h']==h]
        fits.append({'h':h,'log_bad_vs_log_delta_slope':float(np.polyfit(np.log([r['delta'] for r in rows]),np.log([r['bad_norm'] for r in rows]),1)[0])})
    return {'records':records,'fits':fits,'scope':'Local weighted carry/stop tests, not a full approximate clock model.'}

def root_register():
    beta=math.sqrt(2)/2
    ell,u=.7,.75
    bound=1/(2*(ell+beta)) # |2x^2-1|=2|x-beta|(x+beta).
    rng=np.random.default_rng(45001)
    rows=[]
    for theta in (1e-2,1e-4,1e-6):
        ev=np.array([beta-theta*.4,beta+theta*.3])
        b=rot(.73)@np.diag(ev)@rot(.73).T
        z=rng.standard_normal((2,2))
        rho=z@z.T;rho/=np.trace(rho)
        w,v=np.linalg.eigh(rho)
        xi=(v*np.sqrt(w))@v.T
        residual=2*b@b-np.eye(2)
        lhs=norm((b-beta*np.eye(2))@xi)
        rhs=bound*norm(residual@xi)
        assert lhs<=rhs+2e-14
        rows.append({'theta':theta,'lhs':lhs,'bound':rhs,'state_parameter_commutator':norm(comm(b,rho))})
    return rows

def decimal_root(degree):
    # x^degree+x-1, strictly increasing on [0,1], irreducible for degree 3,4.
    lo,hi=D(0),D(1)
    for _ in range(380):
        mid=(lo+hi)/2
        if mid**degree+mid-1<0: lo=mid
        else: hi=mid
    return (lo+hi)/2

def floor(x): return int(x.to_integral_value(rounding=ROUND_FLOOR))
def ceil(x): return int(x.to_integral_value(rounding=ROUND_CEILING))

def boundary_histories():
    rows=[]
    for degree in (3,4):
        beta=decimal_root(degree)
        for nc in (2,3,5):
            size=1<<nc
            times=np.arange(size)
            periods=np.array([1<<next((i for i in range(nc) if not (f>>i&1)),nc) for f in range(size)])
            age=times[None,:]%periods[:,None]
            z=(age==0).astype(float);zn=np.roll(z,-1,axis=1)
            phases=np.array([float(D(r)*beta-floor(D(r)*beta)) for r in range(size)])[age]
            carries=np.array([floor(D(r+1)*beta)-floor(D(r)*beta) for r in range(size)])[age]
            worst=0.0; checked=0; float_log_misclassified=0
            inputs=[D(0),D(1)]
            for k in (1,2,5,20,100):
                exact=math.ldexp(1.,-k)
                inputs.extend(D.from_float(x) for x in (math.nextafter(exact,0.),exact,math.nextafter(exact,1.)))
            for t in inputs:
                if t==0:
                    j=10**9;s=D(0);k=None
                else:
                    # Exact k by dyadic comparisons: never floor a rounded float log.
                    k=0
                    while t < D(2)**(-k): k+=1
                    if t != D(2)**(-k): k-=1
                    assert D(2)**(-k-1)<t<=D(2)**(-k)
                    if math.floor(math.log2(1/float(t)))!=k:
                        float_log_misclassified+=1
                    j=ceil(D(k+1)/beta)-1
                    assert floor(D(j)*beta)==k
                    s=D(2)**(-j-1)
                    assert s<=t**(D(1)/beta)
                minage=np.minimum(age,j)
                c=np.array([float(t*D(2)**floor(D(min(r,j))*beta)) for r in range(size)])[age]
                d=np.array([float(s*D(2)**min(r,j)) for r in range(size)])[age]
                h=(age<=j).astype(float);p=(age==j).astype(float)
                errors=[z*(c-float(t)),z*(d-float(s)),z*(h-1),z*phases,
                        np.roll(c,-1,axis=1)-zn*float(t)-(1-zn)*c*(1+carries*(h-p)),
                        np.roll(d,-1,axis=1)-zn*float(s)-(1-zn)*d*(1+h-p),
                        np.roll(h,-1,axis=1)-zn-(1-zn)*(h-p),
                        np.roll(phases,-1,axis=1)-(1-zn)*(phases+float(beta)-carries),
                        (d-.5)*p]
                worst=max(worst,max(float(np.max(np.abs(x))) for x in errors))
                assert min(c.min(),d.min(),phases.min())>=0
                assert max(c.max(),d.max(),phases.max())<=1
                checked+=size*size
            assert worst<3e-14
            rows.append({'polynomial':f'x^{degree}+x-1','beta':str(beta),'clock_bits':nc,
                         'eigenvalues_tested':len(inputs),'scalar_blocks_tested':checked,
                         'max_new_residual':worst,'float_log_boundary_misclassifications':float_log_misclassified})
    return rows

def prefix_amplitudes():
    # Independently perturb three Boolean bits, their flips, and a nonflat state.
    rng=np.random.default_rng(8192);dim=8;ident=np.eye(dim)
    basep=[np.diag([(x>>i)&1 for x in range(dim)]).astype(float) for i in range(3)]
    basex=[]
    for i in range(3):
        x=np.zeros((dim,dim))
        for j in range(dim):x[j^(1<<i),j]=1
        basex.append(x)
    skew=[]
    for _ in range(6):
        z=rng.normal(size=(dim,dim));z=z-z.T;z/=np.linalg.norm(z,2);skew.append(z)
    statepert=np.diag(np.linspace(-.5,.5,dim));rows=[]
    for theta in (1e-2,1e-3,1e-4,1e-5,1e-6):
        us=[]
        for z in skew:
            # Cayley transform is exactly orthogonal (up to roundoff).
            us.append(np.linalg.solve(ident-theta*z/2,ident+theta*z/2))
        ps=[us[i]@basep[i]@us[i].T for i in range(3)]
        xs=[us[i+3]@basex[i]@us[i+3].T for i in range(3)]
        xi=ident/math.sqrt(dim)+theta*statepert;xi/=norm(xi)
        delta=max([norm(comm(y,xi)) for y in ps+xs]+[norm((xs[i]@ps[i]@xs[i]-(ident-ps[i]))@xi) for i in range(3)]+[norm(comm(xs[i],ps[j])@xi) for i in range(3) for j in range(i+1,3)]+[norm(comm(ps[i],ps[j])@xi) for i in range(3) for j in range(i+1,3)])
        maximum=0.
        for i in range(3):
            for suffixbits in range(1<<(2-i)):
                suffix=ident.copy()
                for j in range(i+1,3):
                    bit=(suffixbits>>(j-i-1))&1
                    suffix=suffix@(ps[j] if bit else ident-ps[j])
                a=norm(ps[i]@suffix@xi);b=norm((ident-ps[i])@suffix@xi)
                maximum=max(maximum,abs(a-b))
        assert maximum<20*delta
        rows.append({'theta':theta,'delta':delta,'max_amplitude_difference':maximum,'difference_over_delta':maximum/delta,'noncommuting_bit_norm':norm(comm(ps[0],ps[1]))})
    return rows

def multistep_carries():
    """All local phase residuals are measured, including insertions implicitly.
    No common time unitary or complete clock is asserted for these local tests.
    """
    rng=np.random.default_rng(20261028);dim=4;depth=17
    ident=np.eye(dim);beta=(math.sqrt(5)-1)/2
    offsets=np.array([0.,.19,.46,.87])
    skews=[]
    for _ in range(3*depth+1):
        z=rng.normal(size=(dim,dim));z=z-z.T;z/=np.linalg.norm(z,2);skews.append(z)
    rows=[]
    for theta in (1e-2,1e-3,1e-4,1e-5,1e-6,1e-7):
        def perturb(diag,ix):
            z=skews[ix]
            u=np.linalg.solve(ident-theta*z/2,ident+theta*z/2)
            return u@np.diag(diag)@u.T
        xi=np.diag([math.sqrt(1-3*theta*theta),theta,theta,theta])
        aa=[];gg=[];pp=[]
        for h in range(depth+1):
            phase=(offsets+h*beta)%1
            aa.append(perturb(phase,h))
            if h<depth:
                carry=np.floor(offsets+(h+1)*beta)-np.floor(offsets+h*beta)
                gg.append(perturb(carry,depth+1+h))
                pp.append(perturb([int(h==9),int(h==4),int(h==6),int(h==8)],2*depth+1+h))
        phase_res=[aa[h+1]-aa[h]-beta*ident+gg[h] for h in range(depth)]
        delta=max([norm(aa[0]@xi)]+[norm(r@xi) for r in phase_res]+[norm(comm(y,xi)) for y in aa+gg+pp]+[norm(comm(y,z)@xi) for h in range(depth) for y in (aa[h],gg[h],pp[h]) for z in (aa[h],gg[h],pp[h])])
        k=ident.copy();complete=np.zeros((dim,dim));bads=[];ratios=[]
        for h in range(depth):
            b=math.floor((h+1)*beta)-math.floor(h*beta)
            e=gg[h] if b else ident-gg[h]
            bad=(ident-e)@k;stop=pp[h]@e@k
            kn=(ident-pp[h])@e@k
            complete+=bad.T@bad+stop.T@stop
            v=bad@xi;c=(h*beta)%1+beta-(1-b)
            gap=abs((h+1)*beta-round((h+1)*beta))
            assert gap*norm(v)<=norm((aa[h+1]-c*ident)@v)+2e-14
            bads.append(norm(v));ratios.append(norm((aa[h]-(h*beta)%1*ident)@k@xi)/delta)
            k=kn
        complete+=k.T@k
        err=norm(complete-ident)
        assert err<1e-12
        badtotal=float(np.linalg.norm(bads))
        assert badtotal<100*delta
        rows.append({'theta':theta,'delta':delta,'bad_total':badtotal,'bad_total_over_delta':badtotal/delta,
                     'max_phase_error_over_delta':max(ratios),'completeness_error':err,
                     'max_carry_stop_commutator':max(norm(comm(g,p)) for g,p in zip(gg,pp))})
    slope=float(np.polyfit(np.log([r['delta'] for r in rows]),np.log([r['bad_total'] for r in rows]),1)[0])
    return {'depth':depth,'dimension':dim,'records':rows,'log_bad_vs_log_delta_slope':slope}

def peak_memory():
    # Windows process peak working set, using only the standard library.
    import ctypes
    from ctypes import wintypes
    class Counters(ctypes.Structure):
        _fields_=[('cb',wintypes.DWORD),('PageFaultCount',wintypes.DWORD)]+[(s,ctypes.c_size_t) for s in ('PeakWorkingSetSize','WorkingSetSize','QuotaPeakPagedPoolUsage','QuotaPagedPoolUsage','QuotaPeakNonPagedPoolUsage','QuotaNonPagedPoolUsage','PagefileUsage','PeakPagefileUsage')]
    counters=Counters();counters.cb=ctypes.sizeof(counters)
    kernel=ctypes.WinDLL('kernel32',use_last_error=True)
    kernel.GetCurrentProcess.restype=wintypes.HANDLE
    psapi=ctypes.WinDLL('psapi',use_last_error=True)
    psapi.GetProcessMemoryInfo.argtypes=[wintypes.HANDLE,ctypes.POINTER(Counters),wintypes.DWORD]
    if not psapi.GetProcessMemoryInfo(kernel.GetCurrentProcess(),ctypes.byref(counters),counters.cb):
        raise ctypes.WinError(ctypes.get_last_error())
    return counters.PeakWorkingSetSize

if __name__=='__main__':
    result={'weighted_carry_stop':weighted_carry_and_stop(),'root_register':root_register(),
            'boundary_histories':boundary_histories(),'prefix_amplitudes':prefix_amplitudes(),
            'multistep_carries':multistep_carries(),
            'thread_limits':{k:os.environ[k] for k in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS')}}
    result['peak_working_set_bytes']=peak_memory()
    assert result['peak_working_set_bytes']<1500000000
    result['status']='PASS (finite/local stress tests only)'
    (OUT/'adversarial-results.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status'])
    print('Bad carry slopes:',result['weighted_carry_stop']['fits'])
    print('Boundary history max residual:',max(x['max_new_residual'] for x in result['boundary_histories']))
    print('Float-log misclassifications (diagnostic only):',sum(x['float_log_boundary_misclassifications'] for x in result['boundary_histories']))
    print('Prefix amplitude max difference/delta:',max(x['difference_over_delta'] for x in result['prefix_amplitudes']))
    print('Multistep slope:',result['multistep_carries']['log_bad_vs_log_delta_slope'])
    print('Peak bytes:',result.get('peak_working_set_bytes','not available'))
