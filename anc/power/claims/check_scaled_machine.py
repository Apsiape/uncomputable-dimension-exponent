"""Single-threaded finite checks for scaled counters. No claim of uniform proof by sampling."""
import os
for key in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):
    os.environ[key]='1'
os.environ['PYTHONDONTWRITEBYTECODE']='1'
import json
import math
from fractions import Fraction
from pathlib import Path
import numpy as np

ROOT=Path(__file__).resolve().parent
def err(x): return float(np.max(np.abs(x)))
def floor_log_reciprocal(t):
    numerator,denominator=float(t).as_integer_ratio()
    k=denominator.bit_length()-numerator.bit_length()
    while (numerator<<k)>denominator: k-=1
    while (numerator<<(k+1))<=denominator: k+=1
    return k

# Instruction format: INC register,next; DECJZ register,zero,nonzero;
# OUT bit,next. Each instruction takes one physical tick.
PROGRAM={0:('INC',0,1),1:('INC',0,2),2:('DECJZ',0,6,3),
         3:('INC',1,4),4:('OUT',1,2),6:('DECJZ',1,0,7),7:('OUT',0,6)}
LABELS=sorted(PROGRAM)

def run_machine(length):
    control=0
    counters=np.zeros(2,dtype=np.int64)
    records=[]
    pulses=ones=0
    for h in range(length):
        ins=PROGRAM[control]
        f=int(ins[0]=='OUT')
        g=f*int(ins[1]==1)
        records.append((control,counters.copy(),pulses,ones,f,g))
        if ins[0]=='INC':
            counters[ins[1]]+=1; control=ins[2]
        elif ins[0]=='DECJZ':
            if counters[ins[1]]==0: control=ins[2]
            else: counters[ins[1]]-=1; control=ins[3]
        else: control=ins[2]
        pulses+=f; ones+=g
        assert np.all(counters>=0) and np.all(counters<=h+1)
    return records

def finite_model(nc):
    size=1<<nc
    words=np.arange(size,dtype=np.int64)
    tail=(words>>1)|((words&1)<<(nc-1))
    periods=[]
    for fuel in words:
        k=0
        while k<nc and ((int(fuel)>>k)&1): k+=1
        periods.append(1<<k)
    age=words[None,:]%np.array(periods)[:,None]
    reset=(age==0).astype(float)
    reset_next=np.roll(reset,-1,axis=1)
    assert err(reset-((1-(words&1))[:,None]+(words&1)[:,None]*(1-(words&1))[None,:]*reset[tail[:,None],tail[None,:]]))==0
    history=run_machine(5000)
    q=np.array([r[0] for r in history])
    count=np.stack([r[1] for r in history])
    pulses=np.array([r[2] for r in history])
    ones=np.array([r[3] for r in history])
    f=np.array([r[4] for r in history])[age]
    g=np.array([r[5] for r in history])[age]
    a=1/(age+1)
    y=[count[:,i][age]*a for i in range(2)]
    zero=[(count[:,i][age]==0).astype(float) for i in range(2)]
    witness=[np.maximum(count[:,i][age]-1,0)*a for i in range(2)]
    controls={label:(q[age]==label).astype(float) for label in LABELS}
    delta=[np.zeros_like(a),np.zeros_like(a)]
    transition={label:np.zeros_like(a) for label in LABELS}
    for label,ins in PROGRAM.items():
        current=controls[label]
        if ins[0]=='INC':
            delta[ins[1]]+=current
            transition[ins[2]]+=current
        elif ins[0]=='DECJZ':
            delta[ins[1]]-=current*(1-zero[ins[1]])
            transition[ins[2]]+=current*zero[ins[1]]
            transition[ins[3]]+=current*(1-zero[ins[1]])
        else: transition[ins[2]]+=current
    residuals={'age_init':err(reset*(a-1)),
               'age_transition':err(np.roll(a,-1,axis=1)*(1+a)-a-reset_next)}
    for i in range(2):
        residuals[f'counter_{i}_init']=err(reset*y[i])
        residuals[f'counter_{i}_transition']=err(np.roll(y[i],-1,axis=1)*(1+a)-(1-reset_next)*(y[i]+a*delta[i]))
        residuals[f'counter_{i}_zero']=err(y[i]*zero[i])
        residuals[f'counter_{i}_nonzero']=err((y[i]-a-witness[i])*(1-zero[i]))
        assert np.min(witness[i])>=0 and np.max(witness[i])<=1
    for label in LABELS:
        residuals[f'control_{label}_init']=err(reset*(controls[label]-int(label==0)))
        residuals[f'control_{label}_transition']=err(np.roll(controls[label],-1,axis=1)-reset_next*int(label==0)-(1-reset_next)*transition[label])
    residuals['control_sum']=err(sum(controls.values())-1)
    residuals['pulse']=err(f-controls[4]-controls[7])
    residuals['one']=err(g-controls[4])

    inputs=[0.,1.,np.nextafter(.5,0.),.5,np.nextafter(.5,1.),.25,.01,2.**-40,2.**-100]
    for ix,t in enumerate(inputs):
        if t==0:
            stop=len(history)+1; s=0.
        else:
            k=floor_log_reciprocal(t)
            stop=int(np.flatnonzero(ones==k)[0])
            s=2.**(-int(pulses[stop])-1)
        effective=np.minimum(age,stop)
        c=t*np.exp2(ones[effective])
        d=s*np.exp2(pulses[effective])
        running=(age<=stop).astype(float)
        stopping=(age==stop).astype(float)
        residuals[f'C_{ix}']=err(np.roll(c,-1,axis=1)-reset_next*t-(1-reset_next)*c*(1+g*(running-stopping)))
        residuals[f'D_{ix}']=err(np.roll(d,-1,axis=1)-reset_next*s-(1-reset_next)*d*(1+f*(running-stopping)))
        residuals[f'H_{ix}']=err(np.roll(running,-1,axis=1)-reset_next-(1-reset_next)*(running-stopping))
        residuals[f'stop_{ix}']=err((d-.5)*stopping)
        assert np.min(c)>=0 and np.max(c)<=1+1e-12
        assert np.min(d)>=0 and np.max(d)<=1+1e-12
    maximum=max(residuals.values())
    assert maximum<2e-12,residuals
    return {'clock_bits':nc,'clock_block_dimension':size*size,'max_new_residual':maximum,
            'checked_equations':len(residuals),'note':'Inherited clock defects excluded from this maximum.'}

def noncommuting_identities():
    rng=np.random.default_rng(287)
    maximum=0.
    for _ in range(100):
        def pos():
            u,_=np.linalg.qr(rng.standard_normal((4,4)))
            return u@np.diag(rng.uniform(.05,.95,4))@u.T
        a,an,y,yn=pos(),pos(),pos(),pos()
        h=int(rng.integers(2,100)); n=int(rng.integers(1,h)); s=int(rng.choice([-1,0,1]))
        aa=1/(h+1); bb=n/(h+1); bbnext=(bb+s*aa)/(1+aa)
        eye=np.eye(4)
        ra=an@(eye+a)-a
        ry=yn@(eye+a)-y-s*a
        maximum=max(maximum,err((1+aa)*(an-aa/(1+aa)*eye)-ra-(eye-an)@(a-aa*eye)),
                    err((1+aa)*(yn-bbnext*eye)-ry-(y-bb*eye)-(s*eye-yn)@(a-aa*eye)))
    assert maximum<2e-14
    return maximum

def weighted_bad_branch():
    result=[]
    xi=np.diag(np.sqrt([.7,.3]))
    eye=np.eye(2); truth=np.diag([1.,0.]); static=np.diag([.8,.2])
    for h in (0,7,63):
        a=1/(h+1); y=np.diag([0.,a]); witness=np.zeros((2,2))
        rows=[]
        for theta in (1e-2,1e-3,1e-4,1e-5,1e-6):
            u=np.array([[math.cos(theta),-math.sin(theta)],[math.sin(theta),math.cos(theta)]])
            z=u@truth@u.T
            norm=lambda m: float(np.linalg.norm(m@xi,'fro'))
            defects=[norm(y@z),norm((y-a*eye-witness)@(eye-z)),norm(y@z-z@y),
                     float(np.linalg.norm(z@xi-xi@z,'fro')),norm(static@z-z@static)]
            delta=max(defects)
            bad_zero=norm((eye-z)@truth)
            bad_nonzero=norm(z@(eye-truth))
            bad_input=norm((eye-z)@truth@static)
            rows.append({'theta':theta,'local_delta':delta,'bad_zero':bad_zero,
                         'bad_nonzero':bad_nonzero,'bad_input':bad_input,'bad_over_delta':bad_zero/delta})
        slope=float(np.polyfit(np.log([r['local_delta'] for r in rows]),np.log([r['bad_zero'] for r in rows]),1)[0])
        assert abs(slope-1)<2e-4
        result.append({'age':h,'log_log_slope':slope,'rows':rows})
    return result

def scheduler(count=40000):
    # Abstract coroutine schedule. One background instruction per pulse;
    # q^2 padding is included in the stage's background work budget.
    approximations=[Fraction(1,2)]+[Fraction(2,5)+Fraction((-1)**k,k+4) for k in range(1,30)]
    active=0; position=0; emitted=ones=0; discrepancy=0.; maximum_discrepancy=0.; cost=0
    ready=False; work=0; switches=[]; weighted_target=0.
    while emitted<count:
        p,q=approximations[active].numerator,approximations[active].denominator
        bit=int(position<p)
        ones+=bit; emitted+=1; position=(position+1)%q
        weighted_target+=p/q
        discrepancy=ones-weighted_target
        maximum_discrepancy=max(maximum_discrepancy,abs(discrepancy))
        assert abs(discrepancy)<=q+1e-6
        assert active==0 or q*q<=emitted
        cost+=10*(q+1)
        if not ready and active+1<len(approximations):
            work+=1
            pending=approximations[active+1].denominator
            budget=pending*pending+17*(active+1)**3
            if work>=budget: ready=True
        if ready and position==0:
            active+=1; position=0; work=0; ready=False
            switches.append({'pulse':emitted,'stage':active,'p':approximations[active].numerator,'q':approximations[active].denominator})
            assert approximations[active].denominator**2<=emitted
    assert cost<=100*(count+1)**2
    return {'pulses':count,'observed_density':ones/count,'limit_for_this_example':.4,
            'stage_switches':switches,'max_period_discrepancy':maximum_discrepancy,
            'conservative_microstep_cost':cost,'quadratic_cost_bound':100*(count+1)**2,
            'scope':'Abstract scheduler arithmetic; not a compiled universal-machine implementation.'}

def cheap_closures():
    alpha=[math.sqrt(2)/4,math.sqrt(3)/8]; bases=[2,3]; n=5
    beta=sum(a*math.log(m) for a,m in zip(alpha,bases))/math.log(n)
    depth=np.arange(513)
    products=np.ones(len(depth))
    for a,m in zip(alpha,bases): products*=np.power(float(m),np.floor(depth*a))
    largest=0.; domain=0.; penalty_ratio=0.
    age=np.arange(32)
    for t in (0.,1.,.5,np.nextafter(.5,0.),.25,.01,2.**-80):
        j=512 if t==0 else int(np.searchsorted(products,1/t,side='right')-1)
        assert j<512 or t==0
        s=0. if t==0 else n**(-j-1)
        c=t*products[np.minimum(age,j)]
        d=s*np.power(float(n),np.minimum(age,j))
        h=(age<=j).astype(float); p=(age==j).astype(float)
        growth=np.ones_like(age,dtype=float)
        for a,m in zip(alpha,bases):
            carry=np.floor((age+1)*a)-np.floor(age*a)
            growth*=1+(m-1)*carry*(h-p)
        largest=max(largest,err(c[1:]-c[:-1]*growth[:-1]),err(d[1:]-d[:-1]*(1+(n-1)*(h[:-1]-p[:-1]))),err((d-1/n)*p))
        domain=max(domain,float(np.max(c)))
        if t: penalty_ratio=max(penalty_ratio,s/t**(1/beta))
    assert largest<2e-12 and domain<=1+1e-12 and penalty_ratio<=1+1e-12
    b1,b2=math.sqrt(2)/2,(math.sqrt(5)-1)/2
    def penalty(t,b):
        if not t: return 0.
        k=floor_log_reciprocal(t); j=math.ceil((k+1)/b)-1
        return 2.**(-j-1)
    ratio=0.
    for k in range(50):
        for scale in (1.,1.000001,.999999):
            t=min(1.,2.**(-k)*scale)
            final=penalty(penalty(t,b1),b2)
            ratio=max(ratio,final/t**(1/(b1*b2)))
    assert ratio<=1+1e-12
    return {'mixed_beta':beta,'subset_max_multiplier':6,'denominator_multiplier':5,
            'max_mixed_history_residual':largest,'max_mixed_penalty_power_ratio':penalty_ratio,
            'product_beta':b1*b2,'max_chained_penalty_power_ratio':ratio}

def main():
    result={'thread_limits':{k:os.environ[k] for k in ('OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS')},
            'finite_scaled_counter_models':[finite_model(nc) for nc in (2,3,5)],
            'noncommuting_identity_error':noncommuting_identities(),
            'weighted_bad_branches':weighted_bad_branch(),
            'scheduler':scheduler(),'cheap_closures':cheap_closures(),
            'status':'PASS (finite and local checks; uniform proofs are in RESULT.md)'}
    (ROOT/'numerics.json').write_text(json.dumps(result,indent=2)+'\n',encoding='utf-8')
    print(result['status'])
    print('Largest new finite residual:',max(r['max_new_residual'] for r in result['finite_scaled_counter_models']))
    print('Noncommuting identity error:',result['noncommuting_identity_error'])
    print('Bad-branch slopes:',[r['log_log_slope'] for r in result['weighted_bad_branches']])
    print('Mixed and product exponents:',result['cheap_closures']['mixed_beta'],result['cheap_closures']['product_beta'])
    print('Scheduler stages loaded:',len(result['scheduler']['stage_switches']))

if __name__=='__main__': main()
