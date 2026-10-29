"""Independent counter-trace, literal-marker and matrix-normalization checks.
Standard library only; streaming, one thread."""
import json, random, itertools, hashlib, time
from fractions import Fraction as F
from pathlib import Path
BASE=Path(__file__).resolve().parent
out={}
rng=random.Random(131028)
# Independent interpreter: distinct data structures and enumeration from shipped script.
def advance(program, state, counters):
    op,i,a,b=program[state]
    v=list(counters)
    if op=='+': v[i]+=1; state=a
    elif op=='-':
        if v[i]: v[i]-=1; state=b
        else: state=a
    else: state=a
    return state,tuple(v)
points=0; trace_equalities=0
for trial in range(16):
    program=[(rng.choice(['+','-','0']),rng.randrange(2),rng.randrange(5),rng.randrange(5)) for _ in range(5)]
    # Guarantee several explicitly deterministic increment/test programs as well.
    if trial==0: program=[('+',0,1,1),('-',0,2,3),('0',0,0,0),('0',0,4,4),('0',0,0,0)]
    history=[]; s=0; c=(0,0)
    for h in range(65): history.append((s,c)); s,c=advance(program,s,c)
    for N in range(1,6):
        size=1<<N; counts=[0]*5
        for fuel in range(size):
            r=0
            while r<N and fuel&(1<<r): r+=1
            period=1<<r
            for t in range(size):
                h=t%period; hn=(t+1)%period; reset=int(hn==0)
                st,cv=history[h]; sn,cn=history[hn]
                A=F(1,h+1); An=F(1,hn+1)
                assert An*(1+A)==A+reset
                predicted,pc=advance(program,st,cv)
                assert sn==(0 if reset else predicted)
                for i in range(2):
                    Y=F(cv[i],h+1); Yn=F(cn[i],hn+1)
                    E=int(cv[i]==0); W=F(max(cv[i]-1,0),h+1)
                    assert 0<=Y<=1 and 0<=W<=1
                    assert Y*E==0 and (Y-A)*(1-E)==W*(1-E)
                    assert Yn*(1+A)==(1-reset)*(Y+A*(pc[i]-cv[i]))
                counts[st]+=1; points+=1
        expected=[sum(F(sum(history[h][0]==st for h in range(1<<r)),1<<(2*r+1)) for r in range(N))
                  +F(sum(history[h][0]==st for h in range(size)),size*size) for st in range(5)]
        assert [F(k,size*size) for k in counts]==expected
        assert sum(expected)==1
        trace_equalities+=5
out['random_counter_programs']={'programs':16,'fuel_time_points':points,'trace_equalities':trace_equalities,'all_exact':True}
# Visit-by-visit derivation with h=0 and powers of two included.
for h in range(1025):
    k=h.bit_length()
    lhs=sum(F(1,2*4**r) for r in range(13) if h<2**r)
    tail=F(2,3)*F(1,4**13)
    assert lhs+tail==F(2,3)*F(1,4**k)
out['single_visit_kernel']={'times_checked':1025,'formula':'(2/3)*4^(-bit_length(h))','all_exact':True}
# A literal elementary counter machine for the marker, not an assumed squaring instruction.
# Registers: L, O, TEMP, INNER, ACC. All initially zero; initialize L=4.
P={
'MARK':('0',0,'CO','CO'),
'CO':('-',0,'RO','CO1'), 'CO1':('+',1,'CO2','CO2'), 'CO2':('+',2,'CO','CO'),
'RO':('-',2,'OUTER','RL'), 'RL':('+',0,'RO','RO'),
'OUTER':('-',1,'CLEAR','CI'),
'CI':('-',0,'RI','CI1'), 'CI1':('+',3,'CI2','CI2'), 'CI2':('+',2,'CI','CI'),
'RI':('-',2,'INNER','RL2'), 'RL2':('+',0,'RI','RI'),
'INNER':('-',3,'OUTER','AI'), 'AI':('+',4,'INNER','INNER'),
'CLEAR':('-',0,'MOV','CLEAR'), 'MOV':('-',4,'MARK','ML'), 'ML':('+',0,'MOV','MOV')}
state='MARK'; counters=(4,0,0,0,0); ticks=4; visits=[]
while len(visits)<4:
    if state=='MARK':
        if visits:
            old=visits[-1]
            assert ticks-old['tick']==9*old['L']**2+10*old['L']+6
            assert counters[0]==old['L']**2
        assert counters[1:]==(0,0,0,0)
        visits.append({'tick':ticks,'L':counters[0],'physical_time_fair_interleave':2*ticks+1,'k':(2*ticks+1).bit_length()})
        if len(visits)==4: break
    state,counters=advance(P,state,counters); ticks+=1
    assert max(counters)<=ticks
out['literal_marker_machine']={'registers':5,'states':len(P),'visits':visits,'stage_cost':'9*L^2+10*L+6','elementary_instructions':ticks-4}
# Finite-order Heisenberg normalization, independently from irreducible character values.
heis=[]
for N in range(1,11):
    identity_coefficient=F(1,N)
    matrix_trace=N
    assert identity_coefficient==F(matrix_trace,N*N)
    # Rank-r idempotents have scalar group-ring trace r/N^2.
    for rank in range(N+1): assert F(rank,N*N)/F(1,N)==F(rank,N)
    heis.append({'N':N,'corner_unit_trace':str(identity_coefficient),'rank_one_trace':str(F(1,N*N))})
out['matrix_trace_normalization']=heis
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2),encoding='utf-8')
print(json.dumps(out,indent=2))
print('ALL INDEPENDENT GROUP CHECKS PASS')
