"""Rebuild the cited clock. Test group-algebra lift in small representations.

Natural coordinate matrices test all/selected plaquette holonomies. Sparse
permutation actions on F_2^n test translations and transvections without ever
materializing the exponentially large affine-register representation.
"""
import os
for name in ['OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS']:
    os.environ[name]='1'
from collections import defaultdict, deque
import json
import math
from pathlib import Path
import numpy as np

ROOT=Path(__file__).resolve().parent

def cycle(r,n):
    a=np.arange(n)
    a[0]=r-1
    a[1:r]=np.arange(r-1)
    return a

def swap(i,j,n):
    a=np.arange(n)
    a[i-1],a[j-1]=a[j-1],a[i-1]
    return a

def inv(a):
    return np.argsort(a)

def right_product(*arrays):
    a=np.arange(len(arrays[0]))
    for b in arrays:
        a=b[a]
    return a

def perm_matrix(a):
    return np.eye(len(a),dtype=complex)[:,a]

def bitperm(a,mask):
    out=0
    while mask:
        low=mask&-mask
        out |= 1 << int(a[low.bit_length()-1])
        mask ^= low
    return out

class Clock:
    def __init__(self,M):
        self.M,self.n=M,4*M+4
        n=self.n
        ell=2*M+2
        tau=swap(1,2,n)
        D=[cycle(2*ell-M+1,n)]
        for i in range(M-1):
            D.append(right_product(inv(cycle(ell-i-(M-1),n)),tau,D[-1],cycle(ell-i,n)))
        self.A={};self.B={}
        for i in range(M):
            for j in range(M):
                self.A[i,j]=cycle(ell-i-j,n)
                self.B[i,j]=cycle(2*ell-j,n) if j<M-1 else D[i]
        self.A[M-1,M-1]=right_product(swap(1,M+4,n),self.A[M-1,M-1])
        self.B[0,M-2]=right_product(swap(5,M+5,n),self.B[0,M-2])
        bulk={(M-1,M-1)}|{(M-1,j) for j in range(1,M-1)}|{
            (i,j) for i in range(M-2) for j in range(M-1) if i+j<=M-3}
        top={(0,M-2)}|{(i,j) for i in range(M-2) for j in range(M-2) if i+j<=M-3}
        self.regions={'B':bulk,'T':top}
        self.sources={'B':(M-1,M-1),'T':(0,M-2)}
        assert len(bulk)==M*(M-1)//2
        assert len(top)==1+(M-1)*(M-2)//2
        self.phi={tag:self.potentials(tag) for tag in self.regions}

    def faces(self,q):
        i,j=q;M=self.M
        return [(('a',i,j),1),(('b',(i+1)%M,j),1),
                (('a',i,(j+1)%M),-1),(('b',i,j),-1)]

    def potentials(self,tag):
        R=self.regions[tag]
        incidence=defaultdict(list)
        for q in R:
            for edge,sign in self.faces(q):
                incidence[edge].append((q,sign))
        neighbors=defaultdict(list)
        for edge,entries in incidence.items():
            if len(entries)==2:
                (a,sa),(b,sb)=entries
                assert sa==-sb
                neighbors[a].append((b,edge,sa))
                neighbors[b].append((a,edge,sb))
        source=self.sources[tag]
        order=[source];parents={source:None}
        for a in order:
            for b,edge,sa in neighbors[a]:
                if b not in parents:
                    parents[b]=(a,edge,-sa)
                    order.append(b)
        assert len(order)==len(R),(self.M,tag,'disconnected')
        need={q:math.pi/len(R)-(math.pi if q==source else 0) for q in R}
        result={}
        for q in reversed(order[1:]):
            parent,edge,sign=parents[q]
            result[edge]=need[q]/sign
            need[parent]+=need[q]
        assert abs(need[source])<1e-11
        for q in R:
            actual=sum(sign*result.get(edge,0) for edge,sign in self.faces(q))
            target=math.pi/len(R)-(math.pi if q==source else 0)
            assert abs(actual-target)<1e-11
        return result

    def label(self,tag,c):
        i,j=c;M=self.M;n=self.n
        pairs=[]
        if tag=='B':
            for t in range(5,M+4):
                pair=(t+M-1-j,t+2*M-1-j) if i==M-1 else (t+M-1-i-j,t+2*M-1-j)
                pairs.append(pair)
        else:
            pairs=[(M+3-i-j,2*M+3-j)]
        a=np.arange(n)
        for x,y in pairs:
            assert 1<=x<=n and 1<=y<=n,(tag,c,x,y)
            a[x-1],a[y-1]=a[y-1],a[x-1]
        assert np.array_equal(a[a],np.arange(n))
        return a

    def corrections(self,kind,c):
        return [(self.phi[tag].get((kind,*c),0),self.label(tag,c))
                for tag in ['B','T'] if abs(self.phi[tag].get((kind,*c),0))>1e-15]

    def link_matrix(self,kind,c):
        base=(self.A if kind=='a' else self.B)[c]
        W=perm_matrix(inv(base))
        eye=np.eye(self.n,dtype=complex)
        for angle,p in self.corrections(kind,c):
            phase=np.exp(1j*angle)
            rotation=(1+phase)/2*eye+(1-phase)/2*perm_matrix(p)
            W=rotation@W
        return W

    def geometry_and_curvature(self):
        M,n=self.M,self.n
        eye=np.eye(n,dtype=complex)
        tau=perm_matrix(swap(1,2,n))
        maxcurv,maxlocal,maxprotected=0.,0.,0.
        for c in self.A:
            for kind,base in [('a',self.A[c]),('b',self.B[c])]:
                a=inv(base)
                assert (a[0],a[1])==(1,2)
                for angle,label in self.corrections(kind,c):
                    assert np.array_equal(label[1:4],np.arange(1,4))
                    maxprotected=max(maxprotected,float(np.max(np.abs(label[1:4]-np.arange(1,4)))))
        qs=list(self.A) if M<10 else [(0,0),(0,M-2),(M-1,M-1),(M-1,M-2),(M-2,0),
                                     (1,1),(2,M-5),(M//2,0),(0,M//2),(M-3,0)]
        for i,j in qs:
            A=self.link_matrix('a',(i,j));B1=self.link_matrix('b',((i+1)%M,j))
            A2=self.link_matrix('a',(i,(j+1)%M));B=self.link_matrix('b',(i,j))
            actual=A@B1@A2.conj().T@B.conj().T@tau
            expected=eye.copy()
            for tag in ['B','T']:
                if (i,j) in self.regions[tag]:
                    angle=math.pi/len(self.regions[tag])
                    phase=np.exp(1j*angle)
                    rotation=(1+phase)/2*eye+(1-phase)/2*perm_matrix(self.label(tag,(i,j)))
                    expected=rotation@expected
            maxcurv=max(maxcurv,float(np.linalg.norm(actual-expected,2)))
            bound=sum(math.pi/len(self.regions[tag]) for tag in ['B','T'] if (i,j) in self.regions[tag])
            assert np.linalg.norm(actual-eye,2)<=bound+1e-10
        assert maxcurv<1e-10,(M,maxcurv)
        return {'M':M,'coordinates':n,'region_sizes':{k:len(v) for k,v in self.regions.items()},
                'curvature_plaquettes_tested':len(qs),'max_curvature_formula_error':maxcurv,
                'all_active_labels_fix_2_3_4':True}

    def op(self,token,vector):
        out=defaultdict(complex)
        if token in 'pPqQ':
            kind='a' if token.lower()=='p' else 'b'
            inverse=token.isupper();axis=0 if kind=='a' else 1
            for (i,j,mask),amp in vector.items():
                c=[i,j]
                if not inverse:
                    c[axis]=(c[axis]-1)%self.M
                c=tuple(c)
                base=(self.A if kind=='a' else self.B)[c]
                branches={mask:amp}
                if not inverse:
                    branches={bitperm(inv(base),mask):amp}
                corrections=self.corrections(kind,c)
                if inverse:
                    corrections=list(reversed(corrections))
                for angle,label in corrections:
                    phase=np.exp((-1j if inverse else 1j)*angle)
                    new=defaultdict(complex)
                    for value,a in branches.items():
                        new[value]+=(1+phase)/2*a
                        new[bitperm(label,value)]+=(1-phase)/2*a
                    branches=new
                dest=list(c)
                if inverse:
                    dest[axis]=(dest[axis]+1)%self.M
                    branches={bitperm(base,value):a for value,a in branches.items()}
                for value,a in branches.items():
                    out[(*dest,value)]+=a
        else:
            for (i,j,mask),amp in vector.items():
                if token=='t':value=mask^1
                elif token=='u':value=mask^2
                elif token=='v':value=mask^4
                elif token=='d':value=mask^(2 if mask&1 else 0)
                elif token=='e':value=mask^(4 if mask&2 else 0)
                elif token=='s':value=bitperm(swap(1,2,self.n),mask)
                elif token=='B':value=bitperm(swap(2,3,self.n),mask)
                else:raise ValueError(token)
                out[i,j,value]+=amp
        return {key:a for key,a in out.items() if abs(a)>1e-14}

    def word(self,word,vector):
        for token in reversed(word):
            vector=self.op(token,vector)
        return vector

    def affine_identities(self):
        M=self.M
        clocks=list(self.A) if M<10 else [(0,0),(0,M-2),(M-1,M-1),(M-1,M-2),(M//2,0)]
        rng=np.random.default_rng(20261028+M)
        masks=[0,1,2,4,8,1<<4,1<<(M+4),(1<<4)^1]
        vector={(i,j,mask):complex(rng.normal(),rng.normal()) for i,j in clocks for mask in masks}
        norm=math.sqrt(sum(abs(x)**2 for x in vector.values()))
        vector={key:a/norm for key,a in vector.items()}
        tests={'14_p_e1':('ptP','u'),'14_q_e1':('qtQ','u'),'14_p_e2':('puP','v'),
               '15_p_d':('pdP','e'),'15_q_d':('qdQ','e'),
               '16_t_square':('tt',''),'16_translation_commute':('tutu',''),
               '16_transvection':('dtd','tu'),'16_d_e2':('dudu',''),'16_d_e3':('dvdv',''),
               'H_s_square':('ss',''),'H_braid':('spsPspsPspsP',''),
               'H_far':('sppsPPsppsPP',''),'H_equal':('psPqsQ',''),
               'prototype_t_p':('tsptPs',''),'prototype_t_q':('tsqtQs',''),
               'prototype_d_p':('dBspdPsB',''),'prototype_d_q':('dBsqdQsB','')}
        errors={}
        for name,(left,right) in tests.items():
            a=self.word(left,vector);b=self.word(right,vector)
            error=math.sqrt(sum(abs(a.get(key,0)-b.get(key,0))**2 for key in a.keys()|b.keys()))
            errors[name]=error
        assert max(errors.values())<1e-10,(M,errors)
        return errors

if __name__=='__main__':
    records=[]
    for M in [4,6,48]:
        c=Clock(M)
        result=c.geometry_and_curvature()
        result['sparse_affine_identity_errors']=c.affine_identities()
        records.append(result)
        print(json.dumps(result),flush=True)
    (ROOT/'clock-results.json').write_text(json.dumps(records,indent=2),encoding='utf-8')
