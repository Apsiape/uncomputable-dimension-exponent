"""Small exact-code and numerical CAR/affine attacks. No large matrices."""
import os
for name in ['OMP_NUM_THREADS', 'OPENBLAS_NUM_THREADS', 'MKL_NUM_THREADS', 'NUMEXPR_NUM_THREADS']:
    os.environ[name] = '1'
import itertools
import json
import math
from fractions import Fraction
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parent
IRRED = {1: 0b11, 2: 0b111, 3: 0b1011, 4: 0b10011, 5: 0b100101}

def gf_mul(x, y, m):
    result = 0
    while y:
        if y & 1:
            result ^= x
        y >>= 1
        x <<= 1
        if x & (1 << m):
            x ^= IRRED[m]
    return result

def code(N, k):
    m = (N-1).bit_length()
    cols = []
    for a in range(N):
        col, power = 1, 1
        for r in range(1, 2*k):
            power = gf_mul(power, a, m)
            col |= power << (1 + m*(r-1))
        cols.append(col)
    return cols, 1+(2*k-1)*m

def parity(x):
    return x.bit_count() & 1

def exact_codes():
    records = []
    for N,k in [(2,1),(3,1),(4,2),(5,2),(8,2),(5,3),(8,3)]:
        cols,n = code(N,k)
        for size in range(1,min(2*k,N)+1):
            for sub in itertools.combinations(cols,size):
                total = 0
                for col in sub:
                    total ^= col
                assert total != 0, (N,k,sub)
        hist = {}
        for u in range(1 << n):
            s = sum(1-2*parity(col & u) for col in cols)
            hist[s] = hist.get(s,0)+1
        numer = sum(count*s**(2*k) for s,count in hist.items())
        full = Fraction(numer, (1 << n)*N**(2*k))
        nonzero = Fraction(numer-N**(2*k), ((1 << n)-1)*N**(2*k))
        B = math.prod(range(1,2*k,2))
        bound = Fraction(B,N**k)
        assert nonzero <= full <= bound
        real_checks = []
        for nu in [x/2 for x in range(2,2*k+1)]:
            moment = (sum(count*abs(s/N)**(2*nu) for s,count in hist.items())-1)/((1 << n)-1)
            upper = B**(nu/k)*N**(-nu)
            assert moment <= upper+1e-13
            real_checks.append({'nu':nu,'moment_nonzero':moment,'bound':upper})
        records.append({'N':N,'k':k,'n0':n,'integer_moment':str(full),
                        'nonzero_integer_moment':str(nonzero),'bound':str(bound),
                        'real_moments':real_checks})
    return records

def majorana_checks():
    records = []
    for N in [2,3]:
        cols,n = code(N,1)
        modes,dim = 3*N,1 << (3*N)
        eye = np.eye(dim,dtype=complex)
        gammas = []
        for j in range(modes):
            matrix = np.zeros((dim,dim),complex)
            for mask in range(dim):
                matrix[mask^(1 << j),mask] = 1-2*parity(mask&((1 << j)-1))
            gammas.append(matrix)
        errors = {}
        def save(name, value):
            errors[name] = max(errors.get(name,0),float(value))
        def err(matrix):
            return np.linalg.norm(matrix,'fro')/math.sqrt(dim)
        for i in range(modes):
            for j in range(modes):
                save('CAR',err(gammas[i]@gammas[j]+gammas[j]@gammas[i]-(2*eye if i==j else 0)))
        lamps = {}
        for u in range(1 << n):
            signs = np.array([1-2*parity(c&u) for c in cols],float)/math.sqrt(N)
            A,B,C = [sum(signs[j]*gammas[3*j+f] for j in range(N)) for f in range(3)]
            X,Z = 1j*A@B,1j*A@C
            lamps[u] = (A,B,C,X,Z)
            save('reflection',max(err(X@X-eye),err(Z@Z-eye),err(X-X.conj().T),err(Z-Z.conj().T)))
            save('onsite',err(X@Z+Z@X))
        for u,w in [(0,1),(0,2),(0,3),(2,3)]:
            if w >= (1 << n):
                continue
            A,B,C,X,Z=lamps[u]
            Ap,Bp,Cp,Xp,Zp=lamps[w]
            c=sum(1-2*parity(col&(u^w)) for col in cols)/N
            save('mixed_additive_5',err(X@Zp-Zp@X-2*c*B@Cp))
            R=(X@Zp@X@Zp-eye)/2
            save('scalar_absolute_6',err(R.conj().T@R-c*c*eye))
            save('same_type_formula',err(X@Xp-Xp@X+2*c*(Ap@A+Bp@B-2*c*eye)))
            same=(X@Xp@X@Xp-eye)/2
            actual=np.linalg.norm(same,2)
            assert actual <= 2*abs(c)*math.sqrt(max(0,1-c*c))+1e-12
        translation_diags={}
        for u in range(1 << n):
            negative=sum((1 << (3*j+f)) for j,col in enumerate(cols) if parity(col&u) for f in range(3))
            translation_diags[u]=np.array([1-2*parity(mask&negative) for mask in range(dim)])
        for u in range(1 << n):
            for w in range(1 << n):
                assert np.array_equal(translation_diags[u]*translation_diags[w],translation_diags[u^w])
        for u,w in [(1,0),(2,1),(3,2)]:
            phase=translation_diags[u]
            for idx in [3,4]:
                save('translation_8',err(phase[:,None]*lamps[w][idx]*phase[None,:]-lamps[u^w][idx]))
        assert max(errors.values()) < 2e-12,errors
        records.append({'N':N,'complex_modes':modes,'fock_dimension':dim,'normalized_Frobenius_errors':errors})
    return records

def apply_binary(g,u):
    result=0
    for j,col in enumerate(g):
        if u>>j&1:
            result ^= col
    return result

def affine_checks():
    G=[g for g in itertools.product(range(8),repeat=3)
       if len({apply_binary(g,u) for u in range(8)})==8]
    assert len(G)==168
    def mul(g,h):
        return tuple(apply_binary(g,col) for col in h)
    def inverse(g):
        return tuple(next(u for u in range(8) if apply_binary(g,u)==(1<<j)) for j in range(3))
    inv={g:inverse(g) for g in G}
    hist={u:0 for u in range(1,8)}
    checks=0
    for g in G:
        hist[apply_binary(inv[g],1)]+=1
        for h in G:
            # L_h T_u L_h^*: fibre at g is U_(g^-1 h u).
            old=mul(inv[g],h)
            for u in range(8):
                assert apply_binary(inv[mul(inv[h],g)],u)==apply_binary(old,u)
                assert apply_binary(old,u)==apply_binary(inv[g],apply_binary(h,u))
                checks+=1
    assert set(hist.values())=={24}
    return {'GL_3_order':len(G),'covariance_checks':checks,'g_inverse_e1_histogram':hist,
            'translation_representation':'exact binary XOR; full Fock checks above'}

if __name__=='__main__':
    result={'thread_environment':{name:os.environ[name] for name in ['OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS']},
            'character_codes':exact_codes(),'majorana_lamps':majorana_checks(),'affine':affine_checks()}
    target=ROOT/'moments-lamps-results.json'
    target.write_text(json.dumps(result,indent=2),encoding='utf-8')
    print(json.dumps(result,indent=2))
