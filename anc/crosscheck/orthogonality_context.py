import numpy as np
rng=np.random.default_rng(7)
def rand_inv(n):
    q,_=np.linalg.qr(rng.normal(size=(n,n))); return q@np.diag(rng.choice([-1,1],size=n))@q.T
def kron(*ms):
    r=np.eye(1)
    for m in ms: r=np.kron(r,m)
    return r
q=2;L=4;d=3
Xp=np.array([[0,1],[1,0.]]);Zp=np.diag([1.,-1]);I2=np.eye(2);Id=np.eye(d)
Xs=[kron(Xp,I2,Id),kron(I2,Xp,Id)];Zs=[kron(Zp,I2,Id),kron(I2,Zp,Id)]
E=kron(np.ones((2,2))/2,np.ones((2,2))/2,Id)
worst=0
for t in range(20):
    # near-solution: words W_j with small sum (approx relation): W, -W pairs perturbed
    A=rand_inv(d); B=rand_inv(d)
    eps=1e-2*rng.normal(size=(d,d)); u_,s_,vt_=np.linalg.svd(A@B+eps); A2=u_@vt_
    W=[np.kron(np.eye(L),A@B),np.kron(np.eye(L),-A2),np.kron(np.eye(L),Id),np.kron(np.eye(L),-Id)]
    ej=[]
    for bits in [(0,0),(0,1),(1,0),(1,1)]:
        P=np.eye(L*d)
        for i,bt in enumerate(bits): P=P@((np.eye(L*d)+(1-2*bt)*Zs[i])/2)
        ej.append(P)
    S=sum(e@w for e,w in zip(ej,W)); F=S@E@S.T
    M_=(np.eye(L*d)-E)@F; U,s,Vt=np.linalg.svd(M_); rk=(s>1e-10).sum(); Fp=U[:,:rk]@U[:,:rk].T
    worst=max(worst,max(np.linalg.norm(Fp@X-X@Fp) for X in Xs))
    ef=np.linalg.norm(E@F)
print("max ||[F',X_i]|| (orthogonality-context negative control):",worst," last ||EF||:",ef)
