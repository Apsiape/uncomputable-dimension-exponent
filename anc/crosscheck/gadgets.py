import numpy as np
rng = np.random.default_rng(1)
def rand_inv(n):
    q,_ = np.linalg.qr(rng.normal(size=(n,n)))
    d = np.diag(rng.choice([-1,1], size=n))
    return q @ d @ q.T
def comm_inv_pair(n):
    # commuting involutions b,c
    q,_ = np.linalg.qr(rng.normal(size=(n,n)))
    b = q @ np.diag(rng.choice([-1,1],size=n)) @ q.T
    c = q @ np.diag(rng.choice([-1,1],size=n)) @ q.T
    return b,c
n=5; I=np.eye(n); Z=np.zeros((n,n))
def blk(a,b,c,d): return np.block([[a,b],[c,d]])
def M(a): return blk(Z,a,a,Z)
def isinv(x): return np.linalg.norm(x@x-np.eye(len(x)))<1e-9 and np.linalg.norm(x-x.T)<1e-9
err=0
# gadget 2: aba=c with [b,c]=0
for t in range(20):
    a = rand_inv(n); b,_ = comm_inv_pair(n)
    c = a@b@a
    if np.linalg.norm(b@c-c@b)>1e-9:
        # force commuting: choose b commuting with aba -> pick a,b commuting? use b,c generic commuting then a any with aba=c: take a conj b->c
        pass
    # construct proper instance: b,c commuting and conjugate
    q,_=np.linalg.qr(rng.normal(size=(n,n)))
    D=np.diag(rng.choice([-1,1],size=n)); b=q@D@q.T
    perm=np.eye(n)[rng.permutation(n)]
    # c = a b a with a an involution: let a be a random involution commuting-structure; simplest: a= reflection swapping eigvecs
    a = rand_inv(n); c = a@b@a
    if np.linalg.norm(b@c-c@b)>1e-9: continue
    A=blk(a,Z,Z,a); B=blk(b,Z,Z,b); C=blk(c,Z,Z,c); I2=np.eye(2*n)
    d1=M(a); d2=M(I); d3=M(b); d4=blk(Z,b@a,a@b,Z); d5=blk(b@a@b,Z,Z,a); d6=blk(b@c,Z,Z,I); d7=blk(b,Z,Z,c)
    for x in [d1,d2,d3,d4,d5,d6,d7]: assert isinv(x)
    ctx=[(A,d1,d2),(B,d2,d3),(d3,d4,d5),(A,d5,d6),(C,d6,d7),(d1,d4,d7)]
    for (x,y,z) in ctx:
        err=max(err,np.linalg.norm(x@y@z-I2),np.linalg.norm(x@y-y@x),np.linalg.norm(x@z-z@x),np.linalg.norm(y@z-z@y))
print("gadget2 max defect (only instances with [b,c]=0):",err)
# commuting-target instances: b diag, a = permutation involution mapping b to commuting c
err=0;cnt=0
for t in range(200):
    b=np.diag(rng.choice([-1.,1.],size=n)); p=rng.permutation(n)
    # make p an involution
    inv=np.arange(n); idx=list(range(n)); rng.shuffle(idx)
    for k in range(0,n-1,2):
        i,j=idx[k],idx[k+1]
        if rng.random()<0.5: inv[i],inv[j]=j,i
    a=np.eye(n)[inv]; c=a@b@a
    A=blk(a,Z,Z,a); B=blk(b,Z,Z,b); C=blk(c,Z,Z,c); I2=np.eye(2*n)
    d1=M(a); d2=M(I); d3=M(b); d4=blk(Z,b@a,a@b,Z); d5=blk(b@a@b,Z,Z,a); d6=blk(b@c,Z,Z,I); d7=blk(b,Z,Z,c)
    for (x,y,z) in [(A,d1,d2),(B,d2,d3),(d3,d4,d5),(A,d5,d6),(C,d6,d7),(d1,d4,d7)]:
        err=max(err,np.linalg.norm(x@y@z-I2),np.linalg.norm(x@y-y@x),np.linalg.norm(x@z-z@x),np.linalg.norm(y@z-z@y))
    cnt+=1
print("gadget2 diag/perm instances",cnt,"max defect",err)
# gadget 1: x1 x2 x1 = x3 general involutions
err=0
for t in range(50):
    X1=rand_inv(n); X2=rand_inv(n); X3=X1@X2@X1; Xs=[X1,X2,X3]
    x=[blk(X,Z,Z,X) for X in Xs]; y=[blk(X,Z,Z,I) for X in Xs]; z=[blk(I,Z,Z,X) for X in Xs]
    f=M(I); w=[M(X) for X in Xs]; g=blk(X2,Z,Z,X3); I2=np.eye(2*n)
    for v in y+z+w+[f,g]: assert isinv(v)
    ctx=[(x[i],y[i],z[i]) for i in range(3)]+[(x[i],f,w[i]) for i in range(3)]+[(g,y[1],z[2])]
    for (a_,b_,c_) in ctx:
        err=max(err,np.linalg.norm(a_@b_@c_-I2),np.linalg.norm(a_@b_-b_@a_),np.linalg.norm(a_@c_-c_@a_),np.linalg.norm(b_@c_-c_@b_))
    for i in range(3): err=max(err,np.linalg.norm(f@y[i]@f-z[i]))
    err=max(err,np.linalg.norm(w[0]@y[1]@w[0]-z[2]))
    # targets commute
    for i in range(3): err=max(err,np.linalg.norm(y[i]@z[i]-z[i]@y[i]))
    err=max(err,np.linalg.norm(y[1]@z[2]-z[2]@y[1]))
print("gadget1 max defect:",err)
# selector identity (1) and bound (2)
q=2; L=2**q; d=3
Xp=np.array([[0,1],[1,0.]]); Zp=np.diag([1.,-1])
def kron(*ms):
    r=np.eye(1)
    for m in ms: r=np.kron(r,m)
    return r
I2=np.eye(2); Id=np.eye(d)
Xs=[kron(Xp,I2,Id),kron(I2,Xp,Id)]; Zs=[kron(Zp,I2,Id),kron(I2,Zp,Id)]
E=kron(np.ones((2,2))/2,np.ones((2,2))/2,Id)
# words: 4 random orthogonal involution products on source
W=[np.kron(np.eye(L),rand_inv(d)@rand_inv(d)) for _ in range(L)]
ej=[]
for bits in [(0,0),(0,1),(1,0),(1,1)]:
    P=np.eye(L*d)
    for i,bt in enumerate(bits): P=P@((np.eye(L*d)+(1-2*bt)*Zs[i])/2)
    ej.append(P)
S=sum(e@w for e,w in zip(ej,W))
print("S unitary:",np.linalg.norm(S@S.T-np.eye(L*d)))
F=S@E@S.T; p2c=sum(W)  # = 2c p
print("EFS-ESE:",np.linalg.norm(E@F@S-E@S@E), " ESE-(1/L)sumW E:",np.linalg.norm(E@S@E-p2c@E/L))
lhs=np.zeros_like(F)
for v in [(0,0),(0,1),(1,0),(1,1)]:
    Zv=np.linalg.matrix_power(Zs[0],v[0])@np.linalg.matrix_power(Zs[1],v[1])
    lhs+=Zv@E@F@S@Zv
print("identity (1) defect:",np.linalg.norm(L*lhs-p2c))
# bound (2) on random projections
worst=0
for t in range(200):
    D=8; k=3; r=4
    Ee=np.linalg.qr(rng.normal(size=(D,k)))[0]; Ee=Ee@Ee.T
    Ff=np.linalg.qr(rng.normal(size=(D,r)))[0]; Ff=Ff@Ff.T
    M_=(np.eye(D)-Ee)@Ff; U,s,Vt=np.linalg.svd(M_); rk=(s>1e-10).sum(); Fp=U[:,:rk]@U[:,:rk].T
    worst=max(worst,np.linalg.norm(Ff-Fp)**2/(2*np.linalg.norm(Ee@Ff)**2))
print("max ||F-F'||^2/(2||EF||^2) over random:",worst)
