from fractions import Fraction as Fr
from itertools import product

def maj(a,b,c): return (a&b)^(a&c)^(b&c)
cube = list(product((0,1),repeat=3))
def aff(co,p): return co[0]+co[1]*p[0]+co[2]*p[1]+co[3]*p[2]

def mobius(fv):
    coef={}
    for S in cube:
        s=Fr(0)
        for T in cube:
            if all(t<=sv for t,sv in zip(T,S)):
                s += (-1)**(sum(S)-sum(T))*fv[T]
        coef[S]=s
    return coef

found=[]
R=range(-5,6)
for B in product(R,repeat=4):
    if 2*B[0]+B[1]+B[2]+B[3] != 0: continue          # abc coeff of maj*B must vanish
    vb=[aff(B,p) for p in cube]
    if any(v==0 for v in vb): continue                # multiplier nonzero on cube
    # need L1 (l0..l3) with quad part of (maj+L1)*B == 0
    # quad coeffs of L1*B: ab: l1*B2+l2*B1 ; ac: l1*B3+l3*B1 ; bc: l2*B3+l3*B2  (l0 none)
    mb = mobius({p: Fr(maj(*p))*aff(B,p) for p in cube})
    tgt = {(1,1,0):-mb[(1,1,0)], (1,0,1):-mb[(1,0,1)], (0,1,1):-mb[(0,1,1)]}
    b0,b1,b2,b3=B
    import itertools
    A=[[b2,b1,0],[b3,0,b1],[0,b3,b2]]
    y=[tgt[(1,1,0)],tgt[(1,0,1)],tgt[(0,1,1)]]
    det = -2*b1*b2*b3 if False else (A[0][0]*(A[1][1]*A[2][2]-A[1][2]*A[2][1]) - A[0][1]*(A[1][0]*A[2][2]-A[1][2]*A[2][0]) + A[0][2]*(A[1][0]*A[2][1]-A[1][1]*A[2][0]))
    if det==0: continue
    # Cramer
    def solve3(A,y):
        d=(A[0][0]*(A[1][1]*A[2][2]-A[1][2]*A[2][1]) - A[0][1]*(A[1][0]*A[2][2]-A[1][2]*A[2][0]) + A[0][2]*(A[1][0]*A[2][1]-A[1][1]*A[2][0]))
        xs=[]
        for i in range(3):
            M=[r[:] for r in A]
            for r in range(3): M[r][i]=y[r]
            di=(M[0][0]*(M[1][1]*M[2][2]-M[1][2]*M[2][1]) - M[0][1]*(M[1][0]*M[2][2]-M[1][2]*M[2][0]) + M[0][2]*(M[1][0]*M[2][1]-M[1][1]*M[2][0]))
            xs.append(Fr(di,d))
        return xs
    l1,l2,l3 = solve3(A,y)
    for l0 in (Fr(0),):  # l0 free; 0 is fine
        L1=(l0,l1,l2,l3)
        fv={p: (Fr(maj(*p))+aff(L1,p))*aff(B,p) for p in cube}
        cf=mobius(fv)
        if any(cf[S]!=0 for S in [(1,1,0),(1,0,1),(0,1,1),(1,1,1)]): continue
        L3=(cf[(0,0,0)],cf[(1,0,0)],cf[(0,1,0)],cf[(0,0,1)])
        # verify: for all cube pts and z in {0,1}, (z+L1)*B == L3  iff  z == maj
        okk=True
        for p in cube:
            for z in (0,1):
                lhs=(z+aff(L1,p))*aff(B,p)
                if (lhs==aff(L3,p)) != (z==maj(*p)): okk=False
        if okk: found.append((L1,B,L3))
print("found:",len(found))
for L1,B,L3 in found[:6]:
    ints = all(x.denominator==1 for x in list(L1)+list(L3))
    print("int" if ints else "frac"," L1=",tuple(map(str,L1))," B=",B," L3=",tuple(map(str,L3)))
