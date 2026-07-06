from fractions import Fraction as Fr
from itertools import product
# Structured search: target t on n-var boolean cube. Seek A,B,C affine with A*B + C == t on cube,
# using B = s*A + L (s scalar, L affine) so A*B = s*A^2 + A*L. Solve linear system over A's coeffs? 
# Simpler+robust: brute A over SMALL coeff set, set B = s*A + L, solve L,C by least-fit then verify.
# Even simpler & complete for our size: brute A and B both but with coeffs in {-3..3} and require |A|structure.
# n<=6 cube=64 pts. A,B have n+1 coeffs. We test A in small set, and for each A solve for (B,C):
#   t(p) - C = A(p)*B(p)  => for fixed A, RHS is linear in B's coeffs; t-... also has C (affine) unknown.
#   Unknowns: B (n+1), C (n+1). Eq per cube point: A(p)*[B coeffs . (1,p)] + [C coeffs .(1,p)] = t(p). Linear! Solve LS exactly.
def aff(co,p): return co[0]+sum(co[i+1]*p[i] for i in range(len(p)))
def search(n, target, Aset):
    cube=list(product((0,1),repeat=n))
    import itertools
    # build for each A: linear system M x = t, x=(Bcoeffs(n+1), Ccoeffs(n+1)); row per cube point
    for A in Aset:
        Avals=[aff(A,p) for p in cube]
        rows=[]; rhs=[]
        for pi,p in enumerate(cube):
            basis=[1]+list(p)
            row=[Avals[pi]*b for b in basis] + [b for b in basis]  # B then C
            rows.append([Fr(x) for x in row]); rhs.append(Fr(target(p)))
        # gaussian solve (least fit; check consistency)
        m=len(rows); ncol=2*(n+1)
        M=[rows[i]+[rhs[i]] for i in range(m)]
        # elimination
        piv=[]; r=0
        for c in range(ncol):
            pr=next((rr for rr in range(r,m) if M[rr][c]!=0),None)
            if pr is None: continue
            M[r],M[pr]=M[pr],M[r]
            M[r]=[v/M[r][c] for v in M[r]]
            for rr in range(m):
                if rr!=r and M[rr][c]!=0:
                    f=M[rr][c]; M[rr]=[a-f*b for a,b in zip(M[rr],M[r])]
            piv.append(c); r+=1
            if r==m: break
        # consistency
        ok=all(not(all(M[rr][c]==0 for c in range(ncol)) and M[rr][ncol]!=0) for rr in range(m))
        if ok:
            x=[Fr(0)]*ncol
            for i,c in enumerate(piv): x[c]=M[i][ncol]
            B=x[:n+1]; C=x[n+1:]
            # verify + M nonzero on cube (A must be nonzero on cube for the row to pin z)
            if all(aff(A,p)*aff(B,p)+aff(C,p)==target(p) for p in cube) and all(aff(A,p)!=0 for p in cube):
                return (A,B,C)
    return None

def ch(e,f,g): return (e&f)^((1-e)&g)
def maj(a,b,c): return (a&b)^(a&c)^(b&c)
import itertools
Aset=list(itertools.product(range(-4,5),repeat=7))  # 6-var A, 9^7=4.7M — feasible-ish; prune later
# too big; restrict A coeffs to {-2..2}
Aset=[A for A in itertools.product(range(-2,3),repeat=7)]
print("Aset size:",len(Aset))
for lam in [2,4]:
    r=search(6, lambda p: ch(p[0],p[1],p[2])+lam*ch(p[3],p[4],p[5]), Aset)
    print(f"Ch-pair lam={lam}: {'FOUND '+str(r) if r else 'none'}")
