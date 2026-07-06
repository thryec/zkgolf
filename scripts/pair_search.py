from fractions import Fraction as Fr
from itertools import product
import sys

def search(nvars, target, wvals, R=range(-4,5), maxfound=4):
    """Find affine L1,M,L3 in nvars vars with (w+L1)*M == L3 on cube iff w == target(pt).
       w packed value can exceed 1 (e.g. z1+4z2), so also check uniqueness over w in wvals."""
    cube=list(product((0,1),repeat=nvars))
    def aff(co,p): return co[0]+sum(co[i+1]*p[i] for i in range(nvars))
    def mobius(fv):
        coef={}
        for S in cube:
            s=Fr(0)
            for T in cube:
                if all(t<=sv for t,sv in zip(T,S)): s+=(-1)**(sum(S)-sum(T))*fv[T]
            coef[S]=s
        return coef
    NL=[S for S in cube if sum(S)>=2]
    lin=[S for S in cube if sum(S)<=1]
    found=[]
    cnt=0
    for M in product(R,repeat=nvars+1):
        vm=[aff(M,p) for p in cube]
        if any(v==0 for v in vm): continue
        cnt+=1
        # solve for L1 (nvars+1 unknowns): nonlinear coeffs of (target+L1)*M must vanish
        base=mobius({p: Fr(target(p))*aff(M,p) for p in cube})
        mons=[mobius({p: Fr(1 if j==0 else p[j-1])*aff(M,p) for p in cube}) for j in range(nvars+1)]
        # linear system: for S in NL: sum_j x_j*mons[j][S] = -base[S]
        rows=[[mons[j][S] for j in range(nvars+1)]+[-base[S]] for S in NL]
        # gaussian elimination, allow underdetermined; detect inconsistency
        n=nvars+1; m=len(rows); piv=[]
        r=0
        for c in range(n):
            pr=None
            for rr in range(r,m):
                if rows[rr][c]!=0: pr=rr; break
            if pr is None: continue
            rows[r],rows[pr]=rows[pr],rows[r]
            rows[r]=[v/rows[r][c] for v in rows[r]]
            for rr in range(m):
                if rr!=r and rows[rr][c]!=0:
                    f=rows[rr][c]; rows[rr]=[a-f*b for a,b in zip(rows[rr],rows[r])]
            piv.append(c); r+=1
            if r==m: break
        # inconsistency?
        bad=False
        for rr in range(m):
            if all(rows[rr][c]==0 for c in range(n)) and rows[rr][n]!=0: bad=True
        if bad: continue
        # particular solution: free vars = 0
        x=[Fr(0)]*n
        for i,c in enumerate(piv): x[c]=rows[i][n]
        L1=tuple(x)
        fv={p:(Fr(target(p))+aff(L1,p))*aff(M,p) for p in cube}
        cf=mobius(fv)
        if any(cf[S]!=0 for S in NL): continue
        L3=tuple(cf[S] for S in lin)  # order: const, x1..xn  (lin sorted? ensure)
        # rebuild L3 as coeff tuple aligned with aff()
        L3co=[cf[tuple(0 for _ in range(nvars))]]
        for i in range(nvars):
            e=[0]*nvars; e[i]=1
            L3co.append(cf[tuple(e)])
        L3=tuple(L3co)
        # uniqueness check over candidate w values
        ok=True
        for p in cube:
            t=target(p)
            for w in wvals:
                lhs=(w+aff(L1,p))*aff(M,p)
                if (lhs==aff(L3,p)) != (w==t): ok=False; break
            if not ok: break
        if ok:
            found.append((L1,M,L3))
            if len(found)>=maxfound: return found,cnt
    return found,cnt

if sys.argv[1]=="x2x2":
    # vars a,b,c,d ; target xor2(a,b) + 4*xor2(c,d) ; w in 0..5 range {0,1,4,5}
    t=lambda p:(p[0]^p[1])+4*(p[2]^p[3])
    f,c=search(4,t,[0,1,4,5],R=range(-4,5))
    print("xor2+xor2(lam=4) found:",len(f))
    for L1,M,L3 in f[:4]: print(" L1=",[str(v) for v in L1]," M=",[str(v) for v in M]," L3=",[str(v) for v in L3])
elif sys.argv[1]=="x2x2l2":
    t=lambda p:(p[0]^p[1])+2*(p[2]^p[3])
    f,c=search(4,t,[0,1,2,3],R=range(-4,5))
    print("xor2+xor2(lam=2) found:",len(f))
    for L1,M,L3 in f[:4]: print(" L1=",[str(v) for v in L1]," M=",[str(v) for v in M]," L3=",[str(v) for v in L3])
elif sys.argv[1]=="x3x2":
    # 5 vars: xor3(a,b,c) + 4*xor2(d,e)
    t=lambda p:(p[0]^p[1]^p[2])+4*(p[3]^p[4])
    f,c=search(5,t,[0,1,4,5],R=range(-3,4))
    print("xor3+xor2 found:",len(f))
    for L1,M,L3 in f[:4]: print(" L1=",[str(v) for v in L1]," M=",[str(v) for v in M]," L3=",[str(v) for v in L3])
