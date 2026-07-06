from fractions import Fraction as Fr
from itertools import product
# chi bit: z = a XOR ((NOT b) AND c). Search single R1CS row (z+L1)*M = L3, M!=0 on cube (like Maj/Xor3).
def chi(a,b,c): return a ^ ((1-b)&c)
cube=list(product((0,1),repeat=3))
def aff(co,p): return co[0]+co[1]*p[0]+co[2]*p[1]+co[3]*p[2]
def mob(fv):
    c={}
    for S in cube:
        s=Fr(0)
        for T in cube:
            if all(t<=sv for t,sv in zip(T,S)): s+=(-1)**(sum(S)-sum(T))*fv[T]
        c[S]=s
    return c
found=[]
for M in product(range(-5,6),repeat=4):
    if 2*M[0]+M[1]+M[2]+M[3]==0 or True:  # abc-kill condition depends on fn; just solve generally
        vm=[aff(M,p) for p in cube]
        if any(v==0 for v in vm): continue
        # solve L1 (4 unknowns) s.t. nonlinear coeffs of (chi+L1)*M vanish (4 conditions incl abc)
        base=mob({p: Fr(chi(*p))*aff(M,p) for p in cube})
        mons=[mob({p: Fr(1 if j==0 else p[j-1])*aff(M,p) for p in cube}) for j in range(4)]
        NL=[(1,1,0),(1,0,1),(0,1,1),(1,1,1)]
        rows=[[mons[j][S] for j in range(4)]+[-base[S]] for S in NL]
        m,n=4,4; MM=[r[:] for r in rows]; piv=[]; r=0
        for c_ in range(n):
            pr=next((rr for rr in range(r,m) if MM[rr][c_]!=0),None)
            if pr is None: continue
            MM[r],MM[pr]=MM[pr],MM[r]; MM[r]=[v/MM[r][c_] for v in MM[r]]
            for rr in range(m):
                if rr!=r and MM[rr][c_]!=0:
                    f=MM[rr][c_]; MM[rr]=[a-f*b for a,b in zip(MM[rr],MM[r])]
            piv.append(c_); r+=1
        if any(all(MM[rr][c_]==0 for c_ in range(n)) and MM[rr][n]!=0 for rr in range(m)): continue
        x=[Fr(0)]*4
        for i,c_ in enumerate(piv): x[c_]=MM[i][n]
        L1=tuple(x)
        fv={p:(Fr(chi(*p))+aff(L1,p))*aff(M,p) for p in cube}
        cf=mob(fv)
        if any(cf[S]!=0 for S in NL): continue
        L3=(cf[(0,0,0)],cf[(1,0,0)],cf[(0,1,0)],cf[(0,0,1)])
        ok=all(((Fr(z)+aff(L1,p))*aff(M,p)==aff(L3,p))==(z==chi(*p)) for p in cube for z in (0,1))
        if ok: found.append((L1,M,L3))
print("chi single-row identities found:",len(found))
for L1,M,L3 in found[:4]:
    print(" L1=",[str(v) for v in L1]," M=",M," L3=",[str(v) for v in L3])
