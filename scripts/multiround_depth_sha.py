from fractions import Fraction as Fr
from itertools import product
import sympy as sp
# 3-round packed ch target with SHA register-shift sharing:
# ch_t=ch(s,x,y), ch_{t1}=ch(u1,s,x), ch_{t2}=ch(u2,u1,s). chBit(e,f,g)=g+e*(f-g).
lam=sp.Symbol('lam')
def ch(e,f,g): return g+e*(f-g)
vars5=sp.symbols('s x y u1 u2')
s,x,y,u1,u2=vars5
target=ch(s,x,y)+lam*ch(u1,s,x)+lam**2*ch(u2,u1,s)
# Question: exists ONE R1CS row A*B + C = 0, A,B,C affine in (s,x,y,u1,u2) with coeffs in Z[lam],
# z linear in C with UNIT coeff, pinning z=target for all boolean inputs?
# Equivalent: exists affine A,B (one product) and affine C' with  A*B + C' == k*target  as a polynomial
# that agrees on the boolean cube (s..u2 in {0,1}), for some unit k.  I.e. is  k*target - (affine)  a single product on the cube?
# Test: the QUADRATIC part of target (mod booleans, i.e. its multilinear deg-2 form) must be realizable as
# off-diagonal of S=a*bT+b*aT (rank<=2) with free diagonal.  Build S_target (5x5 symmetric off-diag) and check
# min rank over diagonal choices == whether <=2 achievable.  We just check: is there rank<=2 sym matrix M with
# M offdiag == target offdiag?  (diagonal free).
tgt=sp.expand(target)
names=[s,x,y,u1,u2]
S={}
for i in range(5):
  for j in range(i+1,5):
    c=tgt.coeff(names[i]*names[j])
    if c!=0: S[(i,j)]=c
print("target off-diagonal cross-terms (i<j):")
for k2,v in S.items(): print("  ",names[k2[0]],names[k2[1]],"=",v)
# Necessary condition for one product A*B (rank-2 S with free diag): every 3x3 principal minor of the
# off-diagonal-completed matrix... instead use: a graph whose edges are S is realizable as offdiag(rank<=2 + diag)
# iff we can pick diagonal d_i making full 5x5 matrix rank<=2. Search symbolically is hard with lam; instead
# use the cycle/tree criterion: rank-2 S=a bT+b aT => S_ij*S_kl relations (2x2 minors of the bordered form).
# Simplest rigorous check: for a single product, for ANY 4 indices, the 'quadrilateral' relation
#   S_ik*S_jl == S_il*S_jk  must hold when the diagonal is free? No—diagonal matters. 
# Do a concrete numeric test at lam=2^40 over the boolean cube: brute search small-integer A,B,C.
LAM=2**40
def affval(co,pt): return co[0]+sum(co[i+1]*pt[i] for i in range(5))
cube=list(product((0,1),repeat=5))
def tgtnum(pt):
    s_,x_,y_,u1_,u2_=pt
    def chb(e,f,g): return g+e*(f-g)
    return chb(s_,x_,y_)+LAM*chb(u1_,s_,x_)+LAM*LAM*chb(u2_,u1_,s_)
# brute A,B coeffs in {-4..4} but scaled by {1,LAM,LAM^2}; too big. Instead: check the rank-2 necessary condition
# via the 2x2 minor identities on the off-diagonal 'quadrilaterals' that don't involve the diagonal:
# For distinct i,j,k,l: S_ij*S_kl , S_ik*S_jl, S_il*S_jk  — for rank<=2 sym+diag, the three must satisfy
# one equals sum/relation... Actually the clean invariant: a symmetric matrix has rank<=2 iff all 3x3 minors=0.
# With free diagonal we can zero the 3 diagonal-containing minors; the ONE all-off-diagonal 3x3 minor of any
# triple (i,j,k) = 2*S_ij*S_ik*S_jk (for 3x3 [[0,a,b],[a,0,c],[b,c,0]] det = 2abc). rank<=2 needs each such =0.
import itertools
bad=[]
for tri in itertools.combinations(range(5),3):
  i,j,k=tri
  a=S.get((i,j),0); b=S.get((i,k),0); c=S.get((j,k),0)
  if a!=0 and b!=0 and c!=0:
    bad.append((names[i],names[j],names[k]))
print()
print("triangles with all 3 edges nonzero (force a rank-3 off-diag block => NOT one product):")
for t in bad: print("   ",t)
print("=> one-row 3-round ch packing possible:", len(bad)==0)
