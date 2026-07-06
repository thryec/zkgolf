# Keccak theta as GF(2) linear map. Output(x,y,z) = in(x,y,z) XOR (XOR_y' in(x-1,y',z)) XOR (XOR_y' in(x+1,y',z-1))
# Each output = XOR of 11 input bits. Count XOR-gates (=witnesses) to realize all 1600 outputs,
# with common-subexpression sharing. Compare to current 2240 (640 C-intermediates + 1600 outputs).
def idx(x,y,z): return (x%5)*5*64 + (y%5)*64 + (z%64)
outputs = {}   # output index -> frozenset of input indices (GF2 support)
for x in range(5):
  for y in range(5):
    for z in range(64):
      s = set()
      def tog(i):
        if i in s: s.discard(i)
        else: s.add(i)
      tog(idx(x,y,z))
      for yp in range(5): tog(idx(x-1,yp,z))
      for yp in range(5): tog(idx(x+1,yp,z-1))
      outputs[idx(x,y,z)] = frozenset(s)

# sanity: each output is XOR of 11 inputs
import statistics
sizes=[len(v) for v in outputs.values()]
print("outputs:",len(outputs),"support sizes:",set(sizes))

# Column parity C[x][z] = XOR_y in(x,y,z). These are the natural shared subexpressions.
# Current scheme: materialize 320 C-bits (each 5-XOR = 2 gates: t=xor3(a,b,c), C=xor3(t,d,e)) = 640 gates,
# then each output = xor3(in, C[x-1][z], C[x+1][z-1]) = 1 gate. Total 640+1600 = 2240.
# Lower bound check: the 1600 outputs MUST be materialized (feed chi) = 1600 forced gates.
# Question: can the shared linear part (the C's) be built in < 640 gates?
# C-bits: 5*64 = 320 distinct column parities, each a 5-input XOR over DISJOINT inputs (different lanes).
# Disjoint 5-XORs share NO input bits across different C -> no cross-C common subexpression possible.
# Within one 5-XOR: min gates to reduce 5 inputs to 1 boolean output with xor2/xor3 gates,
# where every intermediate must be materialized (re-linearized): xor3(a,b,c)->t, xor3(t,d,e)->C = 2 gates. 1 is impossible (degree 5 in one row).
# Verify disjointness: do any two C-supports share an input?
Csupp = {}
for x in range(5):
  for z in range(64):
    Csupp[(x,z)] = frozenset(idx(x,y,z) for y in range(5))
allpairs_share = False
items=list(Csupp.items())
seen={}
for (k,supp) in items:
  for i in supp:
    if i in seen: allpairs_share=True
    seen[i]=k
print("any input shared between two different C-parities:", allpairs_share)
print("=> C-parities are input-disjoint; no cross-column XOR sharing exists.")
print()
print("Forced outputs (feed chi):        1600 gates")
print("C column-parities: 320 x (5-XOR, 2 gates min each, input-disjoint): 640 gates")
print("Theta layer minimum:              2240 gates  == current")
print("Round = 640(C) + 1600(theta-out) + 1600(chi) = 3840 ; x24 x2 = 184320")
