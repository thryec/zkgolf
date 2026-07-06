# zkgolf

Optimized, formally verified Lean 4 circuits for the [zk.golf](https://zk.golf) challenges.

| challenge | baseline | ours | reduction |
|---|---|---|---|
| Keccak-f[1600] | 307,200 | **184,320** | 40% |
| SHA-256 | 413,810 | **152,070** | 63% |
| RSA-4096 PKCS#1 v1.5 | 827,136 | **327,754** | 60% |

Score = allocations + constraints, proven by `mainCost`. Each circuit proves `soundness`,
`completeness`, `mainCost`, and `isR1CS` with no `sorry` and only the permitted axioms; all scores
verified by the zk.golf server. Bit-decomposed arithmetic, one R1CS row per constraint, no lookups.
Built on [Clean](https://github.com/Verified-zkEVM/clean).

---

## Layout

```
solutions/{sha256,keccak-f1600,rsa-4096}/   the circuits
scripts/                                     identity-search and floor-analysis (Python)
```

---

## Running

Needs [elan](https://github.com/leanprover/elan) (Lean 4.28.0 is pinned by the harness).

Clone the [challenge harness](https://github.com/zksecurity/zk-golf-challenges), drop a solution
into its matching instance directory, and build:

```bash
git clone https://github.com/zksecurity/zk-golf-challenges && cd zk-golf-challenges
cp /path/to/zkgolf/solutions/sha256/*.lean Solution/SHA256/
lake build Solution.SHA256.Main Solution.SHA256.Cost
```

Instance directories: `sha256 → SHA256`, `keccak-f1600 → KeccakF1600`,
`rsa-4096 → RSASSAPKCS1v15_SHA256_4096_65537`.

`Main.lean` holds the proven `allocations` and `constraints`. A clean build (no `sorry`, axioms
limited to the config's `permitted_axioms`) is what the zk.golf server checks; RSA and the packed
SHA round take a few minutes.

---

## Keccak-f[1600] — 307,200 → 184,320

**Single-row χ.** Pins `z = a ⊕ (¬b ∧ c)` in one row, halving χ from two (AND + XOR). Found by search.

```
(z + 3a − b − c) · (4a + b + c − 3) = 4a + 2b
```

**θ D-fold.** Folds the D layer into the state update as one 3-input XOR.

```
state′ = state ⊕ C[x−1] ⊕ rot(C[x+1])
```

**Single-row 3-input XOR** for the column parities.

θ costs 2,240 gates/round — the 320 column-parities are input-disjoint, so no sharing — and
lane-packing can't touch 3-variable functions.

---

## SHA-256 — 413,810 → 152,070

**Single-row Maj.** Pins `z = Maj(a,b,c)` in one row. Found by search.

```
(4z − a − b − c) · (2(a+b+c) − 3) = a + b + c
```

**Base-λ cross-round packing.** Superimpose two rounds' Ch/Maj into one witness column at weights
1 and 2^40, split by a fused two-round adder. Optimal at depth 2; depth 3 hits a rank-3 triangle.

```
z = ch(eₜ, fₜ, gₜ) + 2⁴⁰ · ch(eₜ₊₁, fₜ₊₁, gₜ₊₁)
```

**Fused multi-operand adders** collapse the round's add chain; carry-free `add32`.

**Affine block-5 schedule** — the last padding block is a one-hot function of the length.

**Davies-Meyer round-63 fold**, wide schedule pruning, and block-1 H0 constant folding.

---

## RSA-4096 PKCS#1 v1.5 — 827,136 → 327,754

**Balanced signed-digit residues.** Limbs centered on 0, halving the convolution coefficient
magnitudes in `s^65537 mod n`.

**Graduated grouped-carry equality** with lazy reduction — one carry per group, tent-shaped widths.
Group size is field-capped at 9 (`g=10` overflows `p`).

---

## Attribution

The single-row Maj and χ identities and the floor-analysis scripts are original. Other techniques
adopt the published [zk.golf](https://zk.golf) leaderboards and
[Verified-zkEVM/clean](https://github.com/Verified-zkEVM/clean/pull/395), re-implemented and
re-proven here.
