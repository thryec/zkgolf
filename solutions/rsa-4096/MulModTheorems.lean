import Solution.RSASSAPKCS1v15_SHA256_4096_65537.Theorems
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.NormalizeTight

/-!
# `MulMod` — bridge lemmas and arithmetic cores

The pure arithmetic content underpinning the `MulMod` gadget, factored out of the
gadget file so that the `soundness`/`completeness` proofs only have to wire these
lemmas together. Built on the shared foundation in `Theorems`.
-/

namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537
open Specs.RSA

/-! ## `MulMod`: bridge lemmas and arithmetic cores -/

namespace MulMod

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

/-! ## Pure math helpers for soundness/completeness

These lemmas isolate the arithmetic content of `MulMod` so that the
`soundness`/`completeness` proofs only have to wire them together. -/

omit [NeZero m] in
/-- `value B (map (eval env) x) = ∑ k, (eval env x[k]).val * 2^(B*k)`. -/
lemma value_map_eval {B : ℕ} (env : Environment (F p)) (x : Var (BigInt m) (F p)) :
    BigInt.value B (Vector.map (Expression.eval env) x)
      = ∑ k : Fin m, (Expression.eval env x[k.val]).val * 2 ^ (B * k.val) := by
  rw [BigInt.value_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.getElem_fin, Vector.getElem_map]

/-- **Bridge 1 (multiply side).** Base-`2^B` value of the schoolbook convolution
of `a`, `b` equals the product of the two operands' values. -/
lemma polyValue_mul_eq {B : ℕ} (env : Environment (F p))
    (a b : Var (BigInt m) (F p))
    (ha : ∀ i : Fin m, (Expression.eval env a[i.val]).val < 2 ^ B)
    (hb : ∀ i : Fin m, (Expression.eval env b[i.val]).val < 2 ^ B)
    (hfield : m * (2 ^ B * 2 ^ B) < p) :
    polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce a b))
      = BigInt.value B (Vector.map (Expression.eval env) a)
        * BigInt.value B (Vector.map (Expression.eval env) b) := by
  rw [polyValue_bigIntMulNoReduce env a b ha hb hfield, value_map_eval, value_map_eval]

/-- **Bridge 2 (sum side, convolution part).** Base-`2^B` value of `bigIntMulNoReduce q n`
equals `q.value * n.value`. -/
lemma polyValue_Sqn_eq {B : ℕ} (env : Environment (F p))
    (q n : Var (BigInt m) (F p))
    (hq : ∀ i : Fin m, (Expression.eval env q[i.val]).val < 2 ^ B)
    (hn : ∀ i : Fin m, (Expression.eval env n[i.val]).val < 2 ^ B)
    (hfield : m * (2 ^ B * 2 ^ B) < p) :
    polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce q n))
      = BigInt.value B (Vector.map (Expression.eval env) q)
        * BigInt.value B (Vector.map (Expression.eval env) n) :=
  polyValue_mul_eq env q n hq hn hfield

/-- The natural-number `MulMod` correctness step: `a·b = q·n + r` and `r < n`
imply `r = (a·b) % n`. -/
lemma remainder_eq {a b q n r : ℕ} (heq : a * b = q * n + r) (hr : r < n) :
    r = a * b % n := by
  rw [heq, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]

/-- The `S` coefficient vector used by `MulMod`: `Sqn[k] + r[k]` in the low `m`
limbs, `Sqn[k]` above, where `Sqn = bigIntMulNoReduce q n` and the limbs of `r`
are read from variables at offset `off`. -/
def sVec (q n : Var (BigInt m) (F p)) (off : ℕ) :
    Vector (Expression (F p)) (2 * m - 1) :=
  Vector.mapFinRange (2 * m - 1) fun k =>
    if h : k.val < m then (bigIntMulNoReduce q n)[k.val] + var { index := off + k.val }
    else (bigIntMulNoReduce q n)[k.val]

/-- **Bridge 2 (sum side, limb-add part).** Splitting `S = Sqn + r` (low limbs):
`polyValue S = polyValue Sqn + r.value`, provided each low coefficient does not
wrap mod `p`. -/
lemma polyValue_sVec_split {B : ℕ} (env : Environment (F p))
    (q n : Var (BigInt m) (F p)) (off : ℕ)
    (hnowrap : ∀ k : Fin (2 * m - 1), k.val < m →
      (Expression.eval env ((bigIntMulNoReduce q n)[k.val])).val
        + (Expression.eval env (var (F := F p) { index := off + k.val })).val < p) :
    polyValue B (Vector.map (Expression.eval env) (sVec q n off))
      = polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce q n))
        + BigInt.value B (Vector.map (Expression.eval env)
            (Vector.mapRange m fun i => var (F := F p) { index := off + i })) := by
  rw [polyValue, polyValue, value_map_eval]
  -- per-index value of S
  have hS : ∀ k : Fin (2 * m - 1),
      (Vector.map (Expression.eval env) (sVec q n off))[k.val].val
        = (Expression.eval env ((bigIntMulNoReduce q n)[k.val])).val
          + (if h : k.val < m then (Expression.eval env (var (F := F p) { index := off + k.val })).val else 0) := by
    intro k
    rw [Vector.getElem_map]
    simp only [sVec, Vector.getElem_mapFinRange]
    by_cases hk : k.val < m
    · simp only [dif_pos hk]
      rw [show Expression.eval env ((bigIntMulNoReduce q n)[k.val] + var { index := off + k.val })
            = Expression.eval env ((bigIntMulNoReduce q n)[k.val])
              + Expression.eval env (var (F := F p) { index := off + k.val }) from rfl,
        ZMod.val_add_of_lt (hnowrap k hk)]
    · simp only [dif_neg hk, Nat.add_zero]
  -- rewrite LHS sum
  simp only [hS]
  -- distribute (Sqn + r-part) * 2^(Bk)
  rw [show (∑ k : Fin (2 * m - 1),
        ((Expression.eval env ((bigIntMulNoReduce q n)[k.val])).val
          + (if h : k.val < m then (Expression.eval env (var (F := F p) { index := off + k.val })).val else 0))
          * 2 ^ (B * k.val))
      = (∑ k : Fin (2 * m - 1),
          (Expression.eval env ((bigIntMulNoReduce q n)[k.val])).val * 2 ^ (B * k.val))
        + (∑ k : Fin (2 * m - 1),
          (if h : k.val < m then (Expression.eval env (var (F := F p) { index := off + k.val })).val else 0)
            * 2 ^ (B * k.val)) from by
    rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro k _; ring]
  congr 1
  · -- Sqn part = polyValue Sqn
    apply Finset.sum_congr rfl; intro k _; rw [Vector.getElem_map]
  · -- r part = value r
    -- RHS: simplify the mapRange index to `env.get (off + k)`
    have hRHS : (∑ k : Fin m, (Expression.eval env (Vector.mapRange m
          fun i => var (F := F p) { index := off + i })[k.val]).val * 2 ^ (B * k.val))
        = ∑ k ∈ Finset.range m,
            (Expression.eval env (var (F := F p) { index := off + k })).val * 2 ^ (B * k) := by
      rw [← Fin.sum_univ_eq_sum_range (fun k => (Expression.eval env (var (F := F p) { index := off + k })).val * 2 ^ (B * k))]
      apply Finset.sum_congr rfl
      intro k _
      congr 2
      simp [circuit_norm]
    rw [hRHS]
    -- LHS: guarded sum over Fin (2m-1) collapses to range m (terms k≥m are 0)
    simp only [dite_eq_ite]
    rw [Fin.sum_univ_eq_sum_range (fun k =>
      (if k < m then (Expression.eval env (var (F := F p) { index := off + k })).val else 0) * 2 ^ (B * k))]
    have hext : (∑ k ∈ Finset.range (2 * m - 1),
          (if k < m then (Expression.eval env (var (F := F p) { index := off + k })).val else 0)
            * 2 ^ (B * k))
        = ∑ k ∈ Finset.range m,
          (Expression.eval env (var (F := F p) { index := off + k })).val * 2 ^ (B * k) := by
      rw [← Finset.sum_subset (Finset.range_subset_range.mpr (by have := Nat.pos_of_neZero m; omega : m ≤ 2 * m - 1))
        (f := fun k => (if k < m then (Expression.eval env (var (F := F p) { index := off + k })).val else 0) * 2 ^ (B * k))]
      · apply Finset.sum_congr rfl; intro k hk
        rw [Finset.mem_range] at hk; rw [if_pos hk]
      · intro k _ hk
        rw [Finset.mem_range] at hk; rw [if_neg hk, Nat.zero_mul]
    rw [hext]

/-- **Coefficient bound for `P = bigIntMulNoReduce a b`**: each coefficient is
`< (m+1)·2^(2B)`, the size assumption required by `EqViaCarries`. -/
lemma coeff_P_bound {B : ℕ} (env : Environment (F p))
    (a b : Var (BigInt m) (F p)) (k : Fin (2 * m - 1))
    (ha : ∀ i : Fin m, (Expression.eval env a[i.val]).val < 2 ^ B)
    (hb : ∀ i : Fin m, (Expression.eval env b[i.val]).val < 2 ^ B)
    (hfield : m * (2 ^ B * 2 ^ B) < p) :
    (Expression.eval env ((bigIntMulNoReduce a b)[k.val])).val < (m + 1) * 2 ^ (2 * B) := by
  have h := val_bigIntMulNoReduce_coeff_lt env a b k ha hb hfield
  have : m * 2 ^ (2 * B) ≤ (m + 1) * 2 ^ (2 * B) := by
    apply Nat.mul_le_mul_right; omega
  omega

/-- **Coefficient bound for `S = sVec q n off`**: each coefficient is
`< (m+1)·2^(2B)`, the size assumption required by `EqViaCarries`. -/
lemma coeff_S_bound {B : ℕ} (env : Environment (F p))
    (q n : Var (BigInt m) (F p)) (off : ℕ) (k : Fin (2 * m - 1))
    (hq : ∀ i : Fin m, (Expression.eval env q[i.val]).val < 2 ^ B)
    (hn : ∀ i : Fin m, (Expression.eval env n[i.val]).val < 2 ^ B)
    (hr : ∀ j : ℕ, j < m → (Expression.eval env (var (F := F p) { index := off + j })).val < 2 ^ B)
    (hfield : m * (2 ^ B * 2 ^ B) < p) :
    (Expression.eval env ((sVec q n off)[k.val])).val < (m + 1) * 2 ^ (2 * B) := by
  have hSqn := val_bigIntMulNoReduce_coeff_lt env q n k hq hn hfield
  have hpow : (2 : ℕ) ^ B ≤ 2 ^ (2 * B) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hmm : (m + 1) * 2 ^ (2 * B) = m * 2 ^ (2 * B) + 2 ^ (2 * B) := by ring
  rw [hmm]
  generalize hX : 2 ^ (2 * B) = X at *
  generalize hY : m * X = Y at *
  simp only [sVec, Vector.getElem_mapFinRange]
  by_cases hk : k.val < m
  · rw [dif_pos hk]
    have hr' := hr k.val hk
    have hadd : (Expression.eval env ((bigIntMulNoReduce q n)[k.val])
        + Expression.eval env (var (F := F p) { index := off + k.val })).val
        ≤ (Expression.eval env ((bigIntMulNoReduce q n)[k.val])).val
          + (Expression.eval env (var (F := F p) { index := off + k.val })).val := ZMod.val_add_le _ _
    rw [show Expression.eval env ((bigIntMulNoReduce q n)[k.val] + var { index := off + k.val })
          = Expression.eval env ((bigIntMulNoReduce q n)[k.val])
            + Expression.eval env (var (F := F p) { index := off + k.val }) from rfl]
    omega
  · rw [dif_neg hk]
    omega

/-- **Witnessed-product bridge.** From the per-product asserts
`a[t/m]·b[t%m] = env.get (off + t)` (`t : Fin (m·m)`) — exactly the form produced
by `witnessedMul`'s `forEach assertZero` after `circuit_norm` — the affine
coefficient vector `bigIntMulVars (mapRange (m·m) (var ∘ (off + ·)))` evaluates to
the same vector as the inline schoolbook convolution `bigIntMulNoReduce a b`. -/
lemma witnessedMul_map_eval (env : Environment (F p)) (off : ℕ)
    (a b : Var (BigInt m) (F p))
    (hprod : ∀ t : Fin (m * m),
      Expression.eval env (a[t.val / m]'(Nat.div_lt_of_lt_mul t.isLt))
          * Expression.eval env (b[t.val % m]'(Nat.mod_lt _ (Nat.pos_of_neZero m)))
        = env.get (off + t.val)) :
    Vector.map (Expression.eval env)
        (bigIntMulVars (Vector.mapRange (m * m) fun i => var (F := F p) { index := off + i }))
      = Vector.map (Expression.eval env) (bigIntMulNoReduce a b) := by
  apply map_eval_bigIntMulVars_eq env a b
  intro i j
  -- the product variable at index i*m+j reads env.get (off + (i*m+j))
  have hidx : (Vector.mapRange (m * m) fun i => var (F := F p) { index := off + i })[i.val * m + j.val]'(by
        have := i.isLt; have := j.isLt
        calc i.val * m + j.val < i.val * m + m := by omega
          _ = (i.val + 1) * m := by ring
          _ ≤ m * m := by apply Nat.mul_le_mul_right; omega)
      = var (F := F p) { index := off + (i.val * m + j.val) } := by
    simp [circuit_norm]
  rw [hidx]
  -- the product assert at t = i*m+j
  have ht : (i.val * m + j.val) < m * m := by
    have := i.isLt; have := j.isLt
    calc i.val * m + j.val < i.val * m + m := by omega
      _ = (i.val + 1) * m := by ring
      _ ≤ m * m := by apply Nat.mul_le_mul_right; omega
  have hd : (i.val * m + j.val) / m = i.val := by
    rw [Nat.mul_comm, Nat.mul_add_div (Nat.pos_of_neZero m), Nat.div_eq_of_lt j.isLt, Nat.add_zero]
  have hr : (i.val * m + j.val) % m = j.val := by
    rw [Nat.mul_comm, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt j.isLt
  have := hprod ⟨i.val * m + j.val, ht⟩
  simp only [hd, hr] at this
  rw [show Expression.eval env (var (F := F p) { index := off + (i.val * m + j.val) })
        = env.get (off + (i.val * m + j.val)) from rfl, ← this]

omit [NeZero m] in
/-- **`EqViaCarries` implication bridge.** If two coefficient vectors `Pv`/`Pn`
(and `Qv`/`Qn`) evaluate identically, then the `EqViaCarries` implication phrased
with the witnessed-product vectors `Pv`,`Qv` transfers to the one phrased with the
schoolbook vectors `Pn`,`Qn`. Used to feed `mulMod_soundness_core` (stated against
`bigIntMulNoReduce`) from the witnessed-product circuit. -/
lemma eqImpl_bridge {B rOff : ℕ} (env : Environment (F p))
    (Pv Pn Qv Qn : Vector (Expression (F p)) (2 * m - 1))
    (hP_get : ∀ k : Fin (2 * m - 1), Expression.eval env Pv[k.val] = Expression.eval env Pn[k.val])
    (hQ_get : ∀ k : Fin (2 * m - 1), Expression.eval env Qv[k.val] = Expression.eval env Qn[k.val])
    (himpl :
      ((∀ k : Fin (2 * m - 1), (Expression.eval env Pv[k.val]).val < (m + 1) * 2 ^ (2 * B)) ∧
        ∀ k : Fin (2 * m - 1),
          (Expression.eval env (if h : k.val < m then Qv[k.val] + var { index := rOff + k.val }
            else Qv[k.val])).val < (m + 1) * 2 ^ (2 * B)) →
        polyValue B (Vector.map (Expression.eval env) Pv) =
          polyValue B (Vector.map (Expression.eval env)
            (Vector.mapFinRange (2 * m - 1) fun k =>
              if h : k.val < m then Qv[k.val] + var { index := rOff + k.val } else Qv[k.val]))) :
    ((∀ k : Fin (2 * m - 1), (Expression.eval env Pn[k.val]).val < (m + 1) * 2 ^ (2 * B)) ∧
      ∀ k : Fin (2 * m - 1),
        (Expression.eval env (if h : k.val < m then Qn[k.val] + var { index := rOff + k.val }
          else Qn[k.val])).val < (m + 1) * 2 ^ (2 * B)) →
      polyValue B (Vector.map (Expression.eval env) Pn) =
        polyValue B (Vector.map (Expression.eval env)
          (Vector.mapFinRange (2 * m - 1) fun k =>
            if h : k.val < m then Qn[k.val] + var { index := rOff + k.val } else Qn[k.val])) := by
  -- per-index eval equality of the two `S` dite vectors
  have hS_get : ∀ k : Fin (2 * m - 1),
      Expression.eval env (if h : k.val < m then Qv[k.val] + var (F := F p) { index := rOff + k.val } else Qv[k.val])
        = Expression.eval env (if h : k.val < m then Qn[k.val] + var (F := F p) { index := rOff + k.val } else Qn[k.val]) := by
    intro k
    by_cases hk : k.val < m
    · simp only [dif_pos hk]
      show Expression.eval env Qv[k.val] + Expression.eval env (var (F := F p) { index := rOff + k.val })
        = Expression.eval env Qn[k.val] + Expression.eval env (var (F := F p) { index := rOff + k.val })
      rw [hQ_get k]
    · simp only [dif_neg hk]; exact hQ_get k
  -- the two `S` vectors map-eval equally
  have hSvec : Vector.map (Expression.eval env)
        (Vector.mapFinRange (2 * m - 1) fun k =>
          if h : k.val < m then Qv[k.val] + var (F := F p) { index := rOff + k.val } else Qv[k.val])
      = Vector.map (Expression.eval env)
        (Vector.mapFinRange (2 * m - 1) fun k =>
          if h : k.val < m then Qn[k.val] + var (F := F p) { index := rOff + k.val } else Qn[k.val]) := by
    apply Vector.ext; intro k hk
    rw [Vector.getElem_map, Vector.getElem_map, Vector.getElem_mapFinRange, Vector.getElem_mapFinRange]
    exact hS_get ⟨k, hk⟩
  have hPvec : Vector.map (Expression.eval env) Pv = Vector.map (Expression.eval env) Pn := by
    apply Vector.ext; intro k hk; rw [Vector.getElem_map, Vector.getElem_map]; exact hP_get ⟨k, hk⟩
  intro hbounds
  rw [← hPvec, ← hSvec]
  apply himpl
  refine ⟨fun k => ?_, fun k => ?_⟩
  · rw [hP_get k]; exact hbounds.1 k
  · rw [hS_get k]; exact hbounds.2 k

omit [NeZero m] in
/-- **`EqViaCarries` conjunction bridge** (completeness direction). If `Pv`/`Pn`
and `Qv`/`Qn` evaluate identically, the proven `EqViaCarries` conjunction (bounds
∧ bounds ∧ `polyValue` equality) over the schoolbook vectors `Pn`,`Qn` transfers to
the conjunction over the witnessed-product vectors `Pv`,`Qv`. -/
lemma eqConj_bridge {B rOff : ℕ} (env : Environment (F p))
    (Pv Pn Qv Qn : Vector (Expression (F p)) (2 * m - 1))
    (hP_get : ∀ k : Fin (2 * m - 1), Expression.eval env Pv[k.val] = Expression.eval env Pn[k.val])
    (hQ_get : ∀ k : Fin (2 * m - 1), Expression.eval env Qv[k.val] = Expression.eval env Qn[k.val])
    (hconj :
      ((∀ k : Fin (2 * m - 1), (Expression.eval env Pn[k.val]).val < (m + 1) * 2 ^ (2 * B)) ∧
        (∀ k : Fin (2 * m - 1),
          (Expression.eval env (if h : k.val < m then Qn[k.val] + var { index := rOff + k.val }
            else Qn[k.val])).val < (m + 1) * 2 ^ (2 * B))) ∧
        polyValue B (Vector.map (Expression.eval env) Pn) =
          polyValue B (Vector.map (Expression.eval env)
            (Vector.mapFinRange (2 * m - 1) fun k =>
              if h : k.val < m then Qn[k.val] + var { index := rOff + k.val } else Qn[k.val]))) :
    ((∀ k : Fin (2 * m - 1), (Expression.eval env Pv[k.val]).val < (m + 1) * 2 ^ (2 * B)) ∧
      (∀ k : Fin (2 * m - 1),
        (Expression.eval env (if h : k.val < m then Qv[k.val] + var { index := rOff + k.val }
          else Qv[k.val])).val < (m + 1) * 2 ^ (2 * B))) ∧
        polyValue B (Vector.map (Expression.eval env) Pv) =
          polyValue B (Vector.map (Expression.eval env)
            (Vector.mapFinRange (2 * m - 1) fun k =>
              if h : k.val < m then Qv[k.val] + var { index := rOff + k.val } else Qv[k.val])) := by
  have hS_get : ∀ k : Fin (2 * m - 1),
      Expression.eval env (if h : k.val < m then Qv[k.val] + var (F := F p) { index := rOff + k.val } else Qv[k.val])
        = Expression.eval env (if h : k.val < m then Qn[k.val] + var (F := F p) { index := rOff + k.val } else Qn[k.val]) := by
    intro k
    by_cases hk : k.val < m
    · simp only [dif_pos hk]
      show Expression.eval env Qv[k.val] + Expression.eval env (var (F := F p) { index := rOff + k.val })
        = Expression.eval env Qn[k.val] + Expression.eval env (var (F := F p) { index := rOff + k.val })
      rw [hQ_get k]
    · simp only [dif_neg hk]; exact hQ_get k
  have hPvec : Vector.map (Expression.eval env) Pv = Vector.map (Expression.eval env) Pn := by
    apply Vector.ext; intro k hk; rw [Vector.getElem_map, Vector.getElem_map]; exact hP_get ⟨k, hk⟩
  have hSvec : Vector.map (Expression.eval env)
        (Vector.mapFinRange (2 * m - 1) fun k =>
          if h : k.val < m then Qv[k.val] + var (F := F p) { index := rOff + k.val } else Qv[k.val])
      = Vector.map (Expression.eval env)
        (Vector.mapFinRange (2 * m - 1) fun k =>
          if h : k.val < m then Qn[k.val] + var (F := F p) { index := rOff + k.val } else Qn[k.val]) := by
    apply Vector.ext; intro k hk
    rw [Vector.getElem_map, Vector.getElem_map, Vector.getElem_mapFinRange, Vector.getElem_mapFinRange]
    exact hS_get ⟨k, hk⟩
  refine ⟨⟨fun k => ?_, fun k => ?_⟩, ?_⟩
  · rw [hP_get k]; exact hconj.1.1 k
  · rw [hS_get k]; exact hconj.1.2 k
  · rw [hPvec, hSvec]; exact hconj.2

/-- The arithmetic core of `MulMod` soundness, isolated into its own declaration
(and hence its own heartbeat budget): given the per-subcircuit facts from
`EqViaCarries` and `LessThan`, plus the normalization assumptions,
the witnessed remainder is normalized and denotes `(a·b) % n`. -/
lemma mulMod_soundness_core {B : ℕ} (hp : 2 ^ (2 * B) * (m + 1) * 4 < p)
    (i₀ : ℕ) (env : Environment (F p))
    (input_var : ProvablePair (BigInt m) (ProvablePair (BigInt m) (BigInt m)) (Expression (F p)))
    (input : ProvablePair (BigInt m) (ProvablePair (BigInt m) (BigInt m)) (F p))
    (h_input : (Vector.map (Expression.eval env) input_var.1,
        Vector.map (Expression.eval env) input_var.2.1,
        Vector.map (Expression.eval env) input_var.2.2) = input)
    (ha_norm : BigInt.Normalized B input.1) (hb_norm : BigInt.Normalized B input.2.1)
    (hn_norm : BigInt.Normalized B input.2.2)
    (hq_norm : BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + i })))
    (hr_norm : BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })))
    (h_eq_impl :
      ((∀ k : Fin (2 * m - 1),
          (Expression.eval env (bigIntMulNoReduce input_var.1 input_var.2.1)[k.val]).val
            < (m + 1) * 2 ^ (2 * B)) ∧
        ∀ k : Fin (2 * m - 1),
          (Expression.eval env
            (if h : k.val < m then
              (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val] +
                var { index := i₀ + m + k.val }
            else (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val])).val
            < (m + 1) * 2 ^ (2 * B)) →
        polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce input_var.1 input_var.2.1)) =
          polyValue B
            (Vector.map (Expression.eval env)
              (Vector.mapFinRange (2 * m - 1) fun k ↦
                if h : k.val < m then
                  (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val] +
                    var { index := i₀ + m + k.val }
                else (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val])))
    (h_lt_impl :
      BigInt.Normalized B (Vector.map (Expression.eval env)
          (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) ∧
        BigInt.Normalized B (Vector.map (Expression.eval env) input_var.2.2) →
        BigInt.value B (Vector.map (Expression.eval env)
            (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) <
          BigInt.value B (Vector.map (Expression.eval env) input_var.2.2)) :
    BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) ∧
      BigInt.value B (Vector.map (Expression.eval env)
          (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) =
        BigInt.value B input.1 * BigInt.value B input.2.1 % BigInt.value B input.2.2 := by
  -- abbreviations
  set qVar := (Vector.mapRange m fun i ↦ var (F := F p) { index := i₀ + i }) with hqVar
  set rVar := (Vector.mapRange m fun i ↦ var (F := F p) { index := i₀ + m + i }) with hrVar
  set qv := (Vector.map (Expression.eval env) qVar : BigInt m (F p)) with hqv
  set rv := (Vector.map (Expression.eval env) rVar : BigInt m (F p)) with hrv
  -- digit bounds (each input/witness limb < 2^B)
  have ha_lt : ∀ i : Fin m, (Expression.eval env input_var.1[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env input_var.1[i.val] = input.1[i.val] from by
      rw [← h_input]; simp only [Vector.getElem_map]]; exact ha_norm i
  have hb_lt : ∀ i : Fin m, (Expression.eval env input_var.2.1[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env input_var.2.1[i.val] = input.2.1[i.val] from by
      rw [← h_input]; simp only [Vector.getElem_map]]; exact hb_norm i
  have hn_lt : ∀ i : Fin m, (Expression.eval env input_var.2.2[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env input_var.2.2[i.val] = input.2.2[i.val] from by
      rw [← h_input]; simp only [Vector.getElem_map]]; exact hn_norm i
  have hqd_lt : ∀ i : Fin m, (Expression.eval env qVar[i.val]).val < 2 ^ B := by
    intro i; have := hq_norm i; rwa [hqv, Fin.getElem_fin, Vector.getElem_map] at this
  have hrd_lt : ∀ j : ℕ, j < m → (Expression.eval env (var (F := F p) { index := i₀ + m + j })).val < 2 ^ B := by
    intro j hj; have := hr_norm ⟨j, hj⟩
    rwa [hrv, Fin.getElem_fin, Vector.getElem_map, hrVar,
      show (Vector.mapRange m fun i ↦ var (F := F p) { index := i₀ + m + i })[j]
        = var (F := F p) { index := i₀ + m + j } from by simp [circuit_norm]] at this
  -- field-overflow bound for Cauchy
  have hfield : m * (2 ^ B * 2 ^ B) < p := by
    have h1 : m * (2 ^ B * 2 ^ B) = m * 2 ^ (2 * B) := by rw [two_mul, pow_add]
    rw [h1]
    have h2 : m * 2 ^ (2 * B) ≤ 2 ^ (2 * B) * (m + 1) * 4 := by nlinarith [Nat.two_pow_pos (2 * B)]
    omega
  -- the `S` vector in the goal is exactly `sVec qVar input_var.2.2 (i₀ + m)`
  have hS_eq : (Vector.mapFinRange (2 * m - 1) fun k ↦
        if h : k.val < m then (bigIntMulNoReduce qVar input_var.2.2)[k.val] + var { index := i₀ + m + k.val }
        else (bigIntMulNoReduce qVar input_var.2.2)[k.val])
      = sVec qVar input_var.2.2 (i₀ + m) := by
    rfl
  -- discharge EqViaCarries assumptions, get polyValue P = polyValue S
  have h_polyeq := h_eq_impl ⟨fun k => coeff_P_bound env input_var.1 input_var.2.1 k ha_lt hb_lt hfield,
    fun k => by
      have hb := coeff_S_bound env qVar input_var.2.2 (i₀ + m) k hqd_lt hn_lt hrd_lt hfield
      rw [sVec, Vector.getElem_mapFinRange] at hb
      exact hb⟩
  rw [hS_eq] at h_polyeq
  -- Cauchy: polyValue P = a.value * b.value
  have hP : polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce input_var.1 input_var.2.1))
      = BigInt.value B input.1 * BigInt.value B input.2.1 := by
    rw [polyValue_mul_eq env input_var.1 input_var.2.1 ha_lt hb_lt hfield, ← h_input]
  -- split S: polyValue S = polyValue Sqn + r.value
  have hSplit := polyValue_sVec_split (B := B) env qVar input_var.2.2 (i₀ + m)
    (fun k hk => by
      have h1 := val_bigIntMulNoReduce_coeff_lt env qVar input_var.2.2 k hqd_lt hn_lt hfield
      have h2 := hrd_lt k.val hk
      have hpow : (2 : ℕ) ^ B ≤ 2 ^ (2 * B) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h3 : m * 2 ^ (2 * B) + 2 ^ (2 * B) ≤ 2 ^ (2 * B) * (m + 1) * 4 := by nlinarith [Nat.two_pow_pos (2 * B)]
      omega)
  -- polyValue Sqn = q.value * n.value
  have hSqn : polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce qVar input_var.2.2))
      = BigInt.value B qv * BigInt.value B input.2.2 := by
    rw [polyValue_Sqn_eq env qVar input_var.2.2 hqd_lt hn_lt hfield, ← h_input]
  -- r.value of the rVar vector is rv
  have hrval : BigInt.value B (Vector.map (Expression.eval env)
      (Vector.mapRange m fun i => var (F := F p) { index := i₀ + m + i })) = BigInt.value B rv := by
    rw [hrv, hrVar]
  -- combine: a.value * b.value = q.value * n.value + r.value
  rw [hP] at h_polyeq
  rw [hSplit, hSqn, hrval] at h_polyeq
  -- r.value < n.value from LessThan
  have hn_eq : BigInt.value B (Vector.map (Expression.eval env) input_var.2.2) = BigInt.value B input.2.2 := by
    rw [← h_input]
  have hn_norm' : BigInt.Normalized B (Vector.map (Expression.eval env) input_var.2.2) := by
    rw [show (Vector.map (Expression.eval env) input_var.2.2) = input.2.2 from by rw [← h_input]]
    exact hn_norm
  have hr_lt_n : BigInt.value B rv < BigInt.value B input.2.2 := by
    have := h_lt_impl ⟨hr_norm, hn_norm'⟩
    rwa [hn_eq] at this
  -- conclude
  refine ⟨hr_norm, ?_⟩
  exact remainder_eq h_polyeq hr_lt_n

/-- **Witnessed-product soundness core.** Same conclusion as `mulMod_soundness_core`,
but consuming the `EqViaCarries` implication phrased over *abstract* coefficient
vectors `Pv`,`Qv` (instantiated by the gadget with the `witnessedMul` outputs)
together with the per-element eval bridges `Pv[k] = (a·b)[k]`, `Qv[k] = (q·n)[k]`.
This avoids any rewriting inside the (huge) `EqViaCarries` implication at the call
site; the bridges are discharged on small per-`k` goals. Isolated into its own
declaration for a fresh heartbeat budget. -/
lemma mulMod_soundness_core_wm {B : ℕ} (hp : 2 ^ (2 * B) * (m + 1) * 4 < p)
    (i₀ : ℕ) (env : Environment (F p))
    (a b n : Var (BigInt m) (F p))
    (Pv Qv : Vector (Expression (F p)) (2 * m - 1))
    (input : ProvablePair (BigInt m) (ProvablePair (BigInt m) (BigInt m)) (F p))
    (h_input : (Vector.map (Expression.eval env) a,
        Vector.map (Expression.eval env) b,
        Vector.map (Expression.eval env) n) = input)
    (ha_norm : BigInt.Normalized B input.1) (hb_norm : BigInt.Normalized B input.2.1)
    (hn_norm : BigInt.Normalized B input.2.2)
    (hq_norm : BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + i })))
    (hr_norm : BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })))
    (heqAB_get : ∀ k : Fin (2 * m - 1),
      Expression.eval env Pv[k.val] = Expression.eval env (bigIntMulNoReduce a b)[k.val])
    (heqQN_get : ∀ k : Fin (2 * m - 1),
      Expression.eval env Qv[k.val]
        = Expression.eval env (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)[k.val])
    (h_eq_impl :
      ((∀ k : Fin (2 * m - 1), (Expression.eval env Pv[k.val]).val < (m + 1) * 2 ^ (2 * B)) ∧
        ∀ k : Fin (2 * m - 1),
          (Expression.eval env
            (if h : k.val < m then Qv[k.val] + var { index := i₀ + m + k.val } else Qv[k.val])).val
            < (m + 1) * 2 ^ (2 * B)) →
        polyValue B (Vector.map (Expression.eval env) Pv) =
          polyValue B (Vector.map (Expression.eval env)
            (Vector.mapFinRange (2 * m - 1) fun k ↦
              if h : k.val < m then Qv[k.val] + var { index := i₀ + m + k.val } else Qv[k.val])))
    (h_lt_impl :
      BigInt.Normalized B (Vector.map (Expression.eval env)
          (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) ∧
        BigInt.Normalized B (Vector.map (Expression.eval env) n) →
        BigInt.value B (Vector.map (Expression.eval env)
            (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) <
          BigInt.value B (Vector.map (Expression.eval env) n)) :
    BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) ∧
      BigInt.value B (Vector.map (Expression.eval env)
          (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) =
        BigInt.value B input.1 * BigInt.value B input.2.1 % BigInt.value B input.2.2 := by
  -- convert the implication to the schoolbook form via the eval bridges
  have h_eq_impl' := eqImpl_bridge (rOff := i₀ + m) env Pv (bigIntMulNoReduce a b)
    Qv (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)
    heqAB_get heqQN_get h_eq_impl
  -- assemble the schoolbook triple and feed the schoolbook core
  exact mulMod_soundness_core (B := B) hp i₀ env (a, b, n) input h_input
    ha_norm hb_norm hn_norm hq_norm hr_norm h_eq_impl' h_lt_impl

/-- **Lazy soundness core.** Like `mulMod_soundness_core`, but *without* the `r < n`
(`LessThan`) hypothesis: from `a·b = q·n + r` alone we conclude only the
*congruence* `r ≡ a·b (mod n)`, which is all that propagates through the
square-and-multiply chain (the final octet-string comparison pins canonicity). -/
lemma mulMod_soundness_core_lazy {B : ℕ} (hp : 2 ^ (2 * B) * (m + 1) * 4 < p)
    (i₀ : ℕ) (env : Environment (F p))
    (input_var : ProvablePair (BigInt m) (ProvablePair (BigInt m) (BigInt m)) (Expression (F p)))
    (input : ProvablePair (BigInt m) (ProvablePair (BigInt m) (BigInt m)) (F p))
    (h_input : (Vector.map (Expression.eval env) input_var.1,
        Vector.map (Expression.eval env) input_var.2.1,
        Vector.map (Expression.eval env) input_var.2.2) = input)
    (ha_norm : BigInt.Normalized B input.1) (hb_norm : BigInt.Normalized B input.2.1)
    (hn_norm : BigInt.Normalized B input.2.2)
    (hq_norm : BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + i })))
    (hr_norm : BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })))
    (h_eq_impl :
      ((∀ k : Fin (2 * m - 1),
          (Expression.eval env (bigIntMulNoReduce input_var.1 input_var.2.1)[k.val]).val
            < (m + 1) * 2 ^ (2 * B)) ∧
        ∀ k : Fin (2 * m - 1),
          (Expression.eval env
            (if h : k.val < m then
              (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val] +
                var { index := i₀ + m + k.val }
            else (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val])).val
            < (m + 1) * 2 ^ (2 * B)) →
        polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce input_var.1 input_var.2.1)) =
          polyValue B
            (Vector.map (Expression.eval env)
              (Vector.mapFinRange (2 * m - 1) fun k ↦
                if h : k.val < m then
                  (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val] +
                    var { index := i₀ + m + k.val }
                else (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val]))) :
    BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) ∧
      BigInt.value B (Vector.map (Expression.eval env)
          (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) % BigInt.value B input.2.2 =
        BigInt.value B input.1 * BigInt.value B input.2.1 % BigInt.value B input.2.2 := by
  set qVar := (Vector.mapRange m fun i ↦ var (F := F p) { index := i₀ + i }) with hqVar
  set rVar := (Vector.mapRange m fun i ↦ var (F := F p) { index := i₀ + m + i }) with hrVar
  set qv := (Vector.map (Expression.eval env) qVar : BigInt m (F p)) with hqv
  set rv := (Vector.map (Expression.eval env) rVar : BigInt m (F p)) with hrv
  have ha_lt : ∀ i : Fin m, (Expression.eval env input_var.1[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env input_var.1[i.val] = input.1[i.val] from by
      rw [← h_input]; simp only [Vector.getElem_map]]; exact ha_norm i
  have hb_lt : ∀ i : Fin m, (Expression.eval env input_var.2.1[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env input_var.2.1[i.val] = input.2.1[i.val] from by
      rw [← h_input]; simp only [Vector.getElem_map]]; exact hb_norm i
  have hn_lt : ∀ i : Fin m, (Expression.eval env input_var.2.2[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env input_var.2.2[i.val] = input.2.2[i.val] from by
      rw [← h_input]; simp only [Vector.getElem_map]]; exact hn_norm i
  have hqd_lt : ∀ i : Fin m, (Expression.eval env qVar[i.val]).val < 2 ^ B := by
    intro i; have := hq_norm i; rwa [hqv, Fin.getElem_fin, Vector.getElem_map] at this
  have hrd_lt : ∀ j : ℕ, j < m → (Expression.eval env (var (F := F p) { index := i₀ + m + j })).val < 2 ^ B := by
    intro j hj; have := hr_norm ⟨j, hj⟩
    rwa [hrv, Fin.getElem_fin, Vector.getElem_map, hrVar,
      show (Vector.mapRange m fun i ↦ var (F := F p) { index := i₀ + m + i })[j]
        = var (F := F p) { index := i₀ + m + j } from by simp [circuit_norm]] at this
  have hfield : m * (2 ^ B * 2 ^ B) < p := by
    have h1 : m * (2 ^ B * 2 ^ B) = m * 2 ^ (2 * B) := by rw [two_mul, pow_add]
    rw [h1]
    have h2 : m * 2 ^ (2 * B) ≤ 2 ^ (2 * B) * (m + 1) * 4 := by nlinarith [Nat.two_pow_pos (2 * B)]
    omega
  have hS_eq : (Vector.mapFinRange (2 * m - 1) fun k ↦
        if h : k.val < m then (bigIntMulNoReduce qVar input_var.2.2)[k.val] + var { index := i₀ + m + k.val }
        else (bigIntMulNoReduce qVar input_var.2.2)[k.val])
      = sVec qVar input_var.2.2 (i₀ + m) := rfl
  have h_polyeq := h_eq_impl ⟨fun k => coeff_P_bound env input_var.1 input_var.2.1 k ha_lt hb_lt hfield,
    fun k => by
      have hb := coeff_S_bound env qVar input_var.2.2 (i₀ + m) k hqd_lt hn_lt hrd_lt hfield
      rw [sVec, Vector.getElem_mapFinRange] at hb
      exact hb⟩
  rw [hS_eq] at h_polyeq
  have hP : polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce input_var.1 input_var.2.1))
      = BigInt.value B input.1 * BigInt.value B input.2.1 := by
    rw [polyValue_mul_eq env input_var.1 input_var.2.1 ha_lt hb_lt hfield, ← h_input]
  have hSplit := polyValue_sVec_split (B := B) env qVar input_var.2.2 (i₀ + m)
    (fun k hk => by
      have h1 := val_bigIntMulNoReduce_coeff_lt env qVar input_var.2.2 k hqd_lt hn_lt hfield
      have h2 := hrd_lt k.val hk
      have hpow : (2 : ℕ) ^ B ≤ 2 ^ (2 * B) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h3 : m * 2 ^ (2 * B) + 2 ^ (2 * B) ≤ 2 ^ (2 * B) * (m + 1) * 4 := by nlinarith [Nat.two_pow_pos (2 * B)]
      omega)
  have hSqn : polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce qVar input_var.2.2))
      = BigInt.value B qv * BigInt.value B input.2.2 := by
    rw [polyValue_Sqn_eq env qVar input_var.2.2 hqd_lt hn_lt hfield, ← h_input]
  have hrval : BigInt.value B (Vector.map (Expression.eval env)
      (Vector.mapRange m fun i => var (F := F p) { index := i₀ + m + i })) = BigInt.value B rv := by
    rw [hrv, hrVar]
  rw [hP] at h_polyeq
  rw [hSplit, hSqn, hrval] at h_polyeq
  refine ⟨hr_norm, ?_⟩
  rw [hrval, h_polyeq, Nat.add_comm, Nat.add_mul_mod_self_right]

/-- Witnessed-product **lazy** soundness core: like `mulMod_soundness_core_wm` but no
`r < n` hypothesis, concluding only the congruence `r ≡ a·b (mod n)`. -/
lemma mulMod_soundness_core_wm_lazy {B : ℕ} (hp : 2 ^ (2 * B) * (m + 1) * 4 < p)
    (i₀ : ℕ) (env : Environment (F p))
    (a b n : Var (BigInt m) (F p))
    (Pv Qv : Vector (Expression (F p)) (2 * m - 1))
    (input : ProvablePair (BigInt m) (ProvablePair (BigInt m) (BigInt m)) (F p))
    (h_input : (Vector.map (Expression.eval env) a,
        Vector.map (Expression.eval env) b,
        Vector.map (Expression.eval env) n) = input)
    (ha_norm : BigInt.Normalized B input.1) (hb_norm : BigInt.Normalized B input.2.1)
    (hn_norm : BigInt.Normalized B input.2.2)
    (hq_norm : BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + i })))
    (hr_norm : BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })))
    (heqAB_get : ∀ k : Fin (2 * m - 1),
      Expression.eval env Pv[k.val] = Expression.eval env (bigIntMulNoReduce a b)[k.val])
    (heqQN_get : ∀ k : Fin (2 * m - 1),
      Expression.eval env Qv[k.val]
        = Expression.eval env (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)[k.val])
    (h_eq_impl :
      ((∀ k : Fin (2 * m - 1), (Expression.eval env Pv[k.val]).val < (m + 1) * 2 ^ (2 * B)) ∧
        ∀ k : Fin (2 * m - 1),
          (Expression.eval env
            (if h : k.val < m then Qv[k.val] + var { index := i₀ + m + k.val } else Qv[k.val])).val
            < (m + 1) * 2 ^ (2 * B)) →
        polyValue B (Vector.map (Expression.eval env) Pv) =
          polyValue B (Vector.map (Expression.eval env)
            (Vector.mapFinRange (2 * m - 1) fun k ↦
              if h : k.val < m then Qv[k.val] + var { index := i₀ + m + k.val } else Qv[k.val]))) :
    BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) ∧
      BigInt.value B (Vector.map (Expression.eval env)
          (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) % BigInt.value B input.2.2 =
        BigInt.value B input.1 * BigInt.value B input.2.1 % BigInt.value B input.2.2 := by
  have h_eq_impl' := eqImpl_bridge (rOff := i₀ + m) env Pv (bigIntMulNoReduce a b)
    Qv (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)
    heqAB_get heqQN_get h_eq_impl
  exact mulMod_soundness_core_lazy (B := B) hp i₀ env (a, b, n) input h_input
    ha_norm hb_norm hn_norm hq_norm hr_norm h_eq_impl'

omit [NeZero m] in
/-- Witnessed limbs `(N / 2^(B·k) % 2^B : F p)` are `B`-bit, hence normalized. -/
lemma normalized_mapRange {B : ℕ} (off N : ℕ) (env : Environment (F p))
    (hB : 2 ^ B < p)
    (hwit : ∀ i : Fin m, env.get (off + i.val) = ((N / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p)) :
    BigInt.Normalized B (Vector.map (Expression.eval env)
      (Vector.mapRange m fun i => var (F := F p) { index := off + i })) := by
  intro i
  have hget : (Vector.map (Expression.eval env)
      (Vector.mapRange m fun j => var (F := F p) { index := off + j }))[i.val] = env.get (off + i.val) := by
    simp [circuit_norm]
  rw [Fin.getElem_fin, hget, hwit i, ZMod.val_natCast_of_lt
    (lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos B)) (le_of_lt hB))]
  exact Nat.mod_lt _ (Nat.two_pow_pos B)

/-- The arithmetic core of `MulMod` completeness, isolated for its own heartbeat
budget. Given the witness values (`q = ⌊a·b/n⌋`, `r = a·b % n` decomposed into
limbs) it produces all per-subcircuit obligations. -/
lemma mulMod_completeness_core {B : ℕ} (hB : 2 ^ B < p)
    (hp : 2 ^ (2 * B) * (m + 1) * 4 < p)
    (i₀ : ℕ) (env : Environment (F p))
    (input_var : ProvablePair (BigInt m) (ProvablePair (BigInt m) (BigInt m)) (Expression (F p)))
    (input : ProvablePair (BigInt m) (ProvablePair (BigInt m) (BigInt m)) (F p))
    (h_input : (Vector.map (Expression.eval env) input_var.1,
        Vector.map (Expression.eval env) input_var.2.1,
        Vector.map (Expression.eval env) input_var.2.2) = input)
    (ha_norm : BigInt.Normalized B input.1) (hb_norm : BigInt.Normalized B input.2.1)
    (hn_norm : BigInt.Normalized B input.2.2)
    (hab_lt : BigInt.value B input.1 < BigInt.value B input.2.2)
    (hbb_lt : BigInt.value B input.2.1 < BigInt.value B input.2.2)
    (hn_pos : 0 < BigInt.value B input.2.2)
    (hqwit : ∀ i : Fin m, env.get (i₀ + i.val)
      = ((BigInt.value B input.1 * BigInt.value B input.2.1 / BigInt.value B input.2.2
          / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p))
    (hrwit : ∀ i : Fin m, env.get (i₀ + m + i.val)
      = ((BigInt.value B input.1 * BigInt.value B input.2.1 % BigInt.value B input.2.2
          / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p)) :
    BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + i })) ∧
      BigInt.Normalized B (Vector.map (Expression.eval env)
          (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) ∧
        (((∀ k : Fin (2 * m - 1),
                (Expression.eval env (bigIntMulNoReduce input_var.1 input_var.2.1)[k.val]).val
                  < (m + 1) * 2 ^ (2 * B)) ∧
              ∀ k : Fin (2 * m - 1),
                (Expression.eval env
                  (if h : k.val < m then
                    (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val] +
                      var { index := i₀ + m + k.val }
                  else (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val])).val
                  < (m + 1) * 2 ^ (2 * B)) ∧
            polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce input_var.1 input_var.2.1)) =
              polyValue B
                (Vector.map (Expression.eval env)
                  (Vector.mapFinRange (2 * m - 1) fun k ↦
                    if h : k.val < m then
                      (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val] +
                        var { index := i₀ + m + k.val }
                    else (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val]))) ∧
          (BigInt.Normalized B (Vector.map (Expression.eval env)
                (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) ∧
              BigInt.Normalized B (Vector.map (Expression.eval env) input_var.2.2)) ∧
            BigInt.value B (Vector.map (Expression.eval env)
                (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) <
              BigInt.value B (Vector.map (Expression.eval env) input_var.2.2) := by
  -- abbreviations for the two witness values
  set a := BigInt.value B input.1 with ha_def
  set b := BigInt.value B input.2.1 with hb_def
  set n := BigInt.value B input.2.2 with hn_def
  set qval := a * b / n with hqval_def
  set rval := a * b % n with hrval_def
  -- the witness-evaluated inputs are the input components
  have hmap_a : BigInt.value B (Vector.map (Expression.eval env) input_var.1) = a := by
    rw [ha_def, ← h_input]
  have hmap_b : BigInt.value B (Vector.map (Expression.eval env) input_var.2.1) = b := by
    rw [hb_def, ← h_input]
  have hmap_n : BigInt.value B (Vector.map (Expression.eval env) input_var.2.2) = n := by
    rw [hn_def, ← h_input]
  have hmap_n_norm : BigInt.Normalized B (Vector.map (Expression.eval env) input_var.2.2) := by
    rw [show (Vector.map (Expression.eval env) input_var.2.2) = input.2.2 from by rw [← h_input]]
    exact hn_norm
  -- n is positive and bounded by 2^(B*m)
  have hn_lt : n < 2 ^ (B * m) := BigInt.value_lt hn_norm
  -- q = a*b/n < n  (since a < n, b < n ⇒ a*b < n*n)
  have hq_lt_n : qval < n := by
    rw [hqval_def]
    apply Nat.div_lt_of_lt_mul
    have hab : a * b < n * n := by
      rcases Nat.eq_zero_or_pos b with hb0 | hb0
      · rw [hb0, Nat.mul_zero]; exact Nat.mul_pos hn_pos hn_pos
      · calc a * b < n * b := by
              apply (Nat.mul_lt_mul_right hb0).mpr hab_lt
          _ ≤ n * n := by apply Nat.mul_le_mul_left; omega
    omega
  have hqval_lt : qval < 2 ^ (B * m) := lt_trans hq_lt_n hn_lt
  have hrval_lt : rval < 2 ^ (B * m) := lt_trans (Nat.mod_lt _ hn_pos) hn_lt
  -- values of the witness vectors
  have hqv_val : BigInt.value B (Vector.map (Expression.eval env)
      (Vector.mapRange m fun i ↦ var { index := i₀ + i })) = qval :=
    BigInt.value_mapRange i₀ qval env hB hqval_lt (by intro i; rw [hqwit i])
  have hrv_val : BigInt.value B (Vector.map (Expression.eval env)
      (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) = rval :=
    BigInt.value_mapRange (i₀ + m) rval env hB hrval_lt (by intro i; rw [hrwit i])
  -- normalizations of the witness vectors
  have hqv_norm : BigInt.Normalized B (Vector.map (Expression.eval env)
      (Vector.mapRange m fun i ↦ var { index := i₀ + i })) :=
    normalized_mapRange i₀ qval env hB (by intro i; rw [hqwit i])
  have hrv_norm : BigInt.Normalized B (Vector.map (Expression.eval env)
      (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) :=
    normalized_mapRange (i₀ + m) rval env hB (by intro i; rw [hrwit i])
  -- digit bounds (for Cauchy / coefficient bounds)
  have ha_lt : ∀ i : Fin m, (Expression.eval env input_var.1[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env input_var.1[i.val] = input.1[i.val] from by
      rw [← h_input]; simp only [Vector.getElem_map]]; exact ha_norm i
  have hb_lt : ∀ i : Fin m, (Expression.eval env input_var.2.1[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env input_var.2.1[i.val] = input.2.1[i.val] from by
      rw [← h_input]; simp only [Vector.getElem_map]]; exact hb_norm i
  have hn_lt' : ∀ i : Fin m, (Expression.eval env input_var.2.2[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env input_var.2.2[i.val] = input.2.2[i.val] from by
      rw [← h_input]; simp only [Vector.getElem_map]]; exact hn_norm i
  have hqd_lt : ∀ i : Fin m, (Expression.eval env (Vector.mapRange m fun j ↦ var (F := F p) { index := i₀ + j })[i.val]).val < 2 ^ B := by
    intro i; have := hqv_norm i; rwa [Fin.getElem_fin, Vector.getElem_map] at this
  have hrd_lt : ∀ j : ℕ, j < m → (Expression.eval env (var (F := F p) { index := i₀ + m + j })).val < 2 ^ B := by
    intro j hj; have := hrv_norm ⟨j, hj⟩
    rwa [Fin.getElem_fin, Vector.getElem_map,
      show (Vector.mapRange m fun i ↦ var (F := F p) { index := i₀ + m + i })[j]
        = var (F := F p) { index := i₀ + m + j } from by simp [circuit_norm]] at this
  -- field-overflow bound for Cauchy
  have hfield : m * (2 ^ B * 2 ^ B) < p := by
    have h1 : m * (2 ^ B * 2 ^ B) = m * 2 ^ (2 * B) := by rw [two_mul, pow_add]
    rw [h1]
    have h2 : m * 2 ^ (2 * B) ≤ 2 ^ (2 * B) * (m + 1) * 4 := by nlinarith [Nat.two_pow_pos (2 * B)]
    omega
  -- the `S` vector is exactly `sVec qVar input_var.2.2 (i₀ + m)`
  have hS_eq : (Vector.mapFinRange (2 * m - 1) fun k ↦
        if h : k.val < m then (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val]
          + var { index := i₀ + m + k.val }
        else (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val])
      = sVec (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2 (i₀ + m) := rfl
  -- polyValue P = a * b
  have hP : polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce input_var.1 input_var.2.1))
      = a * b := by
    rw [polyValue_mul_eq env input_var.1 input_var.2.1 ha_lt hb_lt hfield, hmap_a, hmap_b]
  -- polyValue S = qval * n + rval = a * b
  have hSplit := polyValue_sVec_split (B := B) env (Vector.mapRange m fun i ↦ var { index := i₀ + i })
    input_var.2.2 (i₀ + m)
    (fun k hk => by
      have h1 := val_bigIntMulNoReduce_coeff_lt env (Vector.mapRange m fun i ↦ var { index := i₀ + i })
        input_var.2.2 k hqd_lt hn_lt' hfield
      have h2 := hrd_lt k.val hk
      have hpow : (2 : ℕ) ^ B ≤ 2 ^ (2 * B) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h3 : m * 2 ^ (2 * B) + 2 ^ (2 * B) ≤ 2 ^ (2 * B) * (m + 1) * 4 := by nlinarith [Nat.two_pow_pos (2 * B)]
      omega)
  have hSqn : polyValue B (Vector.map (Expression.eval env)
      (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2))
      = qval * n := by
    rw [polyValue_Sqn_eq env (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2 hqd_lt hn_lt' hfield,
      hqv_val, hmap_n]
  have hpolyS : polyValue B (Vector.map (Expression.eval env)
      (Vector.mapFinRange (2 * m - 1) fun k ↦
        if h : k.val < m then (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val]
          + var { index := i₀ + m + k.val }
        else (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val]))
      = a * b := by
    rw [hS_eq, hSplit, hSqn, hrv_val, hqval_def, hrval_def, Nat.div_add_mod']
  -- assemble
  refine ⟨hqv_norm, hrv_norm, ⟨⟨?_, ?_⟩, ?_⟩, ⟨hrv_norm, ?_⟩, ?_⟩
  · intro k; exact coeff_P_bound env input_var.1 input_var.2.1 k ha_lt hb_lt hfield
  · intro k
    have hb := coeff_S_bound env (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2 (i₀ + m) k
      hqd_lt hn_lt' hrd_lt hfield
    rw [sVec, Vector.getElem_mapFinRange] at hb
    exact hb
  · rw [hP, hpolyS]
  · exact hmap_n_norm
  · rw [hrv_val, hmap_n, hrval_def]
    exact Nat.mod_lt _ hn_pos

/-- **Witnessed-product completeness core.** Produces the per-subcircuit
completeness obligations (normalized `q`,`r`; the `EqViaCarries` conjunction phrased
over the *abstract* witnessed-product vectors `Pv`,`Qv`; the `LessThan` part), given
the witness values and the eval bridges `Pv[k] = (a·b)[k]`, `Qv[k] = (q·n)[k]`.
Bridges via `eqConj_bridge` to `mulMod_completeness_core`. Own heartbeat budget. -/
lemma mulMod_completeness_core_wm {B : ℕ} (hB : 2 ^ B < p)
    (hp : 2 ^ (2 * B) * (m + 1) * 4 < p)
    (i₀ : ℕ) (env : Environment (F p))
    (a b n : Var (BigInt m) (F p))
    (Pv Qv : Vector (Expression (F p)) (2 * m - 1))
    (input : ProvablePair (BigInt m) (ProvablePair (BigInt m) (BigInt m)) (F p))
    (h_input : (Vector.map (Expression.eval env) a,
        Vector.map (Expression.eval env) b,
        Vector.map (Expression.eval env) n) = input)
    (ha_norm : BigInt.Normalized B input.1) (hb_norm : BigInt.Normalized B input.2.1)
    (hn_norm : BigInt.Normalized B input.2.2)
    (hab_lt : BigInt.value B input.1 < BigInt.value B input.2.2)
    (hbb_lt : BigInt.value B input.2.1 < BigInt.value B input.2.2)
    (hn_pos : 0 < BigInt.value B input.2.2)
    (hqwit : ∀ i : Fin m, env.get (i₀ + i.val)
      = ((BigInt.value B input.1 * BigInt.value B input.2.1 / BigInt.value B input.2.2
          / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p))
    (hrwit : ∀ i : Fin m, env.get (i₀ + m + i.val)
      = ((BigInt.value B input.1 * BigInt.value B input.2.1 % BigInt.value B input.2.2
          / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p))
    (heqAB_get : ∀ k : Fin (2 * m - 1),
      Expression.eval env Pv[k.val] = Expression.eval env (bigIntMulNoReduce a b)[k.val])
    (heqQN_get : ∀ k : Fin (2 * m - 1),
      Expression.eval env Qv[k.val]
        = Expression.eval env (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)[k.val]) :
    BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + i })) ∧
      BigInt.Normalized B (Vector.map (Expression.eval env)
          (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) ∧
        (((∀ k : Fin (2 * m - 1), (Expression.eval env Pv[k.val]).val < (m + 1) * 2 ^ (2 * B)) ∧
            (∀ k : Fin (2 * m - 1),
              (Expression.eval env
                (if h : k.val < m then Qv[k.val] + var { index := i₀ + m + k.val } else Qv[k.val])).val
                < (m + 1) * 2 ^ (2 * B))) ∧
            polyValue B (Vector.map (Expression.eval env) Pv) =
              polyValue B (Vector.map (Expression.eval env)
                (Vector.mapFinRange (2 * m - 1) fun k ↦
                  if h : k.val < m then Qv[k.val] + var { index := i₀ + m + k.val } else Qv[k.val]))) ∧
          (BigInt.Normalized B (Vector.map (Expression.eval env)
                (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) ∧
              BigInt.Normalized B (Vector.map (Expression.eval env) n)) ∧
            BigInt.value B (Vector.map (Expression.eval env)
                (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) <
              BigInt.value B (Vector.map (Expression.eval env) n) := by
  obtain ⟨hqn, hrn, hconj, hlt⟩ :=
    mulMod_completeness_core (B := B) hB hp i₀ env (a, b, n) input h_input
      ha_norm hb_norm hn_norm hab_lt hbb_lt hn_pos hqwit hrwit
  exact ⟨hqn, hrn,
    eqConj_bridge (rOff := i₀ + m) env Pv (bigIntMulNoReduce a b) Qv
      (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)
      heqAB_get heqQN_get hconj, hlt⟩

set_option maxHeartbeats 800000 in
/-- **Lazy completeness core.** Like `mulMod_completeness_core`, but with relaxed
input bounds (`a,b,n < 2^((m-1)·B+tb)`) and a quotient-fit hypothesis
(`2^(2·T) ≤ n·2^(B·m)`, `T = (m-1)·B+tb`, guaranteeing the honest quotient fits `m`
limbs). Produces the `Normalize q` / `NormalizeTight r` / `EqViaCarries` obligations
(no `LessThan`), with the `r` obligation being `NormalizedTight` (top limb `< 2^tb`,
which follows from `r = a·b % n < n < 2^T`). -/
lemma mulMod_completeness_core_lazy {B tb : ℕ} (hB : 2 ^ B < p) (htbB : tb ≤ B)
    (hp : 2 ^ (2 * B) * (m + 1) * 4 < p)
    (i₀ : ℕ) (env : Environment (F p))
    (input_var : ProvablePair (BigInt m) (ProvablePair (BigInt m) (BigInt m)) (Expression (F p)))
    (input : ProvablePair (BigInt m) (ProvablePair (BigInt m) (BigInt m)) (F p))
    (h_input : (Vector.map (Expression.eval env) input_var.1,
        Vector.map (Expression.eval env) input_var.2.1,
        Vector.map (Expression.eval env) input_var.2.2) = input)
    (ha_norm : BigInt.Normalized B input.1) (hb_norm : BigInt.Normalized B input.2.1)
    (hn_norm : BigInt.Normalized B input.2.2)
    (hab_ltT : BigInt.value B input.1 < 2 ^ ((m - 1) * B + tb))
    (hbb_ltT : BigInt.value B input.2.1 < 2 ^ ((m - 1) * B + tb))
    (hn_ltT : BigInt.value B input.2.2 < 2 ^ ((m - 1) * B + tb))
    (hn_pos : 0 < BigInt.value B input.2.2)
    (hn_big : 2 ^ (2 * ((m - 1) * B + tb)) ≤ BigInt.value B input.2.2 * 2 ^ (B * m))
    (hqwit : ∀ i : Fin m, env.get (i₀ + i.val)
      = ((BigInt.value B input.1 * BigInt.value B input.2.1 / BigInt.value B input.2.2
          / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p))
    (hrwit : ∀ i : Fin m, env.get (i₀ + m + i.val)
      = ((BigInt.value B input.1 * BigInt.value B input.2.1 % BigInt.value B input.2.2
          / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p)) :
    BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + i })) ∧
      BigInt.NormalizedTight B tb (Vector.map (Expression.eval env)
          (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) ∧
        ((∀ k : Fin (2 * m - 1),
                (Expression.eval env (bigIntMulNoReduce input_var.1 input_var.2.1)[k.val]).val
                  < (m + 1) * 2 ^ (2 * B)) ∧
              ∀ k : Fin (2 * m - 1),
                (Expression.eval env
                  (if h : k.val < m then
                    (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val] +
                      var { index := i₀ + m + k.val }
                  else (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val])).val
                  < (m + 1) * 2 ^ (2 * B)) ∧
            polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce input_var.1 input_var.2.1)) =
              polyValue B
                (Vector.map (Expression.eval env)
                  (Vector.mapFinRange (2 * m - 1) fun k ↦
                    if h : k.val < m then
                      (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val] +
                        var { index := i₀ + m + k.val }
                    else (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val])) := by
  set a := BigInt.value B input.1 with ha_def
  set b := BigInt.value B input.2.1 with hb_def
  set n := BigInt.value B input.2.2 with hn_def
  set qval := a * b / n with hqval_def
  set rval := a * b % n with hrval_def
  have hmap_a : BigInt.value B (Vector.map (Expression.eval env) input_var.1) = a := by
    rw [ha_def, ← h_input]
  have hmap_b : BigInt.value B (Vector.map (Expression.eval env) input_var.2.1) = b := by
    rw [hb_def, ← h_input]
  have hmap_n : BigInt.value B (Vector.map (Expression.eval env) input_var.2.2) = n := by
    rw [hn_def, ← h_input]
  -- honest quotient fits `m` limbs
  have hab_prod : a * b < 2 ^ (2 * ((m - 1) * B + tb)) := by
    have hTT : (2 : ℕ) ^ (2 * ((m - 1) * B + tb)) = 2 ^ ((m - 1) * B + tb) * 2 ^ ((m - 1) * B + tb) := by
      rw [← pow_add, two_mul]
    rw [hTT]
    exact Nat.mul_lt_mul_of_lt_of_le hab_ltT hbb_ltT.le (Nat.two_pow_pos _)
  have hqval_lt : qval < 2 ^ (B * m) := by
    rw [hqval_def]
    exact Nat.div_lt_of_lt_mul (lt_of_lt_of_le hab_prod hn_big)
  -- honest remainder is `< n < 2^T`, so `< 2^(B*m)` and its top limb `< 2^tb`
  have hrval_ltT : rval < 2 ^ ((m - 1) * B + tb) := lt_trans (Nat.mod_lt _ hn_pos) hn_ltT
  have hTle : (m - 1) * B + tb ≤ B * m := by
    have hm := Nat.pos_of_neZero m
    calc (m - 1) * B + tb ≤ (m - 1) * B + B := by omega
      _ = m * B := by
          cases m with
          | zero => omega
          | succ k => rw [Nat.succ_sub_one]; ring
      _ = B * m := Nat.mul_comm m B
  have hrval_lt : rval < 2 ^ (B * m) :=
    lt_of_lt_of_le hrval_ltT (Nat.pow_le_pow_right (by norm_num) hTle)
  have hqv_val : BigInt.value B (Vector.map (Expression.eval env)
      (Vector.mapRange m fun i ↦ var { index := i₀ + i })) = qval :=
    BigInt.value_mapRange i₀ qval env hB hqval_lt (by intro i; rw [hqwit i])
  have hrv_val : BigInt.value B (Vector.map (Expression.eval env)
      (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) = rval :=
    BigInt.value_mapRange (i₀ + m) rval env hB hrval_lt (by intro i; rw [hrwit i])
  have hqv_norm : BigInt.Normalized B (Vector.map (Expression.eval env)
      (Vector.mapRange m fun i ↦ var { index := i₀ + i })) :=
    normalized_mapRange i₀ qval env hB (by intro i; rw [hqwit i])
  have hrv_norm : BigInt.Normalized B (Vector.map (Expression.eval env)
      (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) :=
    normalized_mapRange (i₀ + m) rval env hB (by intro i; rw [hrwit i])
  -- the tight top-limb bound for `r`
  have hm1 : m - 1 < m := by have := Nat.pos_of_neZero m; omega
  have hrtop : BigInt.NormalizedTight B tb (Vector.map (Expression.eval env)
      (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) := by
    refine ⟨hrv_norm, ?_⟩
    have hget : (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var (F := F p) { index := i₀ + m + i }))[m - 1]'(by
          have := Nat.pos_of_neZero m; omega) = env.get (i₀ + m + (m - 1)) := by
      simp [circuit_norm]
    rw [hget, hrwit ⟨m - 1, hm1⟩,
      ZMod.val_natCast_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos B)) hB.le)]
    calc rval / 2 ^ (B * (m - 1)) % 2 ^ B ≤ rval / 2 ^ (B * (m - 1)) := Nat.mod_le _ _
      _ < 2 ^ tb := by
          apply Nat.div_lt_of_lt_mul
          rw [show (2 : ℕ) ^ (B * (m - 1)) * 2 ^ tb = 2 ^ ((m - 1) * B + tb) from by
            rw [← pow_add]; congr 1; ring]
          exact hrval_ltT
  -- digit bounds
  have ha_lt : ∀ i : Fin m, (Expression.eval env input_var.1[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env input_var.1[i.val] = input.1[i.val] from by
      rw [← h_input]; simp only [Vector.getElem_map]]; exact ha_norm i
  have hb_lt : ∀ i : Fin m, (Expression.eval env input_var.2.1[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env input_var.2.1[i.val] = input.2.1[i.val] from by
      rw [← h_input]; simp only [Vector.getElem_map]]; exact hb_norm i
  have hn_lt' : ∀ i : Fin m, (Expression.eval env input_var.2.2[i.val]).val < 2 ^ B := by
    intro i; rw [show Expression.eval env input_var.2.2[i.val] = input.2.2[i.val] from by
      rw [← h_input]; simp only [Vector.getElem_map]]; exact hn_norm i
  have hqd_lt : ∀ i : Fin m, (Expression.eval env (Vector.mapRange m fun j ↦ var (F := F p) { index := i₀ + j })[i.val]).val < 2 ^ B := by
    intro i; have := hqv_norm i; rwa [Fin.getElem_fin, Vector.getElem_map] at this
  have hrd_lt : ∀ j : ℕ, j < m → (Expression.eval env (var (F := F p) { index := i₀ + m + j })).val < 2 ^ B := by
    intro j hj; have := hrv_norm ⟨j, hj⟩
    rwa [Fin.getElem_fin, Vector.getElem_map,
      show (Vector.mapRange m fun i ↦ var (F := F p) { index := i₀ + m + i })[j]
        = var (F := F p) { index := i₀ + m + j } from by simp [circuit_norm]] at this
  have hfield : m * (2 ^ B * 2 ^ B) < p := by
    have h1 : m * (2 ^ B * 2 ^ B) = m * 2 ^ (2 * B) := by rw [two_mul, pow_add]
    rw [h1]
    have h2 : m * 2 ^ (2 * B) ≤ 2 ^ (2 * B) * (m + 1) * 4 := by nlinarith [Nat.two_pow_pos (2 * B)]
    omega
  have hS_eq : (Vector.mapFinRange (2 * m - 1) fun k ↦
        if h : k.val < m then (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val]
          + var { index := i₀ + m + k.val }
        else (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val])
      = sVec (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2 (i₀ + m) := rfl
  have hP : polyValue B (Vector.map (Expression.eval env) (bigIntMulNoReduce input_var.1 input_var.2.1))
      = a * b := by
    rw [polyValue_mul_eq env input_var.1 input_var.2.1 ha_lt hb_lt hfield, hmap_a, hmap_b]
  have hSplit := polyValue_sVec_split (B := B) env (Vector.mapRange m fun i ↦ var { index := i₀ + i })
    input_var.2.2 (i₀ + m)
    (fun k hk => by
      have h1 := val_bigIntMulNoReduce_coeff_lt env (Vector.mapRange m fun i ↦ var { index := i₀ + i })
        input_var.2.2 k hqd_lt hn_lt' hfield
      have h2 := hrd_lt k.val hk
      have hpow : (2 : ℕ) ^ B ≤ 2 ^ (2 * B) := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h3 : m * 2 ^ (2 * B) + 2 ^ (2 * B) ≤ 2 ^ (2 * B) * (m + 1) * 4 := by nlinarith [Nat.two_pow_pos (2 * B)]
      omega)
  have hSqn : polyValue B (Vector.map (Expression.eval env)
      (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2))
      = qval * n := by
    rw [polyValue_Sqn_eq env (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2 hqd_lt hn_lt' hfield,
      hqv_val, hmap_n]
  have hpolyS : polyValue B (Vector.map (Expression.eval env)
      (Vector.mapFinRange (2 * m - 1) fun k ↦
        if h : k.val < m then (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val]
          + var { index := i₀ + m + k.val }
        else (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2)[k.val]))
      = a * b := by
    rw [hS_eq, hSplit, hSqn, hrv_val, hqval_def, hrval_def, Nat.div_add_mod']
  refine ⟨hqv_norm, hrtop, ⟨?_, ?_⟩, ?_⟩
  · intro k; exact coeff_P_bound env input_var.1 input_var.2.1 k ha_lt hb_lt hfield
  · intro k
    have hb := coeff_S_bound env (Vector.mapRange m fun i ↦ var { index := i₀ + i }) input_var.2.2 (i₀ + m) k
      hqd_lt hn_lt' hrd_lt hfield
    rw [sVec, Vector.getElem_mapFinRange] at hb
    exact hb
  · rw [hP, hpolyS]

/-- **Witnessed-product lazy completeness core.** Produces the per-subcircuit
completeness obligations for the lazy `MulMod` (normalized `q`; `NormalizedTight r`;
the `EqViaCarries` conjunction over the witnessed-product vectors `Pv`,`Qv`; no
`LessThan`), given the witness values and the eval bridges. Bridges via
`eqConj_bridge` to `mulMod_completeness_core_lazy`. -/
lemma mulMod_completeness_core_wm_lazy {B tb : ℕ} (hB : 2 ^ B < p) (htbB : tb ≤ B)
    (hp : 2 ^ (2 * B) * (m + 1) * 4 < p)
    (i₀ : ℕ) (env : Environment (F p))
    (a b n : Var (BigInt m) (F p))
    (Pv Qv : Vector (Expression (F p)) (2 * m - 1))
    (input : ProvablePair (BigInt m) (ProvablePair (BigInt m) (BigInt m)) (F p))
    (h_input : (Vector.map (Expression.eval env) a,
        Vector.map (Expression.eval env) b,
        Vector.map (Expression.eval env) n) = input)
    (ha_norm : BigInt.Normalized B input.1) (hb_norm : BigInt.Normalized B input.2.1)
    (hn_norm : BigInt.Normalized B input.2.2)
    (hab_ltT : BigInt.value B input.1 < 2 ^ ((m - 1) * B + tb))
    (hbb_ltT : BigInt.value B input.2.1 < 2 ^ ((m - 1) * B + tb))
    (hn_ltT : BigInt.value B input.2.2 < 2 ^ ((m - 1) * B + tb))
    (hn_pos : 0 < BigInt.value B input.2.2)
    (hn_big : 2 ^ (2 * ((m - 1) * B + tb)) ≤ BigInt.value B input.2.2 * 2 ^ (B * m))
    (hqwit : ∀ i : Fin m, env.get (i₀ + i.val)
      = ((BigInt.value B input.1 * BigInt.value B input.2.1 / BigInt.value B input.2.2
          / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p))
    (hrwit : ∀ i : Fin m, env.get (i₀ + m + i.val)
      = ((BigInt.value B input.1 * BigInt.value B input.2.1 % BigInt.value B input.2.2
          / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p))
    (heqAB_get : ∀ k : Fin (2 * m - 1),
      Expression.eval env Pv[k.val] = Expression.eval env (bigIntMulNoReduce a b)[k.val])
    (heqQN_get : ∀ k : Fin (2 * m - 1),
      Expression.eval env Qv[k.val]
        = Expression.eval env (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)[k.val]) :
    BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + i })) ∧
      BigInt.NormalizedTight B tb (Vector.map (Expression.eval env)
          (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) ∧
        ((∀ k : Fin (2 * m - 1), (Expression.eval env Pv[k.val]).val < (m + 1) * 2 ^ (2 * B)) ∧
            (∀ k : Fin (2 * m - 1),
              (Expression.eval env
                (if h : k.val < m then Qv[k.val] + var { index := i₀ + m + k.val } else Qv[k.val])).val
                < (m + 1) * 2 ^ (2 * B))) ∧
            polyValue B (Vector.map (Expression.eval env) Pv) =
              polyValue B (Vector.map (Expression.eval env)
                (Vector.mapFinRange (2 * m - 1) fun k ↦
                  if h : k.val < m then Qv[k.val] + var { index := i₀ + m + k.val } else Qv[k.val])) := by
  obtain ⟨hqn, hrn, hconj⟩ :=
    mulMod_completeness_core_lazy (B := B) (tb := tb) hB htbB hp i₀ env (a, b, n) input h_input
      ha_norm hb_norm hn_norm hab_ltT hbb_ltT hn_ltT hn_pos hn_big hqwit hrwit
  exact ⟨hqn, hrn,
    eqConj_bridge (rOff := i₀ + m) env Pv (bigIntMulNoReduce a b) Qv
      (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)
      heqAB_get heqQN_get hconj⟩

/-- **Witnessed-product lazy-input *canonical* completeness core.** Produces the
per-subcircuit completeness obligations for a canonical `MulMod` (normalized `q`;
normalized `r`; the `EqViaCarries` conjunction over `Pv`,`Qv`; **and** the `LessThan`
`r < n` obligation) but under the relaxed lazy input bounds. Reuses
`mulMod_completeness_core_lazy` and adds the `r < n` fact from `r = a·b % n < n`. -/
lemma mulMod_completeness_core_wm_lazy_canon {B tb : ℕ} (hB : 2 ^ B < p) (htbB : tb ≤ B)
    (hp : 2 ^ (2 * B) * (m + 1) * 4 < p)
    (i₀ : ℕ) (env : Environment (F p))
    (a b n : Var (BigInt m) (F p))
    (Pv Qv : Vector (Expression (F p)) (2 * m - 1))
    (input : ProvablePair (BigInt m) (ProvablePair (BigInt m) (BigInt m)) (F p))
    (h_input : (Vector.map (Expression.eval env) a,
        Vector.map (Expression.eval env) b,
        Vector.map (Expression.eval env) n) = input)
    (ha_norm : BigInt.Normalized B input.1) (hb_norm : BigInt.Normalized B input.2.1)
    (hn_norm : BigInt.Normalized B input.2.2)
    (hab_ltT : BigInt.value B input.1 < 2 ^ ((m - 1) * B + tb))
    (hbb_ltT : BigInt.value B input.2.1 < 2 ^ ((m - 1) * B + tb))
    (hn_ltT : BigInt.value B input.2.2 < 2 ^ ((m - 1) * B + tb))
    (hn_pos : 0 < BigInt.value B input.2.2)
    (hn_big : 2 ^ (2 * ((m - 1) * B + tb)) ≤ BigInt.value B input.2.2 * 2 ^ (B * m))
    (hqwit : ∀ i : Fin m, env.get (i₀ + i.val)
      = ((BigInt.value B input.1 * BigInt.value B input.2.1 / BigInt.value B input.2.2
          / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p))
    (hrwit : ∀ i : Fin m, env.get (i₀ + m + i.val)
      = ((BigInt.value B input.1 * BigInt.value B input.2.1 % BigInt.value B input.2.2
          / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p))
    (heqAB_get : ∀ k : Fin (2 * m - 1),
      Expression.eval env Pv[k.val] = Expression.eval env (bigIntMulNoReduce a b)[k.val])
    (heqQN_get : ∀ k : Fin (2 * m - 1),
      Expression.eval env Qv[k.val]
        = Expression.eval env (bigIntMulNoReduce (Vector.mapRange m fun i ↦ var { index := i₀ + i }) n)[k.val]) :
    BigInt.Normalized B (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + i })) ∧
      BigInt.Normalized B (Vector.map (Expression.eval env)
          (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) ∧
        (((∀ k : Fin (2 * m - 1), (Expression.eval env Pv[k.val]).val < (m + 1) * 2 ^ (2 * B)) ∧
            (∀ k : Fin (2 * m - 1),
              (Expression.eval env
                (if h : k.val < m then Qv[k.val] + var { index := i₀ + m + k.val } else Qv[k.val])).val
                < (m + 1) * 2 ^ (2 * B))) ∧
            polyValue B (Vector.map (Expression.eval env) Pv) =
              polyValue B (Vector.map (Expression.eval env)
                (Vector.mapFinRange (2 * m - 1) fun k ↦
                  if h : k.val < m then Qv[k.val] + var { index := i₀ + m + k.val } else Qv[k.val]))) ∧
          (BigInt.Normalized B (Vector.map (Expression.eval env)
                (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) ∧
              BigInt.Normalized B (Vector.map (Expression.eval env) n)) ∧
            BigInt.value B (Vector.map (Expression.eval env)
                (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) <
              BigInt.value B (Vector.map (Expression.eval env) n) := by
  obtain ⟨hqn, hrn, hconj⟩ :=
    mulMod_completeness_core_wm_lazy (B := B) (tb := tb) hB htbB hp i₀ env a b n Pv Qv input h_input
      ha_norm hb_norm hn_norm hab_ltT hbb_ltT hn_ltT hn_pos hn_big hqwit hrwit heqAB_get heqQN_get
  -- `Normalized n` (map-eval of the modulus input)
  have hmap_n_norm : BigInt.Normalized B (Vector.map (Expression.eval env) n) := by
    rw [show (Vector.map (Expression.eval env) n) = input.2.2 from by rw [← h_input]]
    exact hn_norm
  -- `r.value = a·b % n < n`
  have hrval_lt : BigInt.value B input.1 * BigInt.value B input.2.1 % BigInt.value B input.2.2
      < 2 ^ (B * m) :=
    lt_trans (Nat.mod_lt _ hn_pos) (BigInt.value_lt hn_norm)
  have hrv_val : BigInt.value B (Vector.map (Expression.eval env)
      (Vector.mapRange m fun i ↦ var { index := i₀ + m + i }))
      = BigInt.value B input.1 * BigInt.value B input.2.1 % BigInt.value B input.2.2 :=
    BigInt.value_mapRange (i₀ + m) _ env hB hrval_lt (by intro i; rw [hrwit i])
  have hr_lt_n : BigInt.value B (Vector.map (Expression.eval env)
      (Vector.mapRange m fun i ↦ var { index := i₀ + m + i })) < BigInt.value B (Vector.map (Expression.eval env) n) := by
    rw [hrv_val, show (Vector.map (Expression.eval env) n) = input.2.2 from by rw [← h_input]]
    exact Nat.mod_lt _ hn_pos
  exact ⟨hqn, hrn.1, hconj, ⟨hrn.1, hmap_n_norm⟩, hr_lt_n⟩

/-- The modulus lower bound `2^(T-1) ≤ N` (with `T = (m-1)B + tb`) implies the
quotient-fit bound `2^(2T) ≤ N · 2^(Bm)`, provided `tb + 1 ≤ B`. -/
lemma hn_big_of_ge {B tb : ℕ} (hB1 : 1 ≤ B) (htb1 : 1 ≤ tb) (htbB1 : tb + 1 ≤ B) {N : ℕ}
    (hge : 2 ^ ((m - 1) * B + tb - 1) ≤ N) :
    2 ^ (2 * ((m - 1) * B + tb)) ≤ N * 2 ^ (B * m) := by
  have hBm : B * m = (m - 1) * B + B := by
    have hm := Nat.pos_of_neZero m
    cases m with
    | zero => omega
    | succ k => rw [Nat.succ_sub_one]; ring
  calc (2 : ℕ) ^ (2 * ((m - 1) * B + tb))
      ≤ 2 ^ ((m - 1) * B + tb - 1) * 2 ^ (B * m) := by
        rw [← pow_add]
        apply Nat.pow_le_pow_right (by norm_num)
        rw [hBm]
        set T0 := (m - 1) * B
        omega
    _ ≤ N * 2 ^ (B * m) := Nat.mul_le_mul_right _ hge

/-- **Slack-2 variant** of `hn_big_of_ge`: the weaker modulus lower bound
`2^T ≤ 4·N` (with `T = (m-1)B + tb`, i.e. `N ≥ 2^(T-2)`) still implies the
quotient-fit bound `2^(2T) ≤ N · 2^(Bm)`, provided `tb + 2 ≤ B`. Used by the
`B = 32` retune, where no `(m, tb)` makes `T - 1` equal the modulus bit length. -/
lemma hn_big_of_ge4 {B tb : ℕ} (htbB2 : tb + 2 ≤ B) {N : ℕ}
    (hge : 2 ^ ((m - 1) * B + tb) ≤ 4 * N) :
    2 ^ (2 * ((m - 1) * B + tb)) ≤ N * 2 ^ (B * m) := by
  have hBm : B * m = (m - 1) * B + B := by
    have hm := Nat.pos_of_neZero m
    cases m with
    | zero => omega
    | succ k => rw [Nat.succ_sub_one]; ring
  calc (2 : ℕ) ^ (2 * ((m - 1) * B + tb))
      = 2 ^ ((m - 1) * B + tb) * 2 ^ ((m - 1) * B + tb) := by rw [← pow_add, two_mul]
    _ ≤ (4 * N) * 2 ^ ((m - 1) * B + tb) := Nat.mul_le_mul_right _ hge
    _ = N * 2 ^ ((m - 1) * B + tb + 2) := by
        rw [pow_add 2 ((m - 1) * B + tb) 2, show (2 : ℕ) ^ 2 = 4 from rfl]; ring
    _ ≤ N * 2 ^ (B * m) := Nat.mul_le_mul_left _
        (Nat.pow_le_pow_right (by norm_num) (by rw [hBm]; omega))

/-- **Slack-2 variant** of `qwit_tight`: the honest quotient witness `q = ⌊A·C/N⌋`
is tight-normalized with top limb `< 2^tq`, given `A, C < 2^((m-1)B + tb)`,
`2^((m-1)B + tb) ≤ 4·N` and `tb + 2 ≤ tq ≤ B`. -/
lemma qwit_tight4 {B tb tq : ℕ} (hB : 2 ^ B < p) (htqB : tq ≤ B) (htbq : tb + 2 ≤ tq)
    (i₀ : ℕ) (env : Environment (F p)) (A C N : ℕ)
    (hab_ltT : A < 2 ^ ((m - 1) * B + tb)) (hbb_ltT : C < 2 ^ ((m - 1) * B + tb))
    (hn_ge4 : 2 ^ ((m - 1) * B + tb) ≤ 4 * N)
    (hqwit : ∀ i : Fin m, env.get (i₀ + i.val)
      = ((A * C / N / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p)) :
    BigInt.NormalizedTight B tq (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + i })) := by
  set qval := A * C / N with hqval_def
  have hm1 : m - 1 < m := by have := Nat.pos_of_neZero m; omega
  have hab_prod : A * C < 2 ^ (2 * ((m - 1) * B + tb)) := by
    have hTT : (2 : ℕ) ^ (2 * ((m - 1) * B + tb))
        = 2 ^ ((m - 1) * B + tb) * 2 ^ ((m - 1) * B + tb) := by
      rw [← pow_add, two_mul]
    rw [hTT]
    exact Nat.mul_lt_mul_of_lt_of_le hab_ltT hbb_ltT.le (Nat.two_pow_pos _)
  have hqval_ltT : qval < 2 ^ ((m - 1) * B + tq) := by
    rw [hqval_def]
    apply Nat.div_lt_of_lt_mul
    calc A * C < 2 ^ (2 * ((m - 1) * B + tb)) := hab_prod
      _ = 2 ^ ((m - 1) * B + tb) * 2 ^ ((m - 1) * B + tb) := by rw [← pow_add, two_mul]
      _ ≤ (4 * N) * 2 ^ ((m - 1) * B + tb) := Nat.mul_le_mul_right _ hn_ge4
      _ = N * 2 ^ ((m - 1) * B + tb + 2) := by
          rw [pow_add 2 ((m - 1) * B + tb) 2, show (2 : ℕ) ^ 2 = 4 from rfl]; ring
      _ ≤ N * 2 ^ ((m - 1) * B + tq) := Nat.mul_le_mul_left _
          (Nat.pow_le_pow_right (by norm_num) (by omega))
  refine ⟨normalized_mapRange i₀ qval env hB (by intro i; rw [hqwit i]), ?_⟩
  have hget : (Vector.map (Expression.eval env)
      (Vector.mapRange m fun i ↦ var (F := F p) { index := i₀ + i }))[m - 1]'(by
        have := Nat.pos_of_neZero m; omega) = env.get (i₀ + (m - 1)) := by
    simp [circuit_norm]
  rw [hget, hqwit ⟨m - 1, hm1⟩,
    ZMod.val_natCast_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos B)) hB.le)]
  calc qval / 2 ^ (B * (m - 1)) % 2 ^ B ≤ qval / 2 ^ (B * (m - 1)) := Nat.mod_le _ _
    _ < 2 ^ tq := by
        apply Nat.div_lt_of_lt_mul
        rw [show (2 : ℕ) ^ (B * (m - 1)) * 2 ^ tq = 2 ^ ((m - 1) * B + tq) from by
          rw [← pow_add]; congr 1; ring]
        exact hqval_ltT

/-- **Strict variant** of `qwit_tight` for a squaring/multiply whose second factor
is strictly below the modulus: when `C < N`, the honest quotient
`q = ⌊A·C/N⌋ ≤ A·(N−1)/N < A` fits the *same* top-limb width `tq = tb` as the
operand bound `A < 2^((m-1)B + tb)` — one quotient bit fewer than the generic
lazy bound. -/
lemma qwit_tight_lt {B tb tq : ℕ} (hB : 2 ^ B < p) (htqB : tq ≤ B) (htbq : tb ≤ tq)
    (i₀ : ℕ) (env : Environment (F p)) (A C N : ℕ)
    (hab_ltT : A < 2 ^ ((m - 1) * B + tb))
    (hCN : C < N)
    (hqwit : ∀ i : Fin m, env.get (i₀ + i.val)
      = ((A * C / N / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p)) :
    BigInt.NormalizedTight B tq (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + i })) := by
  set qval := A * C / N with hqval_def
  have hm1 : m - 1 < m := by have := Nat.pos_of_neZero m; omega
  have hqval_ltT : qval < 2 ^ ((m - 1) * B + tq) := by
    have hq_lt : qval < 2 ^ ((m - 1) * B + tb) := by
      rcases Nat.eq_zero_or_pos A with hA0 | hA0
      · rw [hqval_def, hA0, Nat.zero_mul, Nat.zero_div]
        positivity
      · have h1 : A * C < N * A := by
          rw [Nat.mul_comm N A]
          exact Nat.mul_lt_mul_of_le_of_lt (le_refl A) hCN hA0
        have h2 : qval < A := Nat.div_lt_of_lt_mul h1
        exact lt_trans h2 hab_ltT
    exact lt_of_lt_of_le hq_lt (Nat.pow_le_pow_right (by norm_num) (by omega))
  refine ⟨normalized_mapRange i₀ qval env hB (by intro i; rw [hqwit i]), ?_⟩
  have hget : (Vector.map (Expression.eval env)
      (Vector.mapRange m fun i ↦ var (F := F p) { index := i₀ + i }))[m - 1]'(by
        have := Nat.pos_of_neZero m; omega) = env.get (i₀ + (m - 1)) := by
    simp [circuit_norm]
  rw [hget, hqwit ⟨m - 1, hm1⟩,
    ZMod.val_natCast_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos B)) hB.le)]
  calc qval / 2 ^ (B * (m - 1)) % 2 ^ B ≤ qval / 2 ^ (B * (m - 1)) := Nat.mod_le _ _
    _ < 2 ^ tq := by
        apply Nat.div_lt_of_lt_mul
        rw [show (2 : ℕ) ^ (B * (m - 1)) * 2 ^ tq = 2 ^ ((m - 1) * B + tq) from by
          rw [← pow_add]; congr 1; ring]
        exact hqval_ltT

/-- The honest quotient witness `q = ⌊A·C/N⌋` (decomposed into base-`2^B` limbs at
offset `i₀`) is tight-normalized with top limb `< 2^tq`, given
`A, C < 2^((m-1)B + tb)`, `N ≥ 2^((m-1)B + tb - 1)` and `tb < tq ≤ B`. -/
lemma qwit_tight {B tb tq : ℕ} (hB : 2 ^ B < p) (htb1 : 1 ≤ tb) (htqB : tq ≤ B) (htbq : tb < tq)
    (i₀ : ℕ) (env : Environment (F p)) (A C N : ℕ)
    (hab_ltT : A < 2 ^ ((m - 1) * B + tb)) (hbb_ltT : C < 2 ^ ((m - 1) * B + tb))
    (hn_ge : 2 ^ ((m - 1) * B + tb - 1) ≤ N)
    (hqwit : ∀ i : Fin m, env.get (i₀ + i.val)
      = ((A * C / N / 2 ^ (B * i.val) % 2 ^ B : ℕ) : F p)) :
    BigInt.NormalizedTight B tq (Vector.map (Expression.eval env)
        (Vector.mapRange m fun i ↦ var { index := i₀ + i })) := by
  set qval := A * C / N with hqval_def
  have hm1 : m - 1 < m := by have := Nat.pos_of_neZero m; omega
  have hab_prod : A * C < 2 ^ (2 * ((m - 1) * B + tb)) := by
    have hTT : (2 : ℕ) ^ (2 * ((m - 1) * B + tb))
        = 2 ^ ((m - 1) * B + tb) * 2 ^ ((m - 1) * B + tb) := by
      rw [← pow_add, two_mul]
    rw [hTT]
    exact Nat.mul_lt_mul_of_lt_of_le hab_ltT hbb_ltT.le (Nat.two_pow_pos _)
  have hqval_ltT : qval < 2 ^ ((m - 1) * B + tq) := by
    rw [hqval_def]
    apply Nat.div_lt_of_lt_mul
    calc A * C < 2 ^ (2 * ((m - 1) * B + tb)) := hab_prod
      _ ≤ 2 ^ ((m - 1) * B + tb - 1) * 2 ^ ((m - 1) * B + tq) := by
          rw [← pow_add]
          apply Nat.pow_le_pow_right (by norm_num)
          set T0 := (m - 1) * B
          omega
      _ ≤ N * 2 ^ ((m - 1) * B + tq) := Nat.mul_le_mul_right _ hn_ge
  refine ⟨normalized_mapRange i₀ qval env hB (by intro i; rw [hqwit i]), ?_⟩
  have hget : (Vector.map (Expression.eval env)
      (Vector.mapRange m fun i ↦ var (F := F p) { index := i₀ + i }))[m - 1]'(by
        have := Nat.pos_of_neZero m; omega) = env.get (i₀ + (m - 1)) := by
    simp [circuit_norm]
  rw [hget, hqwit ⟨m - 1, hm1⟩,
    ZMod.val_natCast_of_lt (lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos B)) hB.le)]
  calc qval / 2 ^ (B * (m - 1)) % 2 ^ B ≤ qval / 2 ^ (B * (m - 1)) := Nat.mod_le _ _
    _ < 2 ^ tq := by
        apply Nat.div_lt_of_lt_mul
        rw [show (2 : ℕ) ^ (B * (m - 1)) * 2 ^ tq = 2 ^ ((m - 1) * B + tq) from by
          rw [← pow_add]; congr 1; ring]
        exact hqval_ltT

end

end MulMod

end Solution.RSASSAPKCS1v15_SHA256_4096_65537
