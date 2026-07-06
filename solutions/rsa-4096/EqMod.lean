import Solution.RSASSAPKCS1v15_SHA256_4096_65537.EqViaCarries
import Solution.RSASSAPKCS1v15_SHA256_4096_65537.MulMod

/-!
# RSA congruence-pinning gadget — `EqMod`

`EqMod` asserts `lhs = rhs + q·n` for a witnessed **bit** `q`: given that the
caller knows (spec-side) `lhs ≡ rhs (mod n)` with `rhs < n` and `lhs < 2n`, the
wrap count is at most one, so a single boolean `q` and the `m` products `q·n_k`
suffice to pin `rhs` as the canonical representative of `lhs` mod `n`.

This replaces the final `MulModCanon (× 1)` + `Equal` step of the lazy-reduction
pipeline: no quotient limbs, no `Normalize`, no `LessThan`, no full `m×m`
product matrices — just `1 + m` witnesses, `1 + m` boolean/product rows and one
`EqViaCarries` base-`2^B` equality.
-/

namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537
open Specs.RSA

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

namespace EqMod

/-- Inputs of `EqMod`: the lazy value `lhs`, the canonical candidate `rhs`, and
the `modulus`. -/
structure Inputs (m : ℕ) (F : Type) where
  lhs : BigInt m F
  rhs : BigInt m F
  modulus : BigInt m F
deriving ProvableStruct

/-- `lhs` padded to `2m−1` base-`2^B` coefficients (zeros above `m`). -/
def padCoeffs (x : Var (BigInt m) (F p)) : Vector (Expression (F p)) (2 * m - 1) :=
  Vector.mapFinRange (2 * m - 1) fun k => if h : k.val < m then x[k.val]'h else 0

/-- `q·n + rhs` as `2m−1` base-`2^B` coefficients (zeros above `m`), with the
products `q·n_k` read from the witness cells `pp`. -/
def sumCoeffs (pp : Var (fields m) (F p)) (y : Var (BigInt m) (F p)) :
    Vector (Expression (F p)) (2 * m - 1) :=
  Vector.mapFinRange (2 * m - 1) fun k =>
    if h : k.val < m then pp[k.val]'h + y[k.val]'h else 0

/-- The `main` circuit of `EqMod`: witness the wrap bit `q = (lhs − rhs)/n`,
boolean-constrain it, witness the `m` products `q·n_k` (one mul row each), and
assert `lhs = rhs + q·n` in base `2^B` via `EqViaCarries`. -/
def main (P : BigIntParams p m) [Fact (p > 2)] (input : Var (Inputs m) (F p)) :
    Circuit (F p) Unit := do
  let x := input.lhs
  let y := input.rhs
  let n := input.modulus

  -- 1. the wrap bit `q = (lhs.value − rhs.value) / n.value ∈ {0,1}`
  let qv ← witnessVector 1 fun env =>
    Vector.ofFn fun _ =>
      (((MulMod.evalValue P.B env x - MulMod.evalValue P.B env y)
          / MulMod.evalValue P.B env n : ℕ) : F p)
  assertZero ((qv[0]) * ((qv[0]) - 1))

  -- 2. the m products `q·n_k`
  let pp ← witnessVector m fun env =>
    Vector.ofFn fun k : Fin m =>
      Expression.eval env.toEnvironment (qv[0])
        * Expression.eval env.toEnvironment (n[k.val]'k.isLt)
  let prodCs : Vector (Expression (F p)) m := Vector.mapFinRange m fun k =>
    (qv[0]) * (n[k.val]'k.isLt) - (pp[k.val]'k.isLt)
  Circuit.forEach prodCs assertZero

  -- 3. `lhs = q·n + rhs` in base `2^B`
  EqViaCarries.circuit P { lhs := padCoeffs x, rhs := sumCoeffs pp y }

instance elaborated (P : BigIntParams p m) [Fact (p > 2)] :
    ElaboratedCircuit (F p) (Inputs m) unit (main P) where
  localLength _ := 1 + m + ((2 * m - 1 - 1) * (P.W - 1) + (2 * m - 1 - 1))
  localLength_eq := by
    intro input offset
    simp only [main, circuit_norm, EqViaCarries.circuit, EqViaCarries.elaborated,
      EqViaCarries.main, RangeCheck.circuit]
    omega
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, circuit_norm, EqViaCarries.circuit, EqViaCarries.elaborated,
      EqViaCarries.main, RangeCheck.circuit]
  channelsLawful := by
    intro input offset
    simp only [main, circuit_norm, EqViaCarries.circuit, EqViaCarries.elaborated,
      EqViaCarries.main, RangeCheck.circuit]

/-- Preconditions: all three operands normalized and `n` positive. The
congruence facts live in the `Spec` (available to completeness). -/
def Assumptions (B : ℕ) (input : Inputs m (F p)) : Prop :=
  input.lhs.Normalized B ∧ input.rhs.Normalized B ∧ input.modulus.Normalized B ∧
    0 < input.modulus.value B

/-- Postcondition: `lhs` equals `rhs` or `rhs + n` (i.e. `rhs` is the canonical
representative of `lhs` mod `n` whenever `rhs < n` and `lhs < 2n`). -/
def Spec (B : ℕ) (input : Inputs m (F p)) : Prop :=
  input.lhs.value B = input.rhs.value B ∨
    input.lhs.value B = input.rhs.value B + input.modulus.value B

/-- `polyValue` as a guarded `range` sum (total indexing). -/
private lemma polyValue_eq_range_sum {B N : ℕ} (v : Vector (F p) N) :
    polyValue B v
      = ∑ k ∈ Finset.range N, (if h : k < N then (v[k]'h).val * 2 ^ (B * k) else 0) := by
  rw [polyValue, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [dif_pos i.isLt]

/-- Reduce a `range (2m−1)` sum whose entries vanish above `m` to a `range m` sum. -/
private lemma range_sum_reduce (f : ℕ → ℕ) (hM : ∀ k, m ≤ k → f k = 0) :
    ∑ k ∈ Finset.range (2 * m - 1), f k = ∑ k ∈ Finset.range m, f k := by
  have hm : 0 < m := Nat.pos_of_neZero m
  have hsub : Finset.range m ⊆ Finset.range (2 * m - 1) := by
    intro t ht
    simp only [Finset.mem_range] at ht ⊢
    omega
  refine (Finset.sum_subset hsub ?_).symm
  intro k _ hnk
  exact hM k (Nat.le_of_not_lt (by simpa using hnk))

/-- Reduce the `polyValue` of a `2m−1` vector with zero high entries to a plain
`range m` sum of the per-index data `g`. -/
private lemma polyValue_reduce {B : ℕ} (v : Vector (F p) (2 * m - 1)) (g : ℕ → ℕ)
    (hlow : ∀ k, (hk : k < m) → (v[k]'(by omega)).val = g k)
    (hhigh : ∀ k, (hk : k < 2 * m - 1) → m ≤ k → (v[k]'hk).val = 0) :
    polyValue B v = ∑ k ∈ Finset.range m, g k * 2 ^ (B * k) := by
  rw [polyValue_eq_range_sum, range_sum_reduce _ (fun k hk => by
    split
    · rename_i h
      rw [hhigh k h hk, Nat.zero_mul]
    · rfl)]
  apply Finset.sum_congr rfl
  intro k hk
  have hkm : k < m := Finset.mem_range.mp hk
  rw [dif_pos (by omega : k < 2 * m - 1), hlow k hkm]

/-- `BigInt.value` as a plain `range m` sum of guarded per-limb values. -/
private lemma value_eq_guard_sum {B : ℕ} (x : BigInt m (F p)) :
    BigInt.value B x
      = ∑ k ∈ Finset.range m, (if h : k < m then (x[k]'h).val else 0) * 2 ^ (B * k) := by
  rw [BigInt.value_eq_sum, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [dif_pos i.isLt]
  rfl

/-- Linearity of the base-`2^B` weighting over `C·n + y` data. -/
private lemma range_sum_linear {B : ℕ} (C : ℕ) (nv yv : ℕ → ℕ) :
    ∑ k ∈ Finset.range m, (C * nv k + yv k) * 2 ^ (B * k)
      = C * (∑ k ∈ Finset.range m, nv k * 2 ^ (B * k))
        + ∑ k ∈ Finset.range m, yv k * 2 ^ (B * k) := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The `EqMod` formal assertion. -/
def circuit (P : BigIntParams p m) [Fact (p > 2)] : FormalAssertion (F p) (Inputs m) where
  main := main P
  Assumptions := Assumptions P.B
  Spec := Spec P.B
  soundness := by
    obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
    circuit_proof_start [EqViaCarries.circuit, EqViaCarries.elaborated, EqViaCarries.main,
      EqViaCarries.Assumptions, EqViaCarries.Spec]
    obtain ⟨hx_norm, hy_norm, hn_norm, hn_pos⟩ := h_assumptions
    obtain ⟨h_bool, h_prod, h_eq_impl⟩ := h_holds
    have hp2 : 2 < p := Fact.out (p := p > 2)
    haveI : Fact (1 < p) := ⟨by omega⟩
    have hm1 : 0 < m := Nat.pos_of_neZero m
    have heval0 : Expression.eval env (0 : Expression (F p)) = 0 := by simp [circuit_norm]
    -- the wrap bit is boolean
    have hq01 : env.get i₀ = 0 ∨ env.get i₀ = 1 := by
      rcases mul_eq_zero.mp h_bool with h0 | h1
      · exact Or.inl h0
      · right; linear_combination h1
    have hqval01 : (env.get i₀).val = 0 ∨ (env.get i₀).val = 1 := by
      rcases hq01 with h0 | h1
      · left; rw [h0, ZMod.val_zero]
      · right; rw [h1, ZMod.val_one]
    -- the witnessed products are `q·n_k` (field level)
    have hpp : ∀ k, (hk : k < m) →
        env.get (i₀ + 1 + k) = env.get i₀ * Expression.eval env (input_var.modulus[k]'hk) := by
      intro k hk
      have := h_prod ⟨k, hk⟩
      linear_combination -this
    -- input-limb translation
    have hxk : ∀ k, (hk : k < m) →
        Expression.eval env (input_var.lhs[k]'hk) = input.lhs[k]'hk := by
      intro k hk; rw [← h_input]; simp [Vector.getElem_map]
    have hyk : ∀ k, (hk : k < m) →
        Expression.eval env (input_var.rhs[k]'hk) = input.rhs[k]'hk := by
      intro k hk; rw [← h_input]; simp [Vector.getElem_map]
    have hnk : ∀ k, (hk : k < m) →
        Expression.eval env (input_var.modulus[k]'hk) = input.modulus[k]'hk := by
      intro k hk; rw [← h_input]; simp [Vector.getElem_map]
    -- the witnessed products at nat level
    have hppval : ∀ k, (hk : k < m) →
        (env.get (i₀ + 1 + k)).val = (env.get i₀).val * (input.modulus[k]'hk).val := by
      intro k hk
      rw [hpp k hk, hnk k hk]
      rcases hq01 with h0 | h1
      · rw [h0, ZMod.val_zero]; simp
      · rw [h1, ZMod.val_one]; simp
    -- generic bounds
    have h2Ble : (2 : ℕ) ^ B ≤ 2 ^ (2 * B) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2B : (2 : ℕ) ^ B + 2 ^ B ≤ (m + 1) * 2 ^ (2 * B) := by
      calc (2 : ℕ) ^ B + 2 ^ B ≤ 2 ^ (2 * B) + 2 ^ (2 * B) := by omega
        _ = 2 * 2 ^ (2 * B) := by ring
        _ ≤ (m + 1) * 2 ^ (2 * B) := Nat.mul_le_mul_right _ (by omega)
    have hposB : (0 : ℕ) < (m + 1) * 2 ^ (2 * B) := by positivity
    -- discharge the EqViaCarries coefficient bounds and get the polyValue equality
    have hbound1 : ∀ k : Fin (2 * m - 1),
        (Expression.eval env ((padCoeffs input_var.lhs)[k.val]'k.isLt)).val
          < (m + 1) * 2 ^ (2 * B) := by
      intro k
      simp only [padCoeffs, Vector.getElem_mapFinRange]
      split
      · rename_i hk
        rw [hxk k.val hk]
        exact lt_of_lt_of_le (hx_norm ⟨k.val, hk⟩) (by omega)
      · rw [heval0, ZMod.val_zero]
        exact hposB
    have hbound2 : ∀ k : Fin (2 * m - 1),
        (Expression.eval env ((sumCoeffs (Vector.mapRange m fun i => var { index := i₀ + 1 + i })
          input_var.rhs)[k.val]'k.isLt)).val < (m + 1) * 2 ^ (2 * B) := by
      intro k
      simp only [sumCoeffs, Vector.getElem_mapFinRange]
      split
      · rename_i hk
        rw [show Expression.eval env
              (((Vector.mapRange m fun i => var (F := F p) { index := i₀ + 1 + i })[k.val]'hk)
                + (input_var.rhs[k.val]'hk))
            = env.get (i₀ + 1 + k.val) + input.rhs[k.val]'hk from by
          simp only [circuit_norm, Vector.getElem_mapRange]
          rw [hyk k.val hk]]
        have hyv : (input.rhs[k.val]'hk).val < 2 ^ B := hy_norm ⟨k.val, hk⟩
        have hnv : (input.modulus[k.val]'hk).val < 2 ^ B := hn_norm ⟨k.val, hk⟩
        have hppv : (env.get (i₀ + 1 + k.val)).val ≤ (input.modulus[k.val]'hk).val := by
          rw [hppval k.val hk]
          rcases hqval01 with h0 | h1
          · rw [h0, Nat.zero_mul]; exact Nat.zero_le _
          · rw [h1, Nat.one_mul]
        calc (env.get (i₀ + 1 + k.val) + input.rhs[k.val]'hk).val
            ≤ (env.get (i₀ + 1 + k.val)).val + (input.rhs[k.val]'hk).val := ZMod.val_add_le _ _
          _ < 2 ^ B + 2 ^ B := by omega
          _ ≤ (m + 1) * 2 ^ (2 * B) := h2B
      · rw [heval0, ZMod.val_zero]
        exact hposB
    have hpoly := h_eq_impl ⟨hbound1, hbound2⟩
    -- convert both polyValues to values
    have hL : polyValue B (Vector.map (Expression.eval env) (padCoeffs input_var.lhs))
        = BigInt.value B input.lhs := by
      rw [polyValue_reduce _ (fun k => if h : k < m then (input.lhs[k]'h).val else 0)
        (fun k hk => by
          simp only [padCoeffs, Vector.getElem_map, Vector.getElem_mapFinRange,
            dif_pos hk, dif_pos (by omega : k < 2 * m - 1)]
          rw [hxk k hk])
        (fun k hk hmk => by
          simp only [padCoeffs, Vector.getElem_map, Vector.getElem_mapFinRange,
            dif_neg (by omega : ¬ k < m)]
          rw [heval0, ZMod.val_zero])]
      rw [value_eq_guard_sum]
    have hS : polyValue B (Vector.map (Expression.eval env)
          (sumCoeffs (Vector.mapRange m fun i => var { index := i₀ + 1 + i }) input_var.rhs))
        = (env.get i₀).val * BigInt.value B input.modulus + BigInt.value B input.rhs := by
      rw [polyValue_reduce _ (fun k =>
          (env.get i₀).val * (if h : k < m then (input.modulus[k]'h).val else 0)
            + (if h : k < m then (input.rhs[k]'h).val else 0))
        (fun k hk => by
          simp only [sumCoeffs, Vector.getElem_map, Vector.getElem_mapFinRange,
            dif_pos hk, dif_pos (show k < 2 * m - 1 by omega)]
          rw [show Expression.eval env
                (((Vector.mapRange m fun i => var (F := F p) { index := i₀ + 1 + i })[k]'hk)
                  + (input_var.rhs[k]'hk))
              = env.get (i₀ + 1 + k) + input.rhs[k]'hk from by
            simp only [circuit_norm, Vector.getElem_mapRange]
            rw [hyk k hk]]
          have hyv : (input.rhs[k]'hk).val < 2 ^ B := hy_norm ⟨k, hk⟩
          have hnv : (input.modulus[k]'hk).val < 2 ^ B := hn_norm ⟨k, hk⟩
          have hppv : (env.get (i₀ + 1 + k)).val ≤ (input.modulus[k]'hk).val := by
            rw [hppval k hk]
            rcases hqval01 with h0 | h1
            · rw [h0, Nat.zero_mul]; exact Nat.zero_le _
            · rw [h1, Nat.one_mul]
          have hXp : (m + 1) * 2 ^ (2 * B) < p := by omega
          rw [ZMod.val_add_of_lt (by omega), hppval k hk])
        (fun k hk hmk => by
          simp only [sumCoeffs, Vector.getElem_map, Vector.getElem_mapFinRange,
            dif_neg (by omega : ¬ k < m)]
          rw [heval0, ZMod.val_zero])]
      rw [range_sum_linear, ← value_eq_guard_sum, ← value_eq_guard_sum]
    rw [hL, hS] at hpoly
    -- conclude
    rcases hqval01 with h0 | h1
    · left; rw [hpoly, h0, Nat.zero_mul, Nat.zero_add]
    · right; rw [hpoly, h1, Nat.one_mul, Nat.add_comm]
  completeness := by
    obtain ⟨B, W, hB, hW, hB1, hWB, hWp, hp⟩ := P
    circuit_proof_start [EqViaCarries.circuit, EqViaCarries.elaborated, EqViaCarries.main,
      EqViaCarries.Assumptions, EqViaCarries.Spec]
    obtain ⟨hx_norm, hy_norm, hn_norm, hn_pos⟩ := h_assumptions
    obtain ⟨hq_env, hpp_env⟩ := h_env
    have hp2 : 2 < p := Fact.out (p := p > 2)
    haveI : Fact (1 < p) := ⟨by omega⟩
    have hm1 : 0 < m := Nat.pos_of_neZero m
    have heval0 : Expression.eval env.toEnvironment (0 : Expression (F p)) = 0 := by
      simp [circuit_norm]
    -- the honest wrap count
    set X := BigInt.value B input.lhs with hX
    set Y := BigInt.value B input.rhs with hY
    set N := BigInt.value B input.modulus with hN
    have hquot : (X - Y) / N = 0 ∧ X = Y ∨ (X - Y) / N = 1 ∧ X = Y + N := by
      rcases h_spec with h | h
      · exact Or.inl ⟨by rw [h]; simp, h⟩
      · refine Or.inr ⟨?_, h⟩
        rw [h, Nat.add_sub_cancel_left, Nat.div_self hn_pos]
    -- witness translations
    have heva : MulMod.evalValue B env input_var.lhs = X := by
      rw [MulMod.evalValue, hX, BigInt.value, ← h_input]
    have hevb : MulMod.evalValue B env input_var.rhs = Y := by
      rw [MulMod.evalValue, hY, BigInt.value, ← h_input]
    have hevn : MulMod.evalValue B env input_var.modulus = N := by
      rw [MulMod.evalValue, hN, BigInt.value, ← h_input]
    have hqval : env.get i₀ = (((X - Y) / N : ℕ) : F p) := by
      have h := hq_env ⟨0, by omega⟩
      simpa [Vector.getElem_ofFn, heva, hevb, hevn] using h
    have hq01F : env.get i₀ = 0 ∨ env.get i₀ = 1 := by
      rcases hquot with ⟨h, _⟩ | ⟨h, _⟩
      · left; rw [hqval, h]; simp
      · right; rw [hqval, h]; simp
    have hqval01 : (env.get i₀).val = 0 ∨ (env.get i₀).val = 1 := by
      rcases hq01F with h0 | h1
      · left; rw [h0, ZMod.val_zero]
      · right; rw [h1, ZMod.val_one]
    -- limb translations
    have hnk : ∀ k, (hk : k < m) →
        Expression.eval env.toEnvironment (input_var.modulus[k]'hk) = input.modulus[k]'hk := by
      intro k hk; rw [← h_input]; simp [Vector.getElem_map]
    have hyk : ∀ k, (hk : k < m) →
        Expression.eval env.toEnvironment (input_var.rhs[k]'hk) = input.rhs[k]'hk := by
      intro k hk; rw [← h_input]; simp [Vector.getElem_map]
    have hxk : ∀ k, (hk : k < m) →
        Expression.eval env.toEnvironment (input_var.lhs[k]'hk) = input.lhs[k]'hk := by
      intro k hk; rw [← h_input]; simp [Vector.getElem_map]
    -- witnessed products
    have hppk : ∀ k, (hk : k < m) →
        env.get (i₀ + 1 + k)
          = env.get i₀ * Expression.eval env.toEnvironment (input_var.modulus[k]'hk) := by
      intro k hk
      have h := hpp_env ⟨k, hk⟩
      simpa [Vector.getElem_ofFn] using h
    have hppval : ∀ k, (hk : k < m) →
        (env.get (i₀ + 1 + k)).val = (env.get i₀).val * (input.modulus[k]'hk).val := by
      intro k hk
      rw [hppk k hk, hnk k hk]
      rcases hq01F with h0 | h1
      · rw [h0, ZMod.val_zero]; simp
      · rw [h1, ZMod.val_one]; simp
    have h2Ble : (2 : ℕ) ^ B ≤ 2 ^ (2 * B) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2B : (2 : ℕ) ^ B + 2 ^ B ≤ (m + 1) * 2 ^ (2 * B) := by
      calc (2 : ℕ) ^ B + 2 ^ B ≤ 2 ^ (2 * B) + 2 ^ (2 * B) := by omega
        _ = 2 * 2 ^ (2 * B) := by ring
        _ ≤ (m + 1) * 2 ^ (2 * B) := Nat.mul_le_mul_right _ (by omega)
    have hposB : (0 : ℕ) < (m + 1) * 2 ^ (2 * B) := by positivity
    refine ⟨?_, ?_, ⟨?_, ?_⟩, ?_⟩
    · -- booleanity holds
      rcases hq01F with h0 | h1
      · rw [h0]; ring
      · rw [h1]; ring
    · -- product asserts hold
      intro k
      rw [hppk k.val k.isLt]
      ring
    · -- EqViaCarries coefficient bound: lhs
      intro k
      simp only [padCoeffs, Vector.getElem_mapFinRange]
      split
      · rename_i hk
        rw [hxk k.val hk]
        exact lt_of_lt_of_le (hx_norm ⟨k.val, hk⟩) (by omega)
      · rw [heval0, ZMod.val_zero]
        exact hposB
    · -- EqViaCarries coefficient bound: rhs
      intro k
      simp only [sumCoeffs, Vector.getElem_mapFinRange]
      split
      · rename_i hk
        rw [show Expression.eval env.toEnvironment
              (((Vector.mapRange m fun i => var (F := F p) { index := i₀ + 1 + i })[k.val]'hk)
                + (input_var.rhs[k.val]'hk))
            = env.get (i₀ + 1 + k.val) + input.rhs[k.val]'hk from by
          simp only [circuit_norm, Vector.getElem_mapRange]
          rw [hyk k.val hk]]
        have hyv : (input.rhs[k.val]'hk).val < 2 ^ B := hy_norm ⟨k.val, hk⟩
        have hnv : (input.modulus[k.val]'hk).val < 2 ^ B := hn_norm ⟨k.val, hk⟩
        have hppv : (env.get (i₀ + 1 + k.val)).val ≤ (input.modulus[k.val]'hk).val := by
          rw [hppval k.val hk]
          rcases hqval01 with h0 | h1
          · rw [h0, Nat.zero_mul]; exact Nat.zero_le _
          · rw [h1, Nat.one_mul]
        calc (env.get (i₀ + 1 + k.val) + input.rhs[k.val]'hk).val
            ≤ (env.get (i₀ + 1 + k.val)).val + (input.rhs[k.val]'hk).val := ZMod.val_add_le _ _
          _ < 2 ^ B + 2 ^ B := by omega
          _ ≤ (m + 1) * 2 ^ (2 * B) := h2B
      · rw [heval0, ZMod.val_zero]
        exact hposB
    · -- EqViaCarries spec: polyValue equality for the honest witness
      have hL : polyValue B (Vector.map (Expression.eval env.toEnvironment)
            (padCoeffs input_var.lhs)) = X := by
        rw [polyValue_reduce _ (fun k => if h : k < m then (input.lhs[k]'h).val else 0)
          (fun k hk => by
            simp only [padCoeffs, Vector.getElem_map, Vector.getElem_mapFinRange,
              dif_pos hk, dif_pos (by omega : k < 2 * m - 1)]
            rw [hxk k hk])
          (fun k hk hmk => by
            simp only [padCoeffs, Vector.getElem_map, Vector.getElem_mapFinRange,
              dif_neg (by omega : ¬ k < m)]
            rw [heval0, ZMod.val_zero])]
        rw [hX, value_eq_guard_sum]
      have hS : polyValue B (Vector.map (Expression.eval env.toEnvironment)
            (sumCoeffs (Vector.mapRange m fun i => var { index := i₀ + 1 + i }) input_var.rhs))
          = (env.get i₀).val * N + Y := by
        rw [polyValue_reduce _ (fun k =>
            (env.get i₀).val * (if h : k < m then (input.modulus[k]'h).val else 0)
              + (if h : k < m then (input.rhs[k]'h).val else 0))
          (fun k hk => by
            simp only [sumCoeffs, Vector.getElem_map, Vector.getElem_mapFinRange,
              dif_pos hk, dif_pos (show k < 2 * m - 1 by omega)]
            rw [show Expression.eval env.toEnvironment
                  (((Vector.mapRange m fun i => var (F := F p) { index := i₀ + 1 + i })[k]'hk)
                    + (input_var.rhs[k]'hk))
                = env.get (i₀ + 1 + k) + input.rhs[k]'hk from by
              simp only [circuit_norm, Vector.getElem_mapRange]
              rw [hyk k hk]]
            have hyv : (input.rhs[k]'hk).val < 2 ^ B := hy_norm ⟨k, hk⟩
            have hnv : (input.modulus[k]'hk).val < 2 ^ B := hn_norm ⟨k, hk⟩
            have hppv : (env.get (i₀ + 1 + k)).val ≤ (input.modulus[k]'hk).val := by
              rw [hppval k hk]
              rcases hqval01 with h0 | h1
              · rw [h0, Nat.zero_mul]; exact Nat.zero_le _
              · rw [h1, Nat.one_mul]
            have hXp : (m + 1) * 2 ^ (2 * B) < p := by omega
            rw [ZMod.val_add_of_lt (by omega), hppval k hk])
          (fun k hk hmk => by
            simp only [sumCoeffs, Vector.getElem_map, Vector.getElem_mapFinRange,
              dif_neg (by omega : ¬ k < m)]
            rw [heval0, ZMod.val_zero])]
        rw [range_sum_linear, ← value_eq_guard_sum, ← value_eq_guard_sum, ← hN, ← hY]
      rw [hL, hS]
      rcases hquot with ⟨hq, hxy⟩ | ⟨hq, hxy⟩
      · rw [hqval, hq, Nat.cast_zero, ZMod.val_zero, Nat.zero_mul, Nat.zero_add]
        exact hxy
      · rw [hqval, hq, Nat.cast_one, ZMod.val_one, Nat.one_mul, hxy, Nat.add_comm]

end EqMod

end
end Solution.RSASSAPKCS1v15_SHA256_4096_65537
