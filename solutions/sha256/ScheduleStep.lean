import Solution.SHA256.LowerSigma0
import Solution.SHA256.LowerSigma1
import Solution.SHA256.Add32
import Solution.SHA256.AddMany
import Solution.SHA256.SigmaSum
import Challenge.Specs.SHA256

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^35)]

namespace Solution.SHA256

/-!
# SHA-256 Message-Schedule Step (fused σ-pairing)

Computes one new schedule word from the four words a step reads:

  w[j] = σ₁(w[j−2]) + w[j−7] + σ₀(w[j−15]) + w[j−16]   (mod 2^32)

Monolithic gadget: instead of composing `LowerSigma1` (32w+32r), `LowerSigma0`
(32w+32r) and `AddMany2` (33w+34r) — 97 witnesses / 98 rows — the 13 two-input
XOR lanes (σ₀ lanes 29–31, σ₁ lanes 22–31) are paired two-at-a-time into a
single witness and single determined row each (see `SigmaSum`):

  u₀ = σ1₂₂ + 4σ1₂₄, u₁ = σ1₂₃ + 4σ1₂₅, u₂ = σ1₂₆ + 4σ1₂₈, u₃ = σ1₂₇ + 4σ1₂₉,
  u₄ = σ1₃₀ + σ0₃₀, u₅ = σ1₃₁ + σ0₃₁, v = σ0₂₉ alone.

Witnesses: 29 (σ₀ lanes 0–28) + 22 (σ₁ lanes 0–21) + 6 (pairs) + 1 (v)
+ 32 (output bits) + 1 (high carry) = 91; rows: 29 + 22 + 6 + 1 + 32 + 1 + 1
= 92. Output word at relative offset 58. The fused adder row recombines the
paired lanes through the packed column vector `SigmaSum.tVec`.
-/

namespace ScheduleStep

structure Inputs (F : Type) where
  wm2  : fields 32 F   -- w[j-2]
  wm7  : fields 32 F   -- w[j-7]
  wm15 : fields 32 F   -- w[j-15]
  wm16 : fields 32 F   -- w[j-16]
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var (fields 32) (F p)) := do
  -- σ₀ 3-input lanes 0–28
  let s0 ← witnessVector 29 fun env =>
    Vector.ofFn fun (i : Fin 29) => ((SigmaSum.lane0 env input.wm15 i.val : ℕ) : F p)
  -- σ₁ 3-input lanes 0–21
  let s1 ← witnessVector 22 fun env =>
    Vector.ofFn fun (i : Fin 22) => ((SigmaSum.lane1 env input.wm2 i.val : ℕ) : F p)
  -- the 6 σ-pair witnesses
  let u ← witnessVector 6 fun env =>
    #v[((SigmaSum.lane1 env input.wm2 22 + 4 * SigmaSum.lane1 env input.wm2 24 : ℕ) : F p),
       ((SigmaSum.lane1 env input.wm2 23 + 4 * SigmaSum.lane1 env input.wm2 25 : ℕ) : F p),
       ((SigmaSum.lane1 env input.wm2 26 + 4 * SigmaSum.lane1 env input.wm2 28 : ℕ) : F p),
       ((SigmaSum.lane1 env input.wm2 27 + 4 * SigmaSum.lane1 env input.wm2 29 : ℕ) : F p),
       ((SigmaSum.lane1 env input.wm2 30 + SigmaSum.lane0 env input.wm15 30 : ℕ) : F p),
       ((SigmaSum.lane1 env input.wm2 31 + SigmaSum.lane0 env input.wm15 31 : ℕ) : F p)]
  -- σ₀ lane 29 alone
  let v ← witnessField fun env => ((SigmaSum.lane0 env input.wm15 29 : ℕ) : F p)
  -- output bits of the fused 4-word addition
  let z ← witnessVector 32 fun env =>
    let s := SigmaSum.schedSumNat env input.wm2 input.wm7 input.wm15 input.wm16
    Vector.ofFn fun (i : Fin 32) => ((s % 2^32 / 2^i.val % 2 : ℕ) : F p)
  -- the single high carry bit (weight 2)
  let c1 ← witnessField fun env =>
    ((SigmaSum.schedSumNat env input.wm2 input.wm7 input.wm15 input.wm16 / 2^32 / 2 % 2 : ℕ) : F p)
  -- σ₀ single-row 3-input XOR lanes (clean#395)
  Circuit.forEach (Vector.finRange 29) fun i =>
    assertZero (6 * (rotr32 7 input.wm15)[i.val]'(by omega)
      + 6 * (rotr32 18 input.wm15)[i.val]'(by omega)
      - 24 * input.wm15[i.val + 3]'(by omega)
      - (s0[i.val]'(by omega) + 2 * (rotr32 7 input.wm15)[i.val]'(by omega)
          + 2 * (rotr32 18 input.wm15)[i.val]'(by omega)
          + 7 * input.wm15[i.val + 3]'(by omega)) *
        ((rotr32 7 input.wm15)[i.val]'(by omega) + (rotr32 18 input.wm15)[i.val]'(by omega)
          - 4 * input.wm15[i.val + 3]'(by omega) + 1))
  -- σ₁ single-row 3-input XOR lanes
  Circuit.forEach (Vector.finRange 22) fun i =>
    assertZero (6 * (rotr32 17 input.wm2)[i.val]'(by omega)
      + 6 * (rotr32 19 input.wm2)[i.val]'(by omega)
      - 24 * input.wm2[i.val + 10]'(by omega)
      - (s1[i.val]'(by omega) + 2 * (rotr32 17 input.wm2)[i.val]'(by omega)
          + 2 * (rotr32 19 input.wm2)[i.val]'(by omega)
          + 7 * input.wm2[i.val + 10]'(by omega)) *
        ((rotr32 17 input.wm2)[i.val]'(by omega) + (rotr32 19 input.wm2)[i.val]'(by omega)
          - 4 * input.wm2[i.val + 10]'(by omega) + 1))
  -- pair rows: u_j = xor2(a,b) + λ·xor2(c,d), one determined row each
  assertZero (2 * (rotr32 17 input.wm2)[(22 : ℕ)]'(by norm_num)
    - 2 * (rotr32 19 input.wm2)[(22 : ℕ)]'(by norm_num)
    + 8 * ((rotr32 17 input.wm2)[(24 : ℕ)]'(by norm_num) + (rotr32 19 input.wm2)[(24 : ℕ)]'(by norm_num))
    - 1 - u[(0 : ℕ)]'(by norm_num)
    - (2 * ((rotr32 17 input.wm2)[(24 : ℕ)]'(by norm_num) + (rotr32 19 input.wm2)[(24 : ℕ)]'(by norm_num))
        - (1 - (rotr32 17 input.wm2)[(22 : ℕ)]'(by norm_num) + (rotr32 19 input.wm2)[(22 : ℕ)]'(by norm_num))) *
      (2 * ((rotr32 17 input.wm2)[(24 : ℕ)]'(by norm_num) + (rotr32 19 input.wm2)[(24 : ℕ)]'(by norm_num))
        + (1 - (rotr32 17 input.wm2)[(22 : ℕ)]'(by norm_num) + (rotr32 19 input.wm2)[(22 : ℕ)]'(by norm_num))))
  assertZero (2 * (rotr32 17 input.wm2)[(23 : ℕ)]'(by norm_num)
    - 2 * (rotr32 19 input.wm2)[(23 : ℕ)]'(by norm_num)
    + 8 * ((rotr32 17 input.wm2)[(25 : ℕ)]'(by norm_num) + (rotr32 19 input.wm2)[(25 : ℕ)]'(by norm_num))
    - 1 - u[(1 : ℕ)]'(by norm_num)
    - (2 * ((rotr32 17 input.wm2)[(25 : ℕ)]'(by norm_num) + (rotr32 19 input.wm2)[(25 : ℕ)]'(by norm_num))
        - (1 - (rotr32 17 input.wm2)[(23 : ℕ)]'(by norm_num) + (rotr32 19 input.wm2)[(23 : ℕ)]'(by norm_num))) *
      (2 * ((rotr32 17 input.wm2)[(25 : ℕ)]'(by norm_num) + (rotr32 19 input.wm2)[(25 : ℕ)]'(by norm_num))
        + (1 - (rotr32 17 input.wm2)[(23 : ℕ)]'(by norm_num) + (rotr32 19 input.wm2)[(23 : ℕ)]'(by norm_num))))
  assertZero (2 * (rotr32 17 input.wm2)[(26 : ℕ)]'(by norm_num)
    - 2 * (rotr32 19 input.wm2)[(26 : ℕ)]'(by norm_num)
    + 8 * ((rotr32 17 input.wm2)[(28 : ℕ)]'(by norm_num) + (rotr32 19 input.wm2)[(28 : ℕ)]'(by norm_num))
    - 1 - u[(2 : ℕ)]'(by norm_num)
    - (2 * ((rotr32 17 input.wm2)[(28 : ℕ)]'(by norm_num) + (rotr32 19 input.wm2)[(28 : ℕ)]'(by norm_num))
        - (1 - (rotr32 17 input.wm2)[(26 : ℕ)]'(by norm_num) + (rotr32 19 input.wm2)[(26 : ℕ)]'(by norm_num))) *
      (2 * ((rotr32 17 input.wm2)[(28 : ℕ)]'(by norm_num) + (rotr32 19 input.wm2)[(28 : ℕ)]'(by norm_num))
        + (1 - (rotr32 17 input.wm2)[(26 : ℕ)]'(by norm_num) + (rotr32 19 input.wm2)[(26 : ℕ)]'(by norm_num))))
  assertZero (2 * (rotr32 17 input.wm2)[(27 : ℕ)]'(by norm_num)
    - 2 * (rotr32 19 input.wm2)[(27 : ℕ)]'(by norm_num)
    + 8 * ((rotr32 17 input.wm2)[(29 : ℕ)]'(by norm_num) + (rotr32 19 input.wm2)[(29 : ℕ)]'(by norm_num))
    - 1 - u[(3 : ℕ)]'(by norm_num)
    - (2 * ((rotr32 17 input.wm2)[(29 : ℕ)]'(by norm_num) + (rotr32 19 input.wm2)[(29 : ℕ)]'(by norm_num))
        - (1 - (rotr32 17 input.wm2)[(27 : ℕ)]'(by norm_num) + (rotr32 19 input.wm2)[(27 : ℕ)]'(by norm_num))) *
      (2 * ((rotr32 17 input.wm2)[(29 : ℕ)]'(by norm_num) + (rotr32 19 input.wm2)[(29 : ℕ)]'(by norm_num))
        + (1 - (rotr32 17 input.wm2)[(27 : ℕ)]'(by norm_num) + (rotr32 19 input.wm2)[(27 : ℕ)]'(by norm_num))))
  assertZero (2 * (rotr32 17 input.wm2)[(30 : ℕ)]'(by norm_num)
    - 2 * (rotr32 19 input.wm2)[(30 : ℕ)]'(by norm_num)
    + 2 * ((rotr32 7 input.wm15)[(30 : ℕ)]'(by norm_num) + (rotr32 18 input.wm15)[(30 : ℕ)]'(by norm_num))
    - 1 - u[(4 : ℕ)]'(by norm_num)
    - (((rotr32 7 input.wm15)[(30 : ℕ)]'(by norm_num) + (rotr32 18 input.wm15)[(30 : ℕ)]'(by norm_num))
        - (1 - (rotr32 17 input.wm2)[(30 : ℕ)]'(by norm_num) + (rotr32 19 input.wm2)[(30 : ℕ)]'(by norm_num))) *
      (((rotr32 7 input.wm15)[(30 : ℕ)]'(by norm_num) + (rotr32 18 input.wm15)[(30 : ℕ)]'(by norm_num))
        + (1 - (rotr32 17 input.wm2)[(30 : ℕ)]'(by norm_num) + (rotr32 19 input.wm2)[(30 : ℕ)]'(by norm_num))))
  assertZero (2 * (rotr32 17 input.wm2)[(31 : ℕ)]'(by norm_num)
    - 2 * (rotr32 19 input.wm2)[(31 : ℕ)]'(by norm_num)
    + 2 * ((rotr32 7 input.wm15)[(31 : ℕ)]'(by norm_num) + (rotr32 18 input.wm15)[(31 : ℕ)]'(by norm_num))
    - 1 - u[(5 : ℕ)]'(by norm_num)
    - (((rotr32 7 input.wm15)[(31 : ℕ)]'(by norm_num) + (rotr32 18 input.wm15)[(31 : ℕ)]'(by norm_num))
        - (1 - (rotr32 17 input.wm2)[(31 : ℕ)]'(by norm_num) + (rotr32 19 input.wm2)[(31 : ℕ)]'(by norm_num))) *
      (((rotr32 7 input.wm15)[(31 : ℕ)]'(by norm_num) + (rotr32 18 input.wm15)[(31 : ℕ)]'(by norm_num))
        + (1 - (rotr32 17 input.wm2)[(31 : ℕ)]'(by norm_num) + (rotr32 19 input.wm2)[(31 : ℕ)]'(by norm_num))))
  -- σ₀ lane 29: determined 2-input row
  assertZero (v - (rotr32 7 input.wm15)[(29 : ℕ)]'(by norm_num) - (rotr32 18 input.wm15)[(29 : ℕ)]'(by norm_num)
    + 2 * (rotr32 7 input.wm15)[(29 : ℕ)]'(by norm_num) * (rotr32 18 input.wm15)[(29 : ℕ)]'(by norm_num))
  -- booleanity of the output bits
  Circuit.forEach (Vector.finRange 32) fun i => assertZero (z[i] * (z[i] - 1))
  -- booleanity of the high carry bit
  assertZero (c1 * (c1 - 1))
  -- fused low-carry booleanity + sum recomposition row
  let e0 := ((2^32 : F p)⁻¹ : F p) *
      (fromBitsExpr input.wm7 + fromBitsExpr input.wm16 + fromBitsExpr (SigmaSum.tVec s0 s1 u v)
        - fromBitsExpr z) - 2 * c1
  assertZero (e0 * (e0 - 1))
  return z

def Assumptions (input : Inputs (F p)) : Prop :=
  Normalized input.wm2 ∧ Normalized input.wm7 ∧ Normalized input.wm15 ∧ Normalized input.wm16

def Spec (input : Inputs (F p)) (wj : fields 32 (F p)) : Prop :=
  valueBits wj =
    _root_.add32
      (_root_.add32 (Specs.SHA256.lowerSigma1 (valueBits input.wm2)) (valueBits input.wm7))
      (_root_.add32 (Specs.SHA256.lowerSigma0 (valueBits input.wm15)) (valueBits input.wm16))
  ∧ Normalized wj

instance elaborated : ElaboratedCircuit (F p) Inputs (fields 32) main := by
  elaborate_circuit

set_option maxHeartbeats 4000000 in
theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [main]
  obtain ⟨h_m2, h_m7, h_m15, h_m16⟩ := h_assumptions
  obtain ⟨h_i2, h_i7, h_i15, h_i16⟩ := h_input
  obtain ⟨h_s0, h_s1, hu0, hu1, hu2, hu3, hu4, hu5, hv, h_zb, h_c1b, h_e0⟩ := h_holds
  -- Normalization of the rotated/shifted evaluated input vectors
  have nr7  := Normalized_eval_rotr32 env input_var_wm15 input_wm15 h_i15 h_m15 7
  have nr18 := Normalized_eval_rotr32 env input_var_wm15 input_wm15 h_i15 h_m15 18
  have ns3  := Normalized_eval_shr32  env input_var_wm15 input_wm15 h_i15 h_m15 3
  have nr17 := Normalized_eval_rotr32 env input_var_wm2 input_wm2 h_i2 h_m2 17
  have nr19 := Normalized_eval_rotr32 env input_var_wm2 input_wm2 h_i2 h_m2 19
  have ns10 := Normalized_eval_shr32  env input_var_wm2 input_wm2 h_i2 h_m2 10
  -- Booleanity of the row atoms
  have b7 : ∀ (j : ℕ) (hj : j < 32),
      IsBool (Expression.eval env ((rotr32 7 input_var_wm15)[j]'hj)) := by
    intro j hj
    have h := nr7 ⟨j, hj⟩
    rwa [Fin.getElem_fin, Vector.getElem_map] at h
  have b18 : ∀ (j : ℕ) (hj : j < 32),
      IsBool (Expression.eval env ((rotr32 18 input_var_wm15)[j]'hj)) := by
    intro j hj
    have h := nr18 ⟨j, hj⟩
    rwa [Fin.getElem_fin, Vector.getElem_map] at h
  have b17 : ∀ (j : ℕ) (hj : j < 32),
      IsBool (Expression.eval env ((rotr32 17 input_var_wm2)[j]'hj)) := by
    intro j hj
    have h := nr17 ⟨j, hj⟩
    rwa [Fin.getElem_fin, Vector.getElem_map] at h
  have b19 : ∀ (j : ℕ) (hj : j < 32),
      IsBool (Expression.eval env ((rotr32 19 input_var_wm2)[j]'hj)) := by
    intro j hj
    have h := nr19 ⟨j, hj⟩
    rwa [Fin.getElem_fin, Vector.getElem_map] at h
  -- Input-bit evaluation and booleanity, ℕ-indexed
  have e15 : ∀ (k : ℕ) (hk : k < 32),
      Expression.eval env (input_var_wm15[k]'hk) = input_wm15[k]'hk := by
    intro k hk
    have h := Vector.ext_iff.mp h_i15 k hk
    rwa [Vector.getElem_map] at h
  have e2 : ∀ (k : ℕ) (hk : k < 32),
      Expression.eval env (input_var_wm2[k]'hk) = input_wm2[k]'hk := by
    intro k hk
    have h := Vector.ext_iff.mp h_i2 k hk
    rwa [Vector.getElem_map] at h
  have m15b : ∀ (k : ℕ) (hk : k < 32), IsBool (input_wm15[k]'hk) := by
    intro k hk
    have h := h_m15 ⟨k, hk⟩
    rwa [Fin.getElem_fin] at h
  have m2b : ∀ (k : ℕ) (hk : k < 32), IsBool (input_wm2[k]'hk) := by
    intro k hk
    have h := h_m2 ⟨k, hk⟩
    rwa [Fin.getElem_fin] at h
  -- Evaluated vectors
  set r7  := Vector.map (Expression.eval env) (rotr32 7 input_var_wm15) with hr7
  set r18 := Vector.map (Expression.eval env) (rotr32 18 input_var_wm15) with hr18
  set s3  := Vector.map (Expression.eval env) (shr32 3 input_var_wm15) with hs3
  set r17 := Vector.map (Expression.eval env) (rotr32 17 input_var_wm2) with hr17
  set r19 := Vector.map (Expression.eval env) (rotr32 19 input_var_wm2) with hr19
  set s10 := Vector.map (Expression.eval env) (shr32 10 input_var_wm2) with hs10
  -- bitsFn of the evaluated vectors at the row atoms
  have br7 : ∀ (j : ℕ) (hj : j < 32),
      SigmaSum.bitsFn r7 j = (Expression.eval env ((rotr32 7 input_var_wm15)[j]'hj)).val := by
    intro j hj
    rw [SigmaSum.bitsFn_lt hj, hr7, Vector.getElem_map]
  have br18 : ∀ (j : ℕ) (hj : j < 32),
      SigmaSum.bitsFn r18 j = (Expression.eval env ((rotr32 18 input_var_wm15)[j]'hj)).val := by
    intro j hj
    rw [SigmaSum.bitsFn_lt hj, hr18, Vector.getElem_map]
  have br17 : ∀ (j : ℕ) (hj : j < 32),
      SigmaSum.bitsFn r17 j = (Expression.eval env ((rotr32 17 input_var_wm2)[j]'hj)).val := by
    intro j hj
    rw [SigmaSum.bitsFn_lt hj, hr17, Vector.getElem_map]
  have br19 : ∀ (j : ℕ) (hj : j < 32),
      SigmaSum.bitsFn r19 j = (Expression.eval env ((rotr32 19 input_var_wm2)[j]'hj)).val := by
    intro j hj
    rw [SigmaSum.bitsFn_lt hj, hr19, Vector.getElem_map]
  have bs3lt : ∀ (j : ℕ) (hj : j < 29),
      SigmaSum.bitsFn s3 j = (input_wm15[j + 3]'(by omega)).val := by
    intro j hj
    rw [SigmaSum.bitsFn_lt (show j < 32 by omega), hs3, Vector.getElem_map]
    have h := eval_shr32 env input_var_wm15 input_wm15 h_i15 3 ⟨j, by omega⟩
    simp only [Fin.val_mk, show (3 : Fin 32).val = 3 from rfl] at h
    rw [h, dif_pos (show j + 3 < 32 by omega)]
  have bs3ge : ∀ (j : ℕ) (h1 : 29 ≤ j) (hj : j < 32), SigmaSum.bitsFn s3 j = 0 := by
    intro j h1 hj
    rw [SigmaSum.bitsFn_lt hj, hs3, Vector.getElem_map]
    have h := eval_shr32 env input_var_wm15 input_wm15 h_i15 3 ⟨j, hj⟩
    simp only [Fin.val_mk, show (3 : Fin 32).val = 3 from rfl] at h
    rw [h, dif_neg (show ¬(j + 3 < 32) by omega)]
    exact ZMod.val_zero
  have bs10lt : ∀ (j : ℕ) (hj : j < 22),
      SigmaSum.bitsFn s10 j = (input_wm2[j + 10]'(by omega)).val := by
    intro j hj
    rw [SigmaSum.bitsFn_lt (show j < 32 by omega), hs10, Vector.getElem_map]
    have h := eval_shr32 env input_var_wm2 input_wm2 h_i2 10 ⟨j, by omega⟩
    simp only [Fin.val_mk, show (10 : Fin 32).val = 10 from rfl] at h
    rw [h, dif_pos (show j + 10 < 32 by omega)]
  have bs10ge : ∀ (j : ℕ) (h1 : 22 ≤ j) (hj : j < 32), SigmaSum.bitsFn s10 j = 0 := by
    intro j h1 hj
    rw [SigmaSum.bitsFn_lt hj, hs10, Vector.getElem_map]
    have h := eval_shr32 env input_var_wm2 input_wm2 h_i2 10 ⟨j, hj⟩
    simp only [Fin.val_mk, show (10 : Fin 32).val = 10 from rfl] at h
    rw [h, dif_neg (show ¬(j + 10 < 32) by omega)]
    exact ZMod.val_zero
  -- The two σ bit-column functions
  set X0 : ℕ → ℕ :=
    fun j => SigmaSum.bitsFn r7 j ^^^ SigmaSum.bitsFn r18 j ^^^ SigmaSum.bitsFn s3 j with hX0
  set X1 : ℕ → ℕ :=
    fun j => SigmaSum.bitsFn r17 j ^^^ SigmaSum.bitsFn r19 j ^^^ SigmaSum.bitsFn s10 j with hX1
  have hX0le : ∀ j, X0 j ≤ 1 := by
    intro j
    simp only [hX0]
    exact SigmaSum.xor_le_one (SigmaSum.xor_le_one (SigmaSum.bitsFn_le_one nr7 j)
      (SigmaSum.bitsFn_le_one nr18 j)) (SigmaSum.bitsFn_le_one ns3 j)
  have hX1le : ∀ j, X1 j ≤ 1 := by
    intro j
    simp only [hX1]
    exact SigmaSum.xor_le_one (SigmaSum.xor_le_one (SigmaSum.bitsFn_le_one nr17 j)
      (SigmaSum.bitsFn_le_one nr19 j)) (SigmaSum.bitsFn_le_one ns10 j)
  have hX0hi : ∀ (j : ℕ) (h1 : 29 ≤ j) (hj : j < 32),
      X0 j = (Expression.eval env ((rotr32 7 input_var_wm15)[j]'hj)).val
        ^^^ (Expression.eval env ((rotr32 18 input_var_wm15)[j]'hj)).val := by
    intro j h1 hj
    simp only [hX0]
    rw [br7 j hj, br18 j hj, bs3ge j h1 hj, Nat.xor_zero]
  have hX1hi : ∀ (j : ℕ) (h1 : 22 ≤ j) (hj : j < 32),
      X1 j = (Expression.eval env ((rotr32 17 input_var_wm2)[j]'hj)).val
        ^^^ (Expression.eval env ((rotr32 19 input_var_wm2)[j]'hj)).val := by
    intro j h1 hj
    simp only [hX1]
    rw [br17 j hj, br19 j hj, bs10ge j h1 hj, Nat.xor_zero]
  -- The σ₀ 3-input lane witnesses carry the parity value
  have hs0val : ∀ (j : ℕ) (hj : j < 29), env.get (i₀ + j) = ((X0 j : ℕ) : F p) := by
    intro j hj
    have h2 := h_s0 ⟨j, hj⟩
    simp only [Fin.val_mk] at h2
    rw [e15 (j + 3) (by omega)] at h2
    have key := Xor3.xor3_unique (o := env.get (i₀ + j)) (b7 j (by omega)) (b18 j (by omega))
      (m15b (j + 3) (by omega)) (by linear_combination -h2)
    rw [key, ← Xor3.xor3_val_cast_eq (b7 j (by omega)) (b18 j (by omega)) (m15b (j + 3) (by omega))]
    congr 1
    simp only [hX0]
    rw [br7 j (by omega), br18 j (by omega), bs3lt j hj]
  have hs1val : ∀ (j : ℕ) (hj : j < 22), env.get (i₀ + 29 + j) = ((X1 j : ℕ) : F p) := by
    intro j hj
    have h2 := h_s1 ⟨j, hj⟩
    simp only [Fin.val_mk] at h2
    rw [e2 (j + 10) (by omega)] at h2
    have key := Xor3.xor3_unique (o := env.get (i₀ + 29 + j)) (b17 j (by omega)) (b19 j (by omega))
      (m2b (j + 10) (by omega)) (by linear_combination -h2)
    rw [key, ← Xor3.xor3_val_cast_eq (b17 j (by omega)) (b19 j (by omega)) (m2b (j + 10) (by omega))]
    congr 1
    simp only [hX1]
    rw [br17 j (by omega), br19 j (by omega), bs10lt j hj]
  -- Pair witnesses carry the packed pair values
  have hu0val : env.get (i₀ + 29 + 22) = ((X1 22 + 4 * X1 24 : ℕ) : F p) := by
    rw [hX1hi 22 (by norm_num) (by norm_num), hX1hi 24 (by norm_num) (by norm_num),
      ← SigmaSum.pair_val4 (b17 22 (by norm_num)) (b19 22 (by norm_num))
        (b17 24 (by norm_num)) (b19 24 (by norm_num))]
    linear_combination -hu0
  have hu1val : env.get (i₀ + 29 + 22 + 1) = ((X1 23 + 4 * X1 25 : ℕ) : F p) := by
    rw [hX1hi 23 (by norm_num) (by norm_num), hX1hi 25 (by norm_num) (by norm_num),
      ← SigmaSum.pair_val4 (b17 23 (by norm_num)) (b19 23 (by norm_num))
        (b17 25 (by norm_num)) (b19 25 (by norm_num))]
    linear_combination -hu1
  have hu2val : env.get (i₀ + 29 + 22 + 2) = ((X1 26 + 4 * X1 28 : ℕ) : F p) := by
    rw [hX1hi 26 (by norm_num) (by norm_num), hX1hi 28 (by norm_num) (by norm_num),
      ← SigmaSum.pair_val4 (b17 26 (by norm_num)) (b19 26 (by norm_num))
        (b17 28 (by norm_num)) (b19 28 (by norm_num))]
    linear_combination -hu2
  have hu3val : env.get (i₀ + 29 + 22 + 3) = ((X1 27 + 4 * X1 29 : ℕ) : F p) := by
    rw [hX1hi 27 (by norm_num) (by norm_num), hX1hi 29 (by norm_num) (by norm_num),
      ← SigmaSum.pair_val4 (b17 27 (by norm_num)) (b19 27 (by norm_num))
        (b17 29 (by norm_num)) (b19 29 (by norm_num))]
    linear_combination -hu3
  have hu4val : env.get (i₀ + 29 + 22 + 4) = ((X1 30 + X0 30 : ℕ) : F p) := by
    rw [hX1hi 30 (by norm_num) (by norm_num), hX0hi 30 (by norm_num) (by norm_num),
      ← SigmaSum.pair_val1 (b17 30 (by norm_num)) (b19 30 (by norm_num))
        (b7 30 (by norm_num)) (b18 30 (by norm_num))]
    linear_combination -hu4
  have hu5val : env.get (i₀ + 29 + 22 + 5) = ((X1 31 + X0 31 : ℕ) : F p) := by
    rw [hX1hi 31 (by norm_num) (by norm_num), hX0hi 31 (by norm_num) (by norm_num),
      ← SigmaSum.pair_val1 (b17 31 (by norm_num)) (b19 31 (by norm_num))
        (b7 31 (by norm_num)) (b18 31 (by norm_num))]
    linear_combination -hu5
  have hvval : env.get (i₀ + 29 + 22 + 6) = ((X0 29 : ℕ) : F p) := by
    rw [hX0hi 29 (by norm_num) (by norm_num),
      ← SigmaSum.xor2_cast (b7 29 (by norm_num)) (b18 29 (by norm_num))]
    linear_combination hv
  -- The packed column vector and its values
  set s0v : Var (fields 29) (F p) :=
    Vector.mapRange 29 (fun i => (var { index := i₀ + i } : Expression (F p))) with hs0v
  set s1v : Var (fields 22) (F p) :=
    Vector.mapRange 22 (fun i => (var { index := i₀ + 29 + i } : Expression (F p))) with hs1v
  set uv : Var (fields 6) (F p) :=
    Vector.mapRange 6 (fun i => (var { index := i₀ + 29 + 22 + i } : Expression (F p))) with huv
  set tv := SigmaSum.tVec s0v s1v uv (var { index := i₀ + 29 + 22 + 6 }) with htv
  set TW := Vector.map (Expression.eval env) tv with hTW
  have hTWv : ∀ (j : ℕ) (hj : j < 32),
      SigmaSum.bitsFn TW j = (Expression.eval env (tv[j]'hj)).val := by
    intro j hj
    rw [SigmaSum.bitsFn_lt hj, hTW, Vector.getElem_map]
  have hlow : ∀ j, j < 22 → SigmaSum.bitsFn TW j = X0 j + X1 j := by
    intro j hj
    rw [hTWv j (by omega), htv, SigmaSum.tVec_get_low s0v s1v uv _ j hj, hs0v, hs1v]
    rw [Vector.getElem_mapRange, Vector.getElem_mapRange]
    show (env.get (i₀ + j) + env.get (i₀ + 29 + j)).val = X0 j + X1 j
    rw [hs0val j (by omega), hs1val j hj, ← Nat.cast_add]
    exact SigmaSum.val_cast_small _
      (by have h0 := hX0le j; have h1 := hX1le j; omega)
  have h22 : SigmaSum.bitsFn TW 22 = X0 22 + (X1 22 + 4 * X1 24) := by
    rw [hTWv 22 (by norm_num), htv, SigmaSum.tVec_get_22, hs0v, huv]
    rw [Vector.getElem_mapRange, Vector.getElem_mapRange]
    show (env.get (i₀ + 22) + env.get (i₀ + 29 + 22)).val = _
    rw [hs0val 22 (by norm_num), hu0val, ← Nat.cast_add]
    exact SigmaSum.val_cast_small _
      (by have h0 := hX0le 22; have h1 := hX1le 22; have h2 := hX1le 24; omega)
  have h23 : SigmaSum.bitsFn TW 23 = X0 23 + (X1 23 + 4 * X1 25) := by
    rw [hTWv 23 (by norm_num), htv, SigmaSum.tVec_get_23, hs0v, huv]
    rw [Vector.getElem_mapRange, Vector.getElem_mapRange]
    show (env.get (i₀ + 23) + env.get (i₀ + 29 + 22 + 1)).val = _
    rw [hs0val 23 (by norm_num), hu1val, ← Nat.cast_add]
    exact SigmaSum.val_cast_small _
      (by have h0 := hX0le 23; have h1 := hX1le 23; have h2 := hX1le 25; omega)
  have h24 : SigmaSum.bitsFn TW 24 = X0 24 := by
    rw [hTWv 24 (by norm_num), htv, SigmaSum.tVec_get_24, hs0v]
    rw [Vector.getElem_mapRange]
    show (env.get (i₀ + 24)).val = _
    rw [hs0val 24 (by norm_num)]
    exact SigmaSum.val_cast_small _ (by have h0 := hX0le 24; omega)
  have h25 : SigmaSum.bitsFn TW 25 = X0 25 := by
    rw [hTWv 25 (by norm_num), htv, SigmaSum.tVec_get_25, hs0v]
    rw [Vector.getElem_mapRange]
    show (env.get (i₀ + 25)).val = _
    rw [hs0val 25 (by norm_num)]
    exact SigmaSum.val_cast_small _ (by have h0 := hX0le 25; omega)
  have h26 : SigmaSum.bitsFn TW 26 = X0 26 + (X1 26 + 4 * X1 28) := by
    rw [hTWv 26 (by norm_num), htv, SigmaSum.tVec_get_26, hs0v, huv]
    rw [Vector.getElem_mapRange, Vector.getElem_mapRange]
    show (env.get (i₀ + 26) + env.get (i₀ + 29 + 22 + 2)).val = _
    rw [hs0val 26 (by norm_num), hu2val, ← Nat.cast_add]
    exact SigmaSum.val_cast_small _
      (by have h0 := hX0le 26; have h1 := hX1le 26; have h2 := hX1le 28; omega)
  have h27 : SigmaSum.bitsFn TW 27 = X0 27 + (X1 27 + 4 * X1 29) := by
    rw [hTWv 27 (by norm_num), htv, SigmaSum.tVec_get_27, hs0v, huv]
    rw [Vector.getElem_mapRange, Vector.getElem_mapRange]
    show (env.get (i₀ + 27) + env.get (i₀ + 29 + 22 + 3)).val = _
    rw [hs0val 27 (by norm_num), hu3val, ← Nat.cast_add]
    exact SigmaSum.val_cast_small _
      (by have h0 := hX0le 27; have h1 := hX1le 27; have h2 := hX1le 29; omega)
  have h28 : SigmaSum.bitsFn TW 28 = X0 28 := by
    rw [hTWv 28 (by norm_num), htv, SigmaSum.tVec_get_28, hs0v]
    rw [Vector.getElem_mapRange]
    show (env.get (i₀ + 28)).val = _
    rw [hs0val 28 (by norm_num)]
    exact SigmaSum.val_cast_small _ (by have h0 := hX0le 28; omega)
  have h29 : SigmaSum.bitsFn TW 29 = X0 29 := by
    rw [hTWv 29 (by norm_num), htv, SigmaSum.tVec_get_29]
    show (env.get (i₀ + 29 + 22 + 6)).val = _
    rw [hvval]
    exact SigmaSum.val_cast_small _ (by have h0 := hX0le 29; omega)
  have h30 : SigmaSum.bitsFn TW 30 = X1 30 + X0 30 := by
    rw [hTWv 30 (by norm_num), htv, SigmaSum.tVec_get_30, huv]
    rw [Vector.getElem_mapRange]
    show (env.get (i₀ + 29 + 22 + 4)).val = _
    rw [hu4val]
    exact SigmaSum.val_cast_small _
      (by have h0 := hX0le 30; have h1 := hX1le 30; omega)
  have h31 : SigmaSum.bitsFn TW 31 = X1 31 + X0 31 := by
    rw [hTWv 31 (by norm_num), htv, SigmaSum.tVec_get_31, huv]
    rw [Vector.getElem_mapRange]
    show (env.get (i₀ + 29 + 22 + 5)).val = _
    rw [hu5val]
    exact SigmaSum.val_cast_small _
      (by have h0 := hX0le 31; have h1 := hX1le 31; omega)
  -- Regroup the packed column values into the two σ bit-columns
  have hNsplit : valueBits TW
      = (∑ j ∈ Finset.range 32, X0 j * 2^j) + (∑ j ∈ Finset.range 32, X1 j * 2^j) := by
    rw [SigmaSum.valueBits_eq_range]
    exact SigmaSum.regroup_sum (SigmaSum.bitsFn TW) X0 X1
      hlow h22 h23 h24 h25 h26 h27 h28 h29 h30 h31
  -- Bridge the σ bit-columns to the spec sigmas
  have hsig0 : (∑ j ∈ Finset.range 32, X0 j * 2^j)
      = Specs.SHA256.lowerSigma0 (valueBits input_wm15) := by
    simp only [hX0]
    rw [SigmaSum.range_xor3_sum r7 r18 s3 nr7 nr18 ns3, hr7, hr18, hs3,
      valueBits_eval_rotr32 env input_var_wm15 input_wm15 h_i15 h_m15 7,
      valueBits_eval_rotr32 env input_var_wm15 input_wm15 h_i15 h_m15 18,
      valueBits_eval_shr32 env input_var_wm15 input_wm15 h_i15 h_m15 3]
    rfl
  have hsig1 : (∑ j ∈ Finset.range 32, X1 j * 2^j)
      = Specs.SHA256.lowerSigma1 (valueBits input_wm2) := by
    simp only [hX1]
    rw [SigmaSum.range_xor3_sum r17 r19 s10 nr17 nr19 ns10, hr17, hr19, hs10,
      valueBits_eval_rotr32 env input_var_wm2 input_wm2 h_i2 h_m2 17,
      valueBits_eval_rotr32 env input_var_wm2 input_wm2 h_i2 h_m2 19,
      valueBits_eval_shr32 env input_var_wm2 input_wm2 h_i2 h_m2 10]
    rfl
  -- Output word: booleanity and value
  rw [Add32.z_var_eval env (i₀ + 29 + 22 + 6 + 1)]
  have h_z_norm := Add32.normalized_of_bool_holds env (i₀ + 29 + 22 + 6 + 1) h_zb
  refine ⟨?_, h_z_norm⟩
  -- Field-level names for the fused-row atoms
  set A7 := Expression.eval env (fromBitsExpr input_var_wm7) with hA7
  set A16 := Expression.eval env (fromBitsExpr input_var_wm16) with hA16
  set At := Expression.eval env (fromBitsExpr tv) with hAt
  set Az := Expression.eval env (fromBitsExpr
    (Vector.mapRange 32 fun i => (var { index := i₀ + 29 + 22 + 6 + 1 + i } : Expression (F p)))) with hAz
  set C1 := env.get (i₀ + 29 + 22 + 6 + 1 + 32) with hC1
  set vz := valueBits (Vector.ofFn fun i : Fin 32 => env.get (i₀ + 29 + 22 + 6 + 1 + i.val)) with hvz
  have h_w7 : A7 = ((valueBits input_wm7 : ℕ) : F p) := by
    rw [hA7]; exact Add32.fromBitsExpr_eval_normalized env input_var_wm7 input_wm7 h_i7
  have h_w16 : A16 = ((valueBits input_wm16 : ℕ) : F p) := by
    rw [hA16]; exact Add32.fromBitsExpr_eval_normalized env input_var_wm16 input_wm16 h_i16
  have h_t : At = ((valueBits TW : ℕ) : F p) := by
    rw [hAt]; exact Add32.fromBitsExpr_eval_normalized env tv TW hTW.symm
  have h_z : Az = ((vz : ℕ) : F p) := by
    rw [hAz, hvz]
    exact Add32.fromBitsExpr_eval_normalized env _ _
      (Add32.z_var_eval env (i₀ + 29 + 22 + 6 + 1))
  -- ℕ-level bounds
  have hp_big : (2:ℕ)^35 < p := Fact.out
  have hp32 : (2:ℕ)^32 < p :=
    lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (by norm_num)) hp_big
  have h_pow32_ne : (2^32 : F p) ≠ 0 := by
    intro hz
    have hval : (2^32 : F p).val = 2^32 := by
      rw [show (2^32 : F p) = ((2^32 : ℕ) : F p) from by push_cast; ring,
        ZMod.val_natCast_of_lt hp32]
    rw [hz, ZMod.val_zero] at hval
    norm_num at hval
  have hinv : (2^32 : F p) * (2^32 : F p)⁻¹ = 1 := mul_inv_cancel₀ h_pow32_ne
  have h_c1_le : C1.val ≤ 1 := by
    rcases IsBool.val_of_IsBool (Add32.isbool_of_bool_constraint h_c1b) with hh | hh <;> omega
  have hC1cast : C1 = ((C1.val : ℕ) : F p) := (ZMod.natCast_rightInverse C1).symm
  have hvz_lt : vz < 2^32 := valueBits_lt_two_pow _ h_z_norm
  have hb0 : (∑ j ∈ Finset.range 32, X0 j * 2^j) < 2^32 :=
    SigmaSum.range_sum_bool_lt X0 (fun j _ => hX0le j)
  have hb1 : (∑ j ∈ Finset.range 32, X1 j * 2^j) < 2^32 :=
    SigmaSum.range_sum_bool_lt X1 (fun j _ => hX1le j)
  have hw7_lt : valueBits input_wm7 < 2^32 := valueBits_lt_two_pow input_wm7 h_m7
  have hw16_lt : valueBits input_wm16 < 2^32 := valueBits_lt_two_pow input_wm16 h_m16
  have hS_lt : valueBits input_wm7 + valueBits input_wm16 + valueBits TW < 2^34 := by omega
  have hS_lt_p : valueBits input_wm7 + valueBits input_wm16 + valueBits TW < p :=
    lt_trans hS_lt (lt_trans (by norm_num) hp_big)
  rcases mul_eq_zero.mp h_e0 with h0 | h1
  · -- low carry bit = 0
    have key : A7 + A16 + At - Az = (2^32 : F p) * (2 * C1) := by
      linear_combination (2^32 : F p) * h0 - (A7 + A16 + At - Az) * hinv
    rw [h_w7, h_w16, h_t, h_z] at key
    have hlin : ((valueBits input_wm7 + valueBits input_wm16 + valueBits TW : ℕ) : F p)
        = ((vz + 2^32 * (2 * C1.val) : ℕ) : F p) := by
      push_cast
      linear_combination key + ((2^32 : F p) * 2) * hC1cast
    have h_rhs_lt : vz + 2^32 * (2 * C1.val) < p := by
      have h34 : vz + 2^32 * (2 * C1.val) < 2^34 := by omega
      exact lt_trans h34 (lt_trans (by norm_num) hp_big)
    have h_nat : valueBits input_wm7 + valueBits input_wm16 + valueBits TW
        = vz + 2^32 * (2 * C1.val) := by
      have hval := congr_arg ZMod.val hlin
      rwa [ZMod.val_natCast_of_lt hS_lt_p, ZMod.val_natCast_of_lt h_rhs_lt] at hval
    rw [hNsplit, hsig0, hsig1] at h_nat
    unfold _root_.add32
    omega
  · -- low carry bit = 1
    have key : A7 + A16 + At - Az = (2^32 : F p) * (1 + 2 * C1) := by
      linear_combination (2^32 : F p) * h1 - (A7 + A16 + At - Az) * hinv
    rw [h_w7, h_w16, h_t, h_z] at key
    have hlin : ((valueBits input_wm7 + valueBits input_wm16 + valueBits TW : ℕ) : F p)
        = ((vz + 2^32 * (1 + 2 * C1.val) : ℕ) : F p) := by
      push_cast
      linear_combination key + ((2^32 : F p) * 2) * hC1cast
    have h_rhs_lt : vz + 2^32 * (1 + 2 * C1.val) < p := by
      have h34 : vz + 2^32 * (1 + 2 * C1.val) < 2^34 := by omega
      exact lt_trans h34 (lt_trans (by norm_num) hp_big)
    have h_nat : valueBits input_wm7 + valueBits input_wm16 + valueBits TW
        = vz + 2^32 * (1 + 2 * C1.val) := by
      have hval := congr_arg ZMod.val hlin
      rwa [ZMod.val_natCast_of_lt hS_lt_p, ZMod.val_natCast_of_lt h_rhs_lt] at hval
    rw [hNsplit, hsig0, hsig1] at h_nat
    unfold _root_.add32
    omega

set_option maxHeartbeats 4000000 in
theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [main]
  obtain ⟨h_m2, h_m7, h_m15, h_m16⟩ := h_assumptions
  obtain ⟨h_i2, h_i7, h_i15, h_i16⟩ := h_input
  obtain ⟨h_es0, h_es1, h_eu, h_ev, h_ez, h_ec1, -, -⟩ := h_env
  -- Booleanity of the row atoms
  have b7c : ∀ (j : ℕ) (hj : j < 32),
      IsBool (Expression.eval env.toEnvironment ((rotr32 7 input_var_wm15)[j]'hj)) := by
    intro j hj
    have h := Normalized_eval_rotr32 env.toEnvironment input_var_wm15 input_wm15 h_i15 h_m15 7 ⟨j, hj⟩
    rwa [Fin.getElem_fin, Vector.getElem_map] at h
  have b18c : ∀ (j : ℕ) (hj : j < 32),
      IsBool (Expression.eval env.toEnvironment ((rotr32 18 input_var_wm15)[j]'hj)) := by
    intro j hj
    have h := Normalized_eval_rotr32 env.toEnvironment input_var_wm15 input_wm15 h_i15 h_m15 18 ⟨j, hj⟩
    rwa [Fin.getElem_fin, Vector.getElem_map] at h
  have b17c : ∀ (j : ℕ) (hj : j < 32),
      IsBool (Expression.eval env.toEnvironment ((rotr32 17 input_var_wm2)[j]'hj)) := by
    intro j hj
    have h := Normalized_eval_rotr32 env.toEnvironment input_var_wm2 input_wm2 h_i2 h_m2 17 ⟨j, hj⟩
    rwa [Fin.getElem_fin, Vector.getElem_map] at h
  have b19c : ∀ (j : ℕ) (hj : j < 32),
      IsBool (Expression.eval env.toEnvironment ((rotr32 19 input_var_wm2)[j]'hj)) := by
    intro j hj
    have h := Normalized_eval_rotr32 env.toEnvironment input_var_wm2 input_wm2 h_i2 h_m2 19 ⟨j, hj⟩
    rwa [Fin.getElem_fin, Vector.getElem_map] at h
  have e15c : ∀ (k : ℕ) (hk : k < 32),
      Expression.eval env.toEnvironment (input_var_wm15[k]'hk) = input_wm15[k]'hk := by
    intro k hk
    have h := Vector.ext_iff.mp h_i15 k hk
    rwa [Vector.getElem_map] at h
  have e2c : ∀ (k : ℕ) (hk : k < 32),
      Expression.eval env.toEnvironment (input_var_wm2[k]'hk) = input_wm2[k]'hk := by
    intro k hk
    have h := Vector.ext_iff.mp h_i2 k hk
    rwa [Vector.getElem_map] at h
  have m15b : ∀ (k : ℕ) (hk : k < 32), IsBool (input_wm15[k]'hk) := by
    intro k hk
    have h := h_m15 ⟨k, hk⟩
    rwa [Fin.getElem_fin] at h
  have m2b : ∀ (k : ℕ) (hk : k < 32), IsBool (input_wm2[k]'hk) := by
    intro k hk
    have h := h_m2 ⟨k, hk⟩
    rwa [Fin.getElem_fin] at h
  -- Lane values in row-atom form
  have hl0 : ∀ (j : ℕ) (hj : j < 29), SigmaSum.lane0 env input_var_wm15 j
      = (Expression.eval env.toEnvironment ((rotr32 7 input_var_wm15)[j]'(by omega))).val
        ^^^ (Expression.eval env.toEnvironment ((rotr32 18 input_var_wm15)[j]'(by omega))).val
        ^^^ (input_wm15[j + 3]'(by omega)).val := by
    intro j hj
    unfold SigmaSum.lane0
    rw [dif_pos (show j < 32 by omega)]
    have h := eval_shr32 env.toEnvironment input_var_wm15 input_wm15 h_i15 3 ⟨j, by omega⟩
    simp only [show (3 : Fin 32).val = 3 from rfl] at h
    rw [h, dif_pos (show j + 3 < 32 by omega)]
  have hl1 : ∀ (j : ℕ) (hj : j < 22), SigmaSum.lane1 env input_var_wm2 j
      = (Expression.eval env.toEnvironment ((rotr32 17 input_var_wm2)[j]'(by omega))).val
        ^^^ (Expression.eval env.toEnvironment ((rotr32 19 input_var_wm2)[j]'(by omega))).val
        ^^^ (input_wm2[j + 10]'(by omega)).val := by
    intro j hj
    unfold SigmaSum.lane1
    rw [dif_pos (show j < 32 by omega)]
    have h := eval_shr32 env.toEnvironment input_var_wm2 input_wm2 h_i2 10 ⟨j, by omega⟩
    simp only [show (10 : Fin 32).val = 10 from rfl] at h
    rw [h, dif_pos (show j + 10 < 32 by omega)]
  -- Witness values, ℕ-indexed
  have hs0g : ∀ (j : ℕ) (hj : j < 29),
      env.get (i₀ + j) = ((SigmaSum.lane0 env input_var_wm15 j : ℕ) : F p) := by
    intro j hj
    have h := h_es0 ⟨j, hj⟩
    rwa [Vector.getElem_ofFn] at h
  have hs1g : ∀ (j : ℕ) (hj : j < 22),
      env.get (i₀ + 29 + j) = ((SigmaSum.lane1 env input_var_wm2 j : ℕ) : F p) := by
    intro j hj
    have h := h_es1 ⟨j, hj⟩
    rwa [Vector.getElem_ofFn] at h
  have hu0g : env.get (i₀ + 29 + 22)
      = ((SigmaSum.lane1 env input_var_wm2 22 + 4 * SigmaSum.lane1 env input_var_wm2 24 : ℕ) : F p) :=
    h_eu ⟨0, by norm_num⟩
  have hu1g : env.get (i₀ + 29 + 22 + 1)
      = ((SigmaSum.lane1 env input_var_wm2 23 + 4 * SigmaSum.lane1 env input_var_wm2 25 : ℕ) : F p) :=
    h_eu ⟨1, by norm_num⟩
  have hu2g : env.get (i₀ + 29 + 22 + 2)
      = ((SigmaSum.lane1 env input_var_wm2 26 + 4 * SigmaSum.lane1 env input_var_wm2 28 : ℕ) : F p) :=
    h_eu ⟨2, by norm_num⟩
  have hu3g : env.get (i₀ + 29 + 22 + 3)
      = ((SigmaSum.lane1 env input_var_wm2 27 + 4 * SigmaSum.lane1 env input_var_wm2 29 : ℕ) : F p) :=
    h_eu ⟨3, by norm_num⟩
  have hu4g : env.get (i₀ + 29 + 22 + 4)
      = ((SigmaSum.lane1 env input_var_wm2 30 + SigmaSum.lane0 env input_var_wm15 30 : ℕ) : F p) :=
    h_eu ⟨4, by norm_num⟩
  have hu5g : env.get (i₀ + 29 + 22 + 5)
      = ((SigmaSum.lane1 env input_var_wm2 31 + SigmaSum.lane0 env input_var_wm15 31 : ℕ) : F p) :=
    h_eu ⟨5, by norm_num⟩
  -- lane bounds
  have hl0le : ∀ j, SigmaSum.lane0 env input_var_wm15 j ≤ 1 :=
    SigmaSum.lane0_le_one env h_i15 h_m15
  have hl1le : ∀ j, SigmaSum.lane1 env input_var_wm2 j ≤ 1 :=
    SigmaSum.lane1_le_one env h_i2 h_m2
  -- The ℕ sum and its bound
  set S := SigmaSum.schedSumNat env input_var_wm2 input_var_wm7 input_var_wm15 input_var_wm16
    with hSdef
  have hw7 : evalBitsNat env input_var_wm7 = valueBits input_wm7 :=
    Add32.evalBitsNat_eq_valueBits env _ _ h_i7
  have hw16 : evalBitsNat env input_var_wm16 = valueBits input_wm16 :=
    Add32.evalBitsNat_eq_valueBits env _ _ h_i16
  have hsig0lt : (∑ j ∈ Finset.range 32, SigmaSum.lane0 env input_var_wm15 j * 2^j) < 2^32 :=
    SigmaSum.range_sum_bool_lt _ (fun j _ => hl0le j)
  have hsig1lt : (∑ j ∈ Finset.range 32, SigmaSum.lane1 env input_var_wm2 j * 2^j) < 2^32 :=
    SigmaSum.range_sum_bool_lt _ (fun j _ => hl1le j)
  have hSsum : S = (∑ j ∈ Finset.range 32, SigmaSum.lane1 env input_var_wm2 j * 2^j)
      + valueBits input_wm7 + (∑ j ∈ Finset.range 32, SigmaSum.lane0 env input_var_wm15 j * 2^j)
      + valueBits input_wm16 := by
    rw [hSdef]
    unfold SigmaSum.schedSumNat
    rw [hw7, hw16]
  have hSbound : S < 2^34 := by
    have hb7 := valueBits_lt_two_pow input_wm7 h_m7
    have hb16 := valueBits_lt_two_pow input_wm16 h_m16
    omega
  have h_div_lt : S / 2^32 < 2^2 := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2^32)]
    calc S < 2^34 := hSbound
      _ = 2^2 * 2^32 := by norm_num
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- σ₀ 3-input rows
    intro i
    rw [hs0g i.val i.isLt, hl0 i.val i.isLt, e15c (i.val + 3) (by omega)]
    rcases b7c i.val (by omega) with h1 | h1 <;> rcases b18c i.val (by omega) with h2 | h2 <;>
      rcases m15b (i.val + 3) (by omega) with h3 | h3 <;>
      simp only [h1, h2, h3, ZMod.val_zero, ZMod.val_one] <;> push_cast <;> ring
  · -- σ₁ 3-input rows
    intro i
    rw [hs1g i.val i.isLt, hl1 i.val i.isLt, e2c (i.val + 10) (by omega)]
    rcases b17c i.val (by omega) with h1 | h1 <;> rcases b19c i.val (by omega) with h2 | h2 <;>
      rcases m2b (i.val + 10) (by omega) with h3 | h3 <;>
      simp only [h1, h2, h3, ZMod.val_zero, ZMod.val_one] <;> push_cast <;> ring
  · -- pair row u₀
    rw [hu0g, SigmaSum.lane1_hi env input_var_wm2 22 (by norm_num) (by norm_num),
      SigmaSum.lane1_hi env input_var_wm2 24 (by norm_num) (by norm_num)]
    linear_combination SigmaSum.pair_val4 (b17c 22 (by norm_num)) (b19c 22 (by norm_num))
      (b17c 24 (by norm_num)) (b19c 24 (by norm_num))
  · -- pair row u₁
    rw [hu1g, SigmaSum.lane1_hi env input_var_wm2 23 (by norm_num) (by norm_num),
      SigmaSum.lane1_hi env input_var_wm2 25 (by norm_num) (by norm_num)]
    linear_combination SigmaSum.pair_val4 (b17c 23 (by norm_num)) (b19c 23 (by norm_num))
      (b17c 25 (by norm_num)) (b19c 25 (by norm_num))
  · -- pair row u₂
    rw [hu2g, SigmaSum.lane1_hi env input_var_wm2 26 (by norm_num) (by norm_num),
      SigmaSum.lane1_hi env input_var_wm2 28 (by norm_num) (by norm_num)]
    linear_combination SigmaSum.pair_val4 (b17c 26 (by norm_num)) (b19c 26 (by norm_num))
      (b17c 28 (by norm_num)) (b19c 28 (by norm_num))
  · -- pair row u₃
    rw [hu3g, SigmaSum.lane1_hi env input_var_wm2 27 (by norm_num) (by norm_num),
      SigmaSum.lane1_hi env input_var_wm2 29 (by norm_num) (by norm_num)]
    linear_combination SigmaSum.pair_val4 (b17c 27 (by norm_num)) (b19c 27 (by norm_num))
      (b17c 29 (by norm_num)) (b19c 29 (by norm_num))
  · -- pair row u₄
    rw [hu4g, SigmaSum.lane1_hi env input_var_wm2 30 (by norm_num) (by norm_num),
      SigmaSum.lane0_hi env input_var_wm15 30 (by norm_num) (by norm_num)]
    linear_combination SigmaSum.pair_val1 (b17c 30 (by norm_num)) (b19c 30 (by norm_num))
      (b7c 30 (by norm_num)) (b18c 30 (by norm_num))
  · -- pair row u₅
    rw [hu5g, SigmaSum.lane1_hi env input_var_wm2 31 (by norm_num) (by norm_num),
      SigmaSum.lane0_hi env input_var_wm15 31 (by norm_num) (by norm_num)]
    linear_combination SigmaSum.pair_val1 (b17c 31 (by norm_num)) (b19c 31 (by norm_num))
      (b7c 31 (by norm_num)) (b18c 31 (by norm_num))
  · -- σ₀ lane 29 determined row
    rw [h_ev, SigmaSum.lane0_hi env input_var_wm15 29 (by norm_num) (by norm_num)]
    linear_combination -SigmaSum.xor2_cast (b7c 29 (by norm_num)) (b18c 29 (by norm_num))
  · -- output bit booleanity
    intro i
    have h := h_ez i
    simp only [Vector.getElem_ofFn] at h
    rw [h]
    rcases Nat.mod_two_eq_zero_or_one (S % 2^32 / 2^i.val) with h0 | h0 <;>
      rw [h0] <;> push_cast <;> ring
  · -- high carry booleanity
    rw [h_ec1]
    rcases Nat.mod_two_eq_zero_or_one (S / 2^32 / 2) with h0 | h0 <;>
      rw [h0] <;> push_cast <;> ring
  · -- fused low-carry booleanity + recomposition row
    have hp_big : (2:ℕ)^35 < p := Fact.out
    have hp32 : (2:ℕ)^32 < p :=
      lt_of_le_of_lt (Nat.pow_le_pow_right (by norm_num) (by norm_num)) hp_big
    -- named atoms
    set s0v : Var (fields 29) (F p) :=
      Vector.mapRange 29 (fun i => (var { index := i₀ + i } : Expression (F p))) with hs0v
    set s1v : Var (fields 22) (F p) :=
      Vector.mapRange 22 (fun i => (var { index := i₀ + 29 + i } : Expression (F p))) with hs1v
    set uv : Var (fields 6) (F p) :=
      Vector.mapRange 6 (fun i => (var { index := i₀ + 29 + 22 + i } : Expression (F p))) with huv
    set tv := SigmaSum.tVec s0v s1v uv (var { index := i₀ + 29 + 22 + 6 }) with htv
    set TW := Vector.map (Expression.eval env.toEnvironment) tv with hTW
    have hTWv : ∀ (j : ℕ) (hj : j < 32),
        SigmaSum.bitsFn TW j = (Expression.eval env.toEnvironment (tv[j]'hj)).val := by
      intro j hj
      rw [SigmaSum.bitsFn_lt hj, hTW, Vector.getElem_map]
    have hlow : ∀ j, j < 22 → SigmaSum.bitsFn TW j
        = SigmaSum.lane0 env input_var_wm15 j + SigmaSum.lane1 env input_var_wm2 j := by
      intro j hj
      rw [hTWv j (by omega), htv, SigmaSum.tVec_get_low s0v s1v uv _ j hj, hs0v, hs1v]
      rw [Vector.getElem_mapRange, Vector.getElem_mapRange]
      show (env.get (i₀ + j) + env.get (i₀ + 29 + j)).val = _
      rw [hs0g j (by omega), hs1g j hj, ← Nat.cast_add]
      exact SigmaSum.val_cast_small _ (by have := hl0le j; have := hl1le j; omega)
    have h22 : SigmaSum.bitsFn TW 22 = SigmaSum.lane0 env input_var_wm15 22
        + (SigmaSum.lane1 env input_var_wm2 22 + 4 * SigmaSum.lane1 env input_var_wm2 24) := by
      rw [hTWv 22 (by norm_num), htv, SigmaSum.tVec_get_22, hs0v, huv]
      rw [Vector.getElem_mapRange, Vector.getElem_mapRange]
      show (env.get (i₀ + 22) + env.get (i₀ + 29 + 22)).val = _
      rw [hs0g 22 (by norm_num), hu0g, ← Nat.cast_add]
      exact SigmaSum.val_cast_small _
        (by have := hl0le 22; have := hl1le 22; have := hl1le 24; omega)
    have h23 : SigmaSum.bitsFn TW 23 = SigmaSum.lane0 env input_var_wm15 23
        + (SigmaSum.lane1 env input_var_wm2 23 + 4 * SigmaSum.lane1 env input_var_wm2 25) := by
      rw [hTWv 23 (by norm_num), htv, SigmaSum.tVec_get_23, hs0v, huv]
      rw [Vector.getElem_mapRange, Vector.getElem_mapRange]
      show (env.get (i₀ + 23) + env.get (i₀ + 29 + 22 + 1)).val = _
      rw [hs0g 23 (by norm_num), hu1g, ← Nat.cast_add]
      exact SigmaSum.val_cast_small _
        (by have := hl0le 23; have := hl1le 23; have := hl1le 25; omega)
    have h24 : SigmaSum.bitsFn TW 24 = SigmaSum.lane0 env input_var_wm15 24 := by
      rw [hTWv 24 (by norm_num), htv, SigmaSum.tVec_get_24, hs0v]
      rw [Vector.getElem_mapRange]
      show (env.get (i₀ + 24)).val = _
      rw [hs0g 24 (by norm_num)]
      exact SigmaSum.val_cast_small _ (by have := hl0le 24; omega)
    have h25 : SigmaSum.bitsFn TW 25 = SigmaSum.lane0 env input_var_wm15 25 := by
      rw [hTWv 25 (by norm_num), htv, SigmaSum.tVec_get_25, hs0v]
      rw [Vector.getElem_mapRange]
      show (env.get (i₀ + 25)).val = _
      rw [hs0g 25 (by norm_num)]
      exact SigmaSum.val_cast_small _ (by have := hl0le 25; omega)
    have h26 : SigmaSum.bitsFn TW 26 = SigmaSum.lane0 env input_var_wm15 26
        + (SigmaSum.lane1 env input_var_wm2 26 + 4 * SigmaSum.lane1 env input_var_wm2 28) := by
      rw [hTWv 26 (by norm_num), htv, SigmaSum.tVec_get_26, hs0v, huv]
      rw [Vector.getElem_mapRange, Vector.getElem_mapRange]
      show (env.get (i₀ + 26) + env.get (i₀ + 29 + 22 + 2)).val = _
      rw [hs0g 26 (by norm_num), hu2g, ← Nat.cast_add]
      exact SigmaSum.val_cast_small _
        (by have := hl0le 26; have := hl1le 26; have := hl1le 28; omega)
    have h27 : SigmaSum.bitsFn TW 27 = SigmaSum.lane0 env input_var_wm15 27
        + (SigmaSum.lane1 env input_var_wm2 27 + 4 * SigmaSum.lane1 env input_var_wm2 29) := by
      rw [hTWv 27 (by norm_num), htv, SigmaSum.tVec_get_27, hs0v, huv]
      rw [Vector.getElem_mapRange, Vector.getElem_mapRange]
      show (env.get (i₀ + 27) + env.get (i₀ + 29 + 22 + 3)).val = _
      rw [hs0g 27 (by norm_num), hu3g, ← Nat.cast_add]
      exact SigmaSum.val_cast_small _
        (by have := hl0le 27; have := hl1le 27; have := hl1le 29; omega)
    have h28 : SigmaSum.bitsFn TW 28 = SigmaSum.lane0 env input_var_wm15 28 := by
      rw [hTWv 28 (by norm_num), htv, SigmaSum.tVec_get_28, hs0v]
      rw [Vector.getElem_mapRange]
      show (env.get (i₀ + 28)).val = _
      rw [hs0g 28 (by norm_num)]
      exact SigmaSum.val_cast_small _ (by have := hl0le 28; omega)
    have h29 : SigmaSum.bitsFn TW 29 = SigmaSum.lane0 env input_var_wm15 29 := by
      rw [hTWv 29 (by norm_num), htv, SigmaSum.tVec_get_29]
      show (env.get (i₀ + 29 + 22 + 6)).val = _
      rw [h_ev]
      exact SigmaSum.val_cast_small _ (by have := hl0le 29; omega)
    have h30 : SigmaSum.bitsFn TW 30
        = SigmaSum.lane1 env input_var_wm2 30 + SigmaSum.lane0 env input_var_wm15 30 := by
      rw [hTWv 30 (by norm_num), htv, SigmaSum.tVec_get_30, huv]
      rw [Vector.getElem_mapRange]
      show (env.get (i₀ + 29 + 22 + 4)).val = _
      rw [hu4g]
      exact SigmaSum.val_cast_small _ (by have := hl0le 30; have := hl1le 30; omega)
    have h31 : SigmaSum.bitsFn TW 31
        = SigmaSum.lane1 env input_var_wm2 31 + SigmaSum.lane0 env input_var_wm15 31 := by
      rw [hTWv 31 (by norm_num), htv, SigmaSum.tVec_get_31, huv]
      rw [Vector.getElem_mapRange]
      show (env.get (i₀ + 29 + 22 + 5)).val = _
      rw [hu5g]
      exact SigmaSum.val_cast_small _ (by have := hl0le 31; have := hl1le 31; omega)
    have hNsplit : valueBits TW
        = (∑ j ∈ Finset.range 32, SigmaSum.lane0 env input_var_wm15 j * 2^j)
          + (∑ j ∈ Finset.range 32, SigmaSum.lane1 env input_var_wm2 j * 2^j) := by
      rw [SigmaSum.valueBits_eq_range]
      exact SigmaSum.regroup_sum (SigmaSum.bitsFn TW) _ _
        hlow h22 h23 h24 h25 h26 h27 h28 h29 h30 h31
    -- field-level evaluations
    have h_w7e : Expression.eval env.toEnvironment (fromBitsExpr input_var_wm7)
        = ((valueBits input_wm7 : ℕ) : F p) :=
      Add32.fromBitsExpr_eval_normalized env.toEnvironment input_var_wm7 input_wm7 h_i7
    have h_w16e : Expression.eval env.toEnvironment (fromBitsExpr input_var_wm16)
        = ((valueBits input_wm16 : ℕ) : F p) :=
      Add32.fromBitsExpr_eval_normalized env.toEnvironment input_var_wm16 input_wm16 h_i16
    have h_t : Expression.eval env.toEnvironment (fromBitsExpr tv)
        = ((valueBits TW : ℕ) : F p) :=
      Add32.fromBitsExpr_eval_normalized env.toEnvironment tv TW hTW.symm
    have h_S_mod_lt : S % 2^32 < 2^32 := Nat.mod_lt _ (by norm_num)
    have h_z_eval' : Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 32 fun i =>
          (var { index := i₀ + 29 + 22 + 6 + 1 + i } : Expression (F p))) =
        Vector.ofFn fun i : Fin 32 => ((S % 2^32 / 2^i.val % 2 : ℕ) : F p) := by
      rw [Add32.z_var_eval env.toEnvironment (i₀ + 29 + 22 + 6 + 1)]
      ext i hh
      simp only [Vector.getElem_ofFn]
      have h := h_ez ⟨i, hh⟩
      simp only [Vector.getElem_ofFn] at h
      exact h
    have h_fz : Expression.eval env.toEnvironment (fromBitsExpr
        (Vector.mapRange 32 fun i =>
          (var { index := i₀ + 29 + 22 + 6 + 1 + i } : Expression (F p)))) =
        ((S % 2^32 : ℕ) : F p) := by
      show Expression.eval env.toEnvironment (Utils.Bits.fieldFromBitsExpr _) = _
      simp only [Utils.Bits.fieldFromBits_eval]
      rw [h_z_eval']
      exact fieldFromBits_bitdecomp_gen (S % 2^32) 32 h_S_mod_lt
    have h_toS : ((valueBits input_wm7 : ℕ) : F p) + ((valueBits input_wm16 : ℕ) : F p)
        + ((valueBits TW : ℕ) : F p) = ((S : ℕ) : F p) := by
      rw [hSsum, hNsplit]
      push_cast
      ring
    have h_pow32_ne : (2^32 : F p) ≠ 0 := by
      intro hz
      have hval : (2^32 : F p).val = 2^32 := by
        rw [show (2^32 : F p) = ((2^32 : ℕ) : F p) from by push_cast; ring,
          ZMod.val_natCast_of_lt hp32]
      rw [hz, ZMod.val_zero] at hval
      norm_num at hval
    rw [h_w7e, h_w16e, h_t, h_fz, h_ec1, h_toS]
    -- E = 2^-32·(S − S%2^32) − 2·(S/2^32/2 % 2) = (S/2^32) % 2, a boolean
    have hq_id : S % 2^32 + 2^32 * (S / 2^32) = S := Nat.mod_add_div S (2^32)
    have hdiff : ((S : ℕ) : F p) - ((S % 2^32 : ℕ) : F p) =
        (2^32 : F p) * ((S / 2^32 : ℕ) : F p) := by
      have hc := congr_arg (Nat.cast : ℕ → F p) hq_id
      rw [Nat.cast_add, Nat.cast_mul,
        show ((2^32 : ℕ) : F p) = (2^32 : F p) from by push_cast; ring] at hc
      linear_combination -hc
    have hinv : (2^32 : F p)⁻¹ * (((S : ℕ) : F p) - ((S % 2^32 : ℕ) : F p)) =
        ((S / 2^32 : ℕ) : F p) := by
      rw [hdiff, ← mul_assoc, inv_mul_cancel₀ h_pow32_ne, one_mul]
    have hq2 : S / 2^32 % 2 + 2 * (S / 2^32 / 2 % 2) = S / 2^32 := by omega
    have hE : (2^32 : F p)⁻¹ * (((S : ℕ) : F p) + -((S % 2^32 : ℕ) : F p)) +
        -(2 * ((S / 2^32 / 2 % 2 : ℕ) : F p)) = ((S / 2^32 % 2 : ℕ) : F p) := by
      have hc := congr_arg (Nat.cast : ℕ → F p) hq2
      push_cast at hc
      have hsub : (2^32 : F p)⁻¹ * (((S : ℕ) : F p) + -((S % 2^32 : ℕ) : F p)) =
          (2^32 : F p)⁻¹ * (((S : ℕ) : F p) - ((S % 2^32 : ℕ) : F p)) := by ring
      rw [hsub, hinv]
      linear_combination -hc
    rw [show ((2^32 : F p)⁻¹ * (((S : ℕ) : F p) + -((S % 2^32 : ℕ) : F p)) +
        -(2 * ((S / 2^32 / 2 % 2 : ℕ) : F p))) = ((S / 2^32 % 2 : ℕ) : F p) from hE]
    rcases Nat.mod_two_eq_zero_or_one (S / 2^32) with hb | hb <;> rw [hb] <;> norm_num

def circuit : FormalCircuit (F p) Inputs (fields 32) where
  main; elaborated; Assumptions; Spec; soundness; completeness

end ScheduleStep
end Solution.SHA256
end
