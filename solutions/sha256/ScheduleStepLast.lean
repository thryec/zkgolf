import Solution.SHA256.ScheduleStep
import Challenge.Utils.CostR1CS

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^35)]

namespace Solution.SHA256

/-!
# SHA-256 Message-Schedule Step, last words (no output decomposition)

Schedule words `w[62]` and `w[63]` are consumed only as *adder addends*
downstream — never as bit inputs to a sigma. For them the 32-bit output
decomposition of `ScheduleStep` (32 output bits + 1 high carry + 34 rows) is
pure overhead: we assert only the 58 sigma-lane rows and return the raw sum

  σ₁(w[j−2]) + w[j−7] + σ₀(w[j−15]) + w[j−16]

as a single affine field expression (exact ℕ sum, `< 2^34`, no mod). The
downstream adder reduces it mod 2^32 together with its other addends.

Witnesses: 29 (σ₀ lanes 0–28) + 22 (σ₁ lanes 0–21) + 6 (pairs) + 1 (v) = 58;
rows: 29 + 22 + 6 + 1 = 58. The output is a pure affine expression of the lane
witnesses and the `wm7`/`wm16` input bits — no output witnesses at all.
-/

namespace ScheduleStepLast

open ScheduleStep (Inputs)

def main (input : Var Inputs (F p)) : Circuit (F p) (Var field (F p)) := do
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
  -- the raw sum as a single affine expression: no output witnesses
  return fromBitsExpr input.wm7 + fromBitsExpr input.wm16 + fromBitsExpr (SigmaSum.tVec s0 s1 u v)

def Assumptions (input : Inputs (F p)) : Prop :=
  Normalized input.wm2 ∧ Normalized input.wm7 ∧ Normalized input.wm15 ∧ Normalized input.wm16

def Spec (input : Inputs (F p)) (out : field (F p)) : Prop :=
  out.val = Specs.SHA256.lowerSigma1 (valueBits input.wm2) + valueBits input.wm7
      + Specs.SHA256.lowerSigma0 (valueBits input.wm15) + valueBits input.wm16
  ∧ out.val < 2^34

instance elaborated : ElaboratedCircuit (F p) Inputs field main := by
  elaborate_circuit

set_option maxHeartbeats 4000000 in
theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [main]
  obtain ⟨h_m2, h_m7, h_m15, h_m16⟩ := h_assumptions
  obtain ⟨h_i2, h_i7, h_i15, h_i16⟩ := h_input
  obtain ⟨h_s0, h_s1, hu0, hu1, hu2, hu3, hu4, hu5, hv⟩ := h_holds
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
  -- Field-level names for the three affine addends of the output
  set A7 := Expression.eval env (fromBitsExpr input_var_wm7) with hA7
  set A16 := Expression.eval env (fromBitsExpr input_var_wm16) with hA16
  set At := Expression.eval env (fromBitsExpr tv) with hAt
  have h_w7 : A7 = ((valueBits input_wm7 : ℕ) : F p) := by
    rw [hA7]; exact Add32.fromBitsExpr_eval_normalized env input_var_wm7 input_wm7 h_i7
  have h_w16 : A16 = ((valueBits input_wm16 : ℕ) : F p) := by
    rw [hA16]; exact Add32.fromBitsExpr_eval_normalized env input_var_wm16 input_wm16 h_i16
  have h_t : At = ((valueBits TW : ℕ) : F p) := by
    rw [hAt]; exact Add32.fromBitsExpr_eval_normalized env tv TW hTW.symm
  -- ℕ-level bounds
  have hp_big : (2:ℕ)^35 < p := Fact.out
  have hb0 : (∑ j ∈ Finset.range 32, X0 j * 2^j) < 2^32 :=
    SigmaSum.range_sum_bool_lt X0 (fun j _ => hX0le j)
  have hb1 : (∑ j ∈ Finset.range 32, X1 j * 2^j) < 2^32 :=
    SigmaSum.range_sum_bool_lt X1 (fun j _ => hX1le j)
  have hw7_lt : valueBits input_wm7 < 2^32 := valueBits_lt_two_pow input_wm7 h_m7
  have hw16_lt : valueBits input_wm16 < 2^32 := valueBits_lt_two_pow input_wm16 h_m16
  have hS_lt : valueBits input_wm7 + valueBits input_wm16 + valueBits TW < 2^34 := by
    rw [hNsplit]; omega
  have hS_lt_p : valueBits input_wm7 + valueBits input_wm16 + valueBits TW < p :=
    lt_trans hS_lt (lt_trans (by norm_num) hp_big)
  -- The output value is the exact ℕ sum
  have hout : A7 + A16 + At
      = ((valueBits input_wm7 + valueBits input_wm16 + valueBits TW : ℕ) : F p) := by
    rw [h_w7, h_w16, h_t]; push_cast; ring
  have hval : (A7 + A16 + At).val
      = valueBits input_wm7 + valueBits input_wm16 + valueBits TW := by
    rw [hout]; exact ZMod.val_natCast_of_lt hS_lt_p
  refine ⟨?_, ?_⟩
  · rw [hval, hNsplit, hsig0, hsig1]
    omega
  · rw [hval]
    exact hS_lt

set_option maxHeartbeats 4000000 in
theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [main]
  obtain ⟨h_m2, h_m7, h_m15, h_m16⟩ := h_assumptions
  obtain ⟨h_i2, h_i7, h_i15, h_i16⟩ := h_input
  obtain ⟨h_es0, h_es1, h_eu, h_ev, -⟩ := h_env
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
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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

def circuit : FormalCircuit (F p) Inputs field where
  main; elaborated; Assumptions; Spec; soundness; completeness

/-!
## R1CS cost

The gadget allocates exactly 58 witnesses (29 + 22 + 6 + 1) and asserts exactly
58 rows (29 + 22 + 6 + 1); the output is a pure affine expression and is free.
-/

section Cost
open Challenge.CostR1CS

omit [Fact (p > 2^35)] in
theorem costIs_main (input : Var Inputs (F p)) :
    CostIs (main input) ⟨58, 58⟩ :=
  CostIs.bind (CostIs.witnessVector 29 _) fun _ =>
  CostIs.bind (CostIs.witnessVector 22 _) fun _ =>
  CostIs.bind (CostIs.witnessVector 6 _) fun _ =>
  CostIs.bind (CostIs.witnessField _) fun _ =>
  CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ =>
  CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ =>
  CostIs.bind (CostIs.assertZero _) fun _ =>
  CostIs.bind (CostIs.assertZero _) fun _ =>
  CostIs.bind (CostIs.assertZero _) fun _ =>
  CostIs.bind (CostIs.assertZero _) fun _ =>
  CostIs.bind (CostIs.assertZero _) fun _ =>
  CostIs.bind (CostIs.assertZero _) fun _ =>
  CostIs.bind (CostIs.assertZero _) fun _ => CostIs.pure _

end Cost

end ScheduleStepLast
end Solution.SHA256
end
