import Solution.SHA256.SHA256Round
import Solution.SHA256.SHA256RoundsTheorems
import Solution.SHA256.SHA256RoundPair
import Solution.SHA256.AddMany
import Solution.SHA256.Add32
import Solution.SHA256.Ch32
import Solution.SHA256.Maj32
import Solution.SHA256.UpperSigma0
import Solution.SHA256.UpperSigma1
import Challenge.Specs.SHA256

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^35)]

instance fact_p_gt_2_of_2_pow_35 : Fact (p > 2) := .mk (by
  have h : (2 : ℕ) < 2^35 := by decide
  exact h.trans (Fact.out (p := p > 2^35)))

namespace Solution.SHA256

/-!
# SHA-256 Compression: 63-round loop + fused final round + Davies-Meyer

Round 63 (the last of the 64 rounds) is the only round whose `new_a`/`new_e`
outputs are consumed *solely* by the Davies-Meyer feedforward add (there is no
round 64 to consume them as the next round's `a`/`e`). Rather than materialize
round 63's `new_a`/`new_e` as separate reduced 32-bit words (via `AddMany`/
`AddMany.circuit2c`) and then separately `Add32` each against the pre-block
chaining state, round 63 is fused directly with the Davies-Meyer add: the raw
addends of `new_a`/`new_e` are summed together with the corresponding
pre-block chaining word in a single widened `AddMany` call.

This file builds two `FormalCircuit`s:
  * `SHA256Rounds63.circuit` — the first 63 rounds (unchanged per-round shape)
  * `SHA256Rounds.circuit`   — 63 rounds, then the fused final round +
    Davies-Meyer for all 8 words (words 0/4 via the widened `AddMany`, words
    1/2/3/5/6/7 via plain `Add32`)
-/

/-!
## FormalCircuit for the first 63 rounds of compression
-/

namespace SHA256Rounds63

structure Inputs (F : Type) where
  state : SHA256State F
  schedule : SHA256Schedule F
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var SHA256State (F p)) :=
  Circuit.foldlRange 63 input.state (fun s i =>
    SHA256Round.circuit ⟨s,
      constWord32 (Specs.SHA256.K[i.val]'(by have := i.isLt; omega)).toNat,
      input.schedule[i.val]'(by have := i.isLt; omega)⟩)

def Assumptions (input : Inputs (F p)) : Prop :=
  (∀ i : Fin 8, Normalized input.state[i]) ∧
  (∀ i : Fin 64, Normalized input.schedule[i])

def Spec (input : Inputs (F p)) (out : SHA256State (F p)) : Prop :=
  out.map valueBits =
    SHA256Rounds.valStateAfterRound (input.state.map valueBits) (input.schedule.map valueBits) 63
  ∧ ∀ i : Fin 8, Normalized out[i]

/-! The `stateVar` / `valStateAfterRound` descriptions and their `foldl`/spec
bridging lemmas live in `SHA256RoundsTheorems`, under the `SHA256Rounds`
namespace (shared with the 64-round helpers they were originally written for;
both `stateVar` and `valStateAfterRound` are already generic in the round
count). -/

@[reducible]
instance elaborated : ElaboratedCircuit (F p) Inputs SHA256State main := by
  elaborate_circuit_with {
    output input i₀ := SHA256Rounds.stateVar i₀ input.state 63
  } using by
    simp only [circuit_norm]
    intros
    apply SHA256Rounds.fin_foldl_eq_stateVar

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [SHA256Round.Spec, SHA256Round.Assumptions]
  obtain ⟨h_state_norm, h_sched_norm⟩ := h_assumptions
  obtain ⟨h_input_state, h_input_schedule⟩ := h_input
  have h_inv : ∀ (k : ℕ) (_ : k ≤ 63),
      Vector.map valueBits (eval env (SHA256Rounds.stateVar i₀ input_var_state k)) =
        SHA256Rounds.valStateAfterRound (Vector.map valueBits input_state)
          (Vector.map valueBits input_schedule) k ∧
      (∀ (j : ℕ) (hj : j < 8),
        Normalized (eval env ((SHA256Rounds.stateVar i₀ input_var_state k)[j]'hj))) := by
    intro k hk
    induction k with
    | zero =>
      refine ⟨?_, ?_⟩
      · simp only [SHA256Rounds.stateVar, SHA256Rounds.valStateAfterRound]; rw [h_input_state]
      · intro j hj
        simp only [SHA256Rounds.stateVar]
        rw [getElem_eval_vector, h_input_state]
        exact h_state_norm ⟨j, hj⟩
    | succ k ih =>
      have hk' : k ≤ 63 := by omega
      have hk'' : k < 63 := by omega
      obtain ⟨ih_val, ih_norm⟩ := ih hk'
      specialize h_holds ⟨k, hk''⟩
      rw [SHA256Rounds.foldlAcc_eq_stateVar63 i₀ input_var_state input_var_schedule k hk''] at h_holds
      simp only [circuit_norm, SHA256Round.circuit, SHA256Round.elaborated,
        SHA256Round.Spec, SHA256Round.Assumptions] at h_holds
      have h2 : Normalized (Vector.map (Expression.eval env)
          (constWord32 (p:=p) (Specs.SHA256.K[k]'(by omega)).toNat)) :=
        SHA256Rounds.normalized_constWord32 env _
      have h3 : Normalized (Vector.map (Expression.eval env) (input_var_schedule[k]'(by omega))) := by
        rw [show Vector.map (Expression.eval env) (input_var_schedule[k]'(by omega))
              = eval env (input_var_schedule[k]'(by omega)) from (CircuitType.eval_var_fields env _).symm]
        rw [getElem_eval_vector, h_input_schedule]
        exact h_sched_norm ⟨k, by omega⟩
      have h_spec := h_holds ⟨by
        intro i
        have h := ih_norm i.val i.isLt
        rw [getElem_eval_vector] at h
        exact h, h2, h3⟩
      obtain ⟨h_value, h_norm⟩ := h_spec
      rw [SHA256Rounds.stateVar, SHA256Rounds.valStateAfterRound, dif_pos (show k < 64 by omega)]
      refine ⟨?_, ?_⟩
      · rw [h_value, ih_val,
          SHA256Rounds.valueBits_constWord32_of_lt env (Specs.SHA256.K[k]'(by omega)).toNat_lt,
          show Vector.map (Expression.eval env) (input_var_schedule[k]'(by omega))
            = eval env (input_var_schedule[k]'(by omega)) from (CircuitType.eval_var_fields env _).symm,
          getElem_eval_vector, h_input_schedule,
          show (Vector.map valueBits input_schedule)[k]'(by omega)
            = valueBits (input_schedule[k]'(by omega)) from Vector.getElem_map _ _]
      · intro j hj
        rw [getElem_eval_vector]
        exact h_norm ⟨j, hj⟩
  obtain ⟨h_val_63, h_norm_63⟩ := h_inv 63 (le_refl 63)
  refine ⟨⟨h_val_63, ?_⟩, ?_⟩
  · intro i
    rw [← getElem_eval_vector]
    exact h_norm_63 i.val i.isLt
  · intro _
    left; rfl

theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [SHA256Round.Spec, SHA256Round.Assumptions]
  obtain ⟨h_state_norm, h_sched_norm⟩ := h_assumptions
  obtain ⟨h_input_state, h_input_schedule⟩ := h_input
  have h_inv : ∀ (k : ℕ) (_ : k ≤ 63),
      ∀ (j : ℕ) (hj : j < 8),
        Normalized (eval env.toEnvironment ((SHA256Rounds.stateVar i₀ input_var_state k)[j]'hj)) := by
    intro k hk
    induction k with
    | zero =>
      intro j hj
      simp only [SHA256Rounds.stateVar]
      rw [getElem_eval_vector, h_input_state]
      exact h_state_norm ⟨j, hj⟩
    | succ k ih =>
      have hk' : k ≤ 63 := by omega
      have hk'' : k < 63 := by omega
      specialize h_env ⟨k, hk''⟩
      rw [SHA256Rounds.foldlAcc_eq_stateVar63 i₀ input_var_state input_var_schedule k hk''] at h_env
      simp only [circuit_norm, SHA256Round.circuit, SHA256Round.elaborated,
        SHA256Round.Spec, SHA256Round.Assumptions] at h_env
      have h2 : Normalized (Vector.map (Expression.eval env.toEnvironment)
          (constWord32 (p:=p) (Specs.SHA256.K[k]'(by omega)).toNat)) :=
        SHA256Rounds.normalized_constWord32 _ _
      have h3 : Normalized (Vector.map (Expression.eval env.toEnvironment)
          (input_var_schedule[k]'(by omega))) := by
        rw [show Vector.map (Expression.eval env.toEnvironment) (input_var_schedule[k]'(by omega))
              = eval env.toEnvironment (input_var_schedule[k]'(by omega)) from
            (CircuitType.eval_var_fields _ _).symm]
        rw [getElem_eval_vector, h_input_schedule]
        exact h_sched_norm ⟨k, by omega⟩
      have h_spec := h_env ⟨by
        intro i
        have h := ih hk' i.val i.isLt
        rw [getElem_eval_vector] at h
        exact h, h2, h3⟩
      obtain ⟨_, h_norm⟩ := h_spec
      intro j hj
      rw [SHA256Rounds.stateVar]
      rw [getElem_eval_vector]
      exact h_norm ⟨j, hj⟩
  intro i
  refine ⟨?_, ?_, ?_⟩
  · intro j
    have h := h_inv i.val (le_of_lt i.isLt) j.val j.isLt
    rw [← SHA256Rounds.foldlAcc_eq_stateVar63 i₀ input_var_state input_var_schedule i.val i.isLt] at h
    rw [getElem_eval_vector] at h
    have heq : (⟨i.val, i.isLt⟩ : Fin 63) = i := Fin.ext rfl
    rw [heq] at h
    exact h
  · exact SHA256Rounds.normalized_constWord32 _ _
  · rw [show Vector.map (Expression.eval env.toEnvironment) (input_var_schedule[i.val]'(by omega))
          = eval env.toEnvironment (input_var_schedule[i.val]'(by omega)) from
        (CircuitType.eval_var_fields _ _).symm]
    rw [getElem_eval_vector, h_input_schedule]
    exact h_sched_norm ⟨i.val, by omega⟩

def circuit : FormalCircuit (F p) Inputs SHA256State := {
  main, elaborated, Assumptions, Spec, soundness
  completeness := by simp only [completeness]
}

/-!
## 62-round variant (last TWO rounds peeled off for the w62/w63 wide gadgets)

Same `Inputs` (full 64-word schedule); only indices `0..61` are read, so the
assumption on the schedule is weakened to normalization on the first 62 words.
Ported from bufferhe4d's 166,935 submission
(`/Users/simon/Documents/dev/Projects/zk.golf/solutions/sha-bufferhe4d-166935/SHA256Rounds.lean`).
-/

def main62 (input : Var Inputs (F p)) : Circuit (F p) (Var SHA256State (F p)) :=
  Circuit.foldlRange 62 input.state (fun s i =>
    SHA256Round.circuit ⟨s, constWord32 (Specs.SHA256.K[i.val]'(by omega)).toNat,
      input.schedule[i.val]'(by omega)⟩)

def Assumptions62 (input : Inputs (F p)) : Prop :=
  (∀ i : Fin 8, Normalized input.state[i]) ∧
  (∀ i : Fin 64, i.val < 62 → Normalized input.schedule[i])

def Spec62 (input : Inputs (F p)) (out : SHA256State (F p)) : Prop :=
  out.map valueBits =
    SHA256Rounds.valStateAfterRound (input.state.map valueBits) (input.schedule.map valueBits) 62
  ∧ ∀ i : Fin 8, Normalized out[i]

instance elaborated62 : ElaboratedCircuit (F p) Inputs SHA256State main62 := by
  elaborate_circuit_with {
    output input i₀ := SHA256Rounds.stateVar i₀ input.state 62
  } using by
    simp only [circuit_norm]
    intros
    apply SHA256Rounds.fin_foldl_eq_stateVar

theorem soundness62 : Soundness (F p) main62 Assumptions62 Spec62 := by
  circuit_proof_start [SHA256Round.Spec, SHA256Round.Assumptions, main62, Spec62, Assumptions62]
  obtain ⟨h_state_norm, h_sched_norm⟩ := h_assumptions
  obtain ⟨h_input_state, h_input_schedule⟩ := h_input
  have h_inv : ∀ (k : ℕ) (_ : k ≤ 62),
      Vector.map valueBits (eval env (SHA256Rounds.stateVar i₀ input_var_state k)) =
        SHA256Rounds.valStateAfterRound (Vector.map valueBits input_state)
          (Vector.map valueBits input_schedule) k ∧
      (∀ (j : ℕ) (hj : j < 8),
        Normalized (eval env ((SHA256Rounds.stateVar i₀ input_var_state k)[j]'hj))) := by
    intro k hk
    induction k with
    | zero =>
      refine ⟨?_, ?_⟩
      · simp only [SHA256Rounds.stateVar, SHA256Rounds.valStateAfterRound]; rw [h_input_state]
      · intro j hj
        simp only [SHA256Rounds.stateVar]
        rw [getElem_eval_vector, h_input_state]
        exact h_state_norm ⟨j, hj⟩
    | succ k ih =>
      have hk' : k ≤ 62 := by omega
      have hk'' : k < 62 := by omega
      have hk64 : k < 64 := by omega
      obtain ⟨ih_val, ih_norm⟩ := ih hk'
      specialize h_holds ⟨k, hk''⟩
      rw [SHA256Rounds.foldlAcc_eq_stateVar62 i₀ input_var_state input_var_schedule k hk''] at h_holds
      simp only [circuit_norm, SHA256Round.circuit, SHA256Round.elaborated,
        SHA256Round.Spec, SHA256Round.Assumptions] at h_holds
      have h2 : Normalized (Vector.map (Expression.eval env)
          (constWord32 (p:=p) (Specs.SHA256.K[k]'hk64).toNat)) :=
        SHA256Rounds.normalized_constWord32 env _
      have h3 : Normalized (Vector.map (Expression.eval env) (input_var_schedule[k]'hk64)) := by
        rw [show Vector.map (Expression.eval env) (input_var_schedule[k]'hk64)
              = eval env (input_var_schedule[k]'hk64) from (CircuitType.eval_var_fields env _).symm]
        rw [getElem_eval_vector, h_input_schedule]
        exact h_sched_norm ⟨k, hk64⟩ hk''
      have h_spec := h_holds ⟨by
        intro i
        have h := ih_norm i.val i.isLt
        rw [getElem_eval_vector] at h
        exact h, h2, h3⟩
      obtain ⟨h_value, h_norm⟩ := h_spec
      rw [SHA256Rounds.stateVar, SHA256Rounds.valStateAfterRound, dif_pos hk64]
      refine ⟨?_, ?_⟩
      · rw [h_value, ih_val,
          SHA256Rounds.valueBits_constWord32_of_lt env (Specs.SHA256.K[k]'hk64).toNat_lt,
          show Vector.map (Expression.eval env) (input_var_schedule[k]'hk64)
            = eval env (input_var_schedule[k]'hk64) from (CircuitType.eval_var_fields env _).symm,
          getElem_eval_vector, h_input_schedule,
          show (Vector.map valueBits input_schedule)[k]'hk64
            = valueBits (input_schedule[k]'hk64) from Vector.getElem_map _ _]
      · intro j hj
        rw [getElem_eval_vector]
        exact h_norm ⟨j, hj⟩
  obtain ⟨h_val_62, h_norm_62⟩ := h_inv 62 (le_refl 62)
  refine ⟨⟨h_val_62, ?_⟩, ?_⟩
  · intro i
    rw [← getElem_eval_vector]
    exact h_norm_62 i.val i.isLt
  · intro _
    left; rfl

theorem completeness62 : Completeness (F p) main62 Assumptions62 := by
  circuit_proof_start [SHA256Round.Spec, SHA256Round.Assumptions, main62, Assumptions62]
  obtain ⟨h_state_norm, h_sched_norm⟩ := h_assumptions
  obtain ⟨h_input_state, h_input_schedule⟩ := h_input
  have h_inv : ∀ (k : ℕ) (_ : k ≤ 62),
      ∀ (j : ℕ) (hj : j < 8),
        Normalized (eval env.toEnvironment ((SHA256Rounds.stateVar i₀ input_var_state k)[j]'hj)) := by
    intro k hk
    induction k with
    | zero =>
      intro j hj
      simp only [SHA256Rounds.stateVar]
      rw [getElem_eval_vector, h_input_state]
      exact h_state_norm ⟨j, hj⟩
    | succ k ih =>
      have hk' : k ≤ 62 := by omega
      have hk'' : k < 62 := by omega
      have hk64 : k < 64 := by omega
      specialize h_env ⟨k, hk''⟩
      rw [SHA256Rounds.foldlAcc_eq_stateVar62 i₀ input_var_state input_var_schedule k hk''] at h_env
      simp only [circuit_norm, SHA256Round.circuit, SHA256Round.elaborated,
        SHA256Round.Spec, SHA256Round.Assumptions] at h_env
      have h2 : Normalized (Vector.map (Expression.eval env.toEnvironment)
          (constWord32 (p:=p) (Specs.SHA256.K[k]'hk64).toNat)) :=
        SHA256Rounds.normalized_constWord32 _ _
      have h3 : Normalized (Vector.map (Expression.eval env.toEnvironment)
          (input_var_schedule[k]'hk64)) := by
        rw [show Vector.map (Expression.eval env.toEnvironment) (input_var_schedule[k]'hk64)
              = eval env.toEnvironment (input_var_schedule[k]'hk64) from
            (CircuitType.eval_var_fields _ _).symm]
        rw [getElem_eval_vector, h_input_schedule]
        exact h_sched_norm ⟨k, hk64⟩ hk''
      have h_spec := h_env ⟨by
        intro i
        have h := ih hk' i.val i.isLt
        rw [getElem_eval_vector] at h
        exact h, h2, h3⟩
      obtain ⟨_, h_norm⟩ := h_spec
      intro j hj
      rw [SHA256Rounds.stateVar]
      rw [getElem_eval_vector]
      exact h_norm ⟨j, hj⟩
  intro i
  refine ⟨?_, ?_, ?_⟩
  · intro j
    have h := h_inv i.val (le_of_lt i.isLt) j.val j.isLt
    rw [← SHA256Rounds.foldlAcc_eq_stateVar62 i₀ input_var_state input_var_schedule i.val i.isLt] at h
    rw [getElem_eval_vector] at h
    have heq : (⟨i.val, i.isLt⟩ : Fin 62) = i := Fin.ext rfl
    rw [heq] at h
    exact h
  · exact SHA256Rounds.normalized_constWord32 _ _
  · have hi64 : i.val < 64 := by omega
    rw [show Vector.map (Expression.eval env.toEnvironment) (input_var_schedule[i.val]'hi64)
          = eval env.toEnvironment (input_var_schedule[i.val]'hi64) from
        (CircuitType.eval_var_fields _ _).symm]
    rw [getElem_eval_vector, h_input_schedule]
    exact h_sched_norm ⟨i.val, hi64⟩ i.isLt

def circuit62 : FormalCircuit (F p) Inputs SHA256State := {
  main := main62, elaborated := elaborated62, Assumptions := Assumptions62, Spec := Spec62
  soundness := soundness62
  completeness := by simp only [completeness62]
}

/-!
## 62-round variant built from the cross-round paired gadget (Phase-6)

31 pair-steps of `SHA256RoundPair.circuit`, advancing two rounds per step.
Same `Assumptions62`/`Spec62` as `circuit62`; only the witness layout differs
(328 witnesses per pair vs. 2·195 = 390 for two single rounds).
-/

section Paired
variable [Fact (p > 2^76)]

/-- Variable-level state after `k` paired steps (each consumes 328 witnesses).
    The additive offset form mirrors what `circuit_norm` produces for the fold body. -/
def stateVarPaired (i₀ : ℕ) (input_var_state : Var SHA256State (F p)) :
    ℕ → Var SHA256State (F p)
  | 0 => input_var_state
  | k + 1 =>
    let prev := stateVarPaired i₀ input_var_state k
    #v[Vector.mapRange 32 fun j => var { index := i₀ + k * 328 + 128 + 32 + 32 + 32 + j },
       Vector.mapRange 32 fun j => var { index := i₀ + k * 328 + 32 + 32 + 32 + j },
       prev[0], prev[1],
       Vector.mapRange 32 fun j => var { index := i₀ + k * 328 + 128 + 32 + 32 + j },
       Vector.mapRange 32 fun j => var { index := i₀ + k * 328 + 32 + 32 + j },
       prev[4], prev[5]]

omit [Fact (Nat.Prime p)] [Fact (p > 2 ^ 35)] [Fact (p > 2 ^ 76)] in
/-- The `Fin.foldl` over the paired round body equals `stateVarPaired i₀ input_var_state k`. -/
lemma fin_foldl_eq_stateVarPaired (i₀ : ℕ) (input_var_state : Var SHA256State (F p)) (k : ℕ) :
    Fin.foldl k
      (fun (acc : Var SHA256State (F p)) (i : Fin k) =>
        #v[Vector.mapRange 32 fun i_1 => var { index := i₀ + i.val * 328 + 128 + 32 + 32 + 32 + i_1 },
           Vector.mapRange 32 fun i_1 => var { index := i₀ + i.val * 328 + 32 + 32 + 32 + i_1 },
           acc[0], acc[1],
           Vector.mapRange 32 fun i_1 => var { index := i₀ + i.val * 328 + 128 + 32 + 32 + i_1 },
           Vector.mapRange 32 fun i_1 => var { index := i₀ + i.val * 328 + 32 + 32 + i_1 },
           acc[4], acc[5]]) input_var_state =
      stateVarPaired i₀ input_var_state k := by
  induction k with
  | zero => simp [stateVarPaired, Fin.foldl_zero]
  | succ k ih =>
    rw [Fin.foldl_succ_last]
    simp only [Fin.val_last]
    rw [stateVarPaired]
    rw [show Fin.foldl k
        (fun (acc : Var SHA256State (F p)) (i : Fin k) =>
          #v[Vector.mapRange 32 fun i_1 => var { index := i₀ + i.castSucc.val * 328 + 128 + 32 + 32 + 32 + i_1 },
             Vector.mapRange 32 fun i_1 => var { index := i₀ + i.castSucc.val * 328 + 32 + 32 + 32 + i_1 },
             acc[0], acc[1],
             Vector.mapRange 32 fun i_1 => var { index := i₀ + i.castSucc.val * 328 + 128 + 32 + 32 + i_1 },
             Vector.mapRange 32 fun i_1 => var { index := i₀ + i.castSucc.val * 328 + 32 + 32 + i_1 },
             acc[4], acc[5]]) input_var_state =
        Fin.foldl k
          (fun (acc : Var SHA256State (F p)) (i : Fin k) =>
            #v[Vector.mapRange 32 fun i_1 => var { index := i₀ + i.val * 328 + 128 + 32 + 32 + 32 + i_1 },
               Vector.mapRange 32 fun i_1 => var { index := i₀ + i.val * 328 + 32 + 32 + 32 + i_1 },
               acc[0], acc[1],
               Vector.mapRange 32 fun i_1 => var { index := i₀ + i.val * 328 + 128 + 32 + 32 + i_1 },
               Vector.mapRange 32 fun i_1 => var { index := i₀ + i.val * 328 + 32 + 32 + i_1 },
               acc[4], acc[5]]) input_var_state from rfl, ih]

def main62_paired (input : Var Inputs (F p)) : Circuit (F p) (Var SHA256State (F p)) :=
  Circuit.foldlRange 31 input.state (fun s i =>
    SHA256RoundPair.circuit ⟨s,
      constWord32 (Specs.SHA256.K[2*i.val]'(by omega)).toNat, input.schedule[2*i.val]'(by omega),
      constWord32 (Specs.SHA256.K[2*i.val+1]'(by omega)).toNat, input.schedule[2*i.val+1]'(by omega)⟩)

instance elaborated62_paired : ElaboratedCircuit (F p) Inputs SHA256State main62_paired := by
  elaborate_circuit_with {
    output input i₀ := stateVarPaired i₀ input.state 31
  } using by
    simp only [circuit_norm]
    intros
    apply fin_foldl_eq_stateVarPaired

/-- `Circuit.FoldlM.foldlAcc` at index `⟨k, h⟩ : Fin 31` equals `stateVarPaired i₀ input_var_state k`. -/
lemma foldlAcc_eq_stateVarPaired (i₀ : ℕ)
    (input_var_state : SHA256State (Expression (F p)))
    (input_var_schedule : SHA256Schedule (Expression (F p)))
    (k : ℕ) (h : k < 31) :
    Circuit.FoldlM.foldlAcc (β := SHA256State (Expression (F p)))
      i₀ (Vector.finRange 31)
      (fun s (i : Fin 31) => subcircuit SHA256RoundPair.circuit
        { state := s,
          k0 := constWord32 (Specs.SHA256.K[2*i.val]'(by omega)).toNat,
          w0 := input_var_schedule[2*i.val]'(by omega),
          k1 := constWord32 (Specs.SHA256.K[2*i.val+1]'(by omega)).toNat,
          w1 := input_var_schedule[2*i.val+1]'(by omega) })
      input_var_state ⟨k, h⟩ =
        stateVarPaired i₀ input_var_state k := by
  simp only [Circuit.FoldlM.foldlAcc, Vector.getElem_finRange]
  exact fin_foldl_eq_stateVarPaired _ _ _

set_option maxHeartbeats 1000000 in
theorem soundness62_paired : Soundness (F p) main62_paired Assumptions62 Spec62 := by
  circuit_proof_start [SHA256RoundPair.Spec, SHA256RoundPair.Assumptions, main62_paired, Spec62,
    Assumptions62]
  obtain ⟨h_state_norm, h_sched_norm⟩ := h_assumptions
  obtain ⟨h_input_state, h_input_schedule⟩ := h_input
  have h_inv : ∀ (k : ℕ) (_ : k ≤ 31),
      Vector.map valueBits (eval env (stateVarPaired i₀ input_var_state k)) =
        SHA256Rounds.valStateAfterRound (Vector.map valueBits input_state)
          (Vector.map valueBits input_schedule) (2 * k) ∧
      (∀ (j : ℕ) (hj : j < 8),
        Normalized (eval env ((stateVarPaired i₀ input_var_state k)[j]'hj))) := by
    intro k hk
    induction k with
    | zero =>
      refine ⟨?_, ?_⟩
      · simp only [stateVarPaired, SHA256Rounds.valStateAfterRound]; rw [h_input_state]
      · intro j hj
        simp only [stateVarPaired]
        rw [getElem_eval_vector, h_input_state]
        exact h_state_norm ⟨j, hj⟩
    | succ k ih =>
      have hk' : k ≤ 31 := by omega
      have hk'' : k < 31 := by omega
      have hk2 : 2 * k < 64 := by omega
      have hk2' : 2 * k + 1 < 64 := by omega
      obtain ⟨ih_val, ih_norm⟩ := ih hk'
      specialize h_holds ⟨k, hk''⟩
      rw [foldlAcc_eq_stateVarPaired i₀ input_var_state input_var_schedule k hk''] at h_holds
      simp only [circuit_norm, SHA256RoundPair.circuit, SHA256RoundPair.elaborated,
        SHA256RoundPair.Spec, SHA256RoundPair.Assumptions] at h_holds
      have h2a : Normalized (Vector.map (Expression.eval env)
          (constWord32 (p:=p) (Specs.SHA256.K[2*k]'hk2).toNat)) := SHA256Rounds.normalized_constWord32 env _
      have h2b : Normalized (Vector.map (Expression.eval env)
          (constWord32 (p:=p) (Specs.SHA256.K[2*k+1]'hk2').toNat)) := SHA256Rounds.normalized_constWord32 env _
      have h3a : Normalized (Vector.map (Expression.eval env) (input_var_schedule[2*k]'hk2)) := by
        rw [show Vector.map (Expression.eval env) (input_var_schedule[2*k]'hk2)
              = eval env (input_var_schedule[2*k]'hk2) from (CircuitType.eval_var_fields env _).symm]
        rw [getElem_eval_vector, h_input_schedule]
        exact h_sched_norm ⟨2*k, hk2⟩ (by change 2*k < 62; omega)
      have h3b : Normalized (Vector.map (Expression.eval env) (input_var_schedule[2*k+1]'hk2')) := by
        rw [show Vector.map (Expression.eval env) (input_var_schedule[2*k+1]'hk2')
              = eval env (input_var_schedule[2*k+1]'hk2') from (CircuitType.eval_var_fields env _).symm]
        rw [getElem_eval_vector, h_input_schedule]
        exact h_sched_norm ⟨2*k+1, hk2'⟩ (by change 2*k+1 < 62; omega)
      have h_spec := h_holds ⟨by
        intro i
        have h := ih_norm i.val i.isLt
        rw [getElem_eval_vector] at h
        exact h, h2a, h3a, h2b, h3b⟩
      obtain ⟨h_value, h_norm⟩ := h_spec
      rw [stateVarPaired]
      refine ⟨?_, ?_⟩
      · rw [h_value, SHA256RoundPair.specFn_eq, ih_val,
          show 2 * (k + 1) = (2 * k + 1) + 1 from by ring,
          SHA256Rounds.valStateAfterRound_succ _ _ (2*k+1) hk2', SHA256Rounds.valStateAfterRound_succ _ _ (2*k) hk2,
          SHA256Rounds.valueBits_constWord32_of_lt env (Specs.SHA256.K[2*k]'hk2).toNat_lt,
          SHA256Rounds.valueBits_constWord32_of_lt env (Specs.SHA256.K[2*k+1]'hk2').toNat_lt,
          show Vector.map (Expression.eval env) (input_var_schedule[2*k]'hk2)
            = eval env (input_var_schedule[2*k]'hk2) from (CircuitType.eval_var_fields env _).symm,
          show Vector.map (Expression.eval env) (input_var_schedule[2*k+1]'hk2')
            = eval env (input_var_schedule[2*k+1]'hk2') from (CircuitType.eval_var_fields env _).symm,
          getElem_eval_vector, getElem_eval_vector, h_input_schedule,
          show (Vector.map valueBits input_schedule)[2*k]'hk2
            = valueBits (input_schedule[2*k]'hk2) from Vector.getElem_map _ _,
          show (Vector.map valueBits input_schedule)[2*k+1]'hk2'
            = valueBits (input_schedule[2*k+1]'hk2') from Vector.getElem_map _ _]
      · intro j hj
        rw [getElem_eval_vector]
        exact h_norm ⟨j, hj⟩
  obtain ⟨h_val_62, h_norm_62⟩ := h_inv 31 (le_refl 31)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · exact h_val_62
  · intro i
    rw [← getElem_eval_vector]
    exact h_norm_62 i.val i.isLt
  · intro _
    left; rfl

set_option maxHeartbeats 1000000 in
theorem completeness62_paired : Completeness (F p) main62_paired Assumptions62 := by
  circuit_proof_start [SHA256RoundPair.Spec, SHA256RoundPair.Assumptions, main62_paired,
    Assumptions62]
  obtain ⟨h_state_norm, h_sched_norm⟩ := h_assumptions
  obtain ⟨h_input_state, h_input_schedule⟩ := h_input
  have h_inv : ∀ (k : ℕ) (_ : k ≤ 31),
      ∀ (j : ℕ) (hj : j < 8),
        Normalized (eval env.toEnvironment ((stateVarPaired i₀ input_var_state k)[j]'hj)) := by
    intro k hk
    induction k with
    | zero =>
      intro j hj
      simp only [stateVarPaired]
      rw [getElem_eval_vector, h_input_state]
      exact h_state_norm ⟨j, hj⟩
    | succ k ih =>
      have hk' : k ≤ 31 := by omega
      have hk'' : k < 31 := by omega
      have hk2 : 2 * k < 64 := by omega
      have hk2' : 2 * k + 1 < 64 := by omega
      specialize h_env ⟨k, hk''⟩
      rw [foldlAcc_eq_stateVarPaired i₀ input_var_state input_var_schedule k hk''] at h_env
      simp only [circuit_norm, SHA256RoundPair.circuit, SHA256RoundPair.elaborated,
        SHA256RoundPair.Spec, SHA256RoundPair.Assumptions] at h_env
      have h2a : Normalized (Vector.map (Expression.eval env.toEnvironment)
          (constWord32 (p:=p) (Specs.SHA256.K[2*k]'hk2).toNat)) := SHA256Rounds.normalized_constWord32 _ _
      have h2b : Normalized (Vector.map (Expression.eval env.toEnvironment)
          (constWord32 (p:=p) (Specs.SHA256.K[2*k+1]'hk2').toNat)) := SHA256Rounds.normalized_constWord32 _ _
      have h3a : Normalized (Vector.map (Expression.eval env.toEnvironment)
          (input_var_schedule[2*k]'hk2)) := by
        rw [show Vector.map (Expression.eval env.toEnvironment) (input_var_schedule[2*k]'hk2)
              = eval env.toEnvironment (input_var_schedule[2*k]'hk2) from
            (CircuitType.eval_var_fields _ _).symm]
        rw [getElem_eval_vector, h_input_schedule]
        exact h_sched_norm ⟨2*k, hk2⟩ (by change 2*k < 62; omega)
      have h3b : Normalized (Vector.map (Expression.eval env.toEnvironment)
          (input_var_schedule[2*k+1]'hk2')) := by
        rw [show Vector.map (Expression.eval env.toEnvironment) (input_var_schedule[2*k+1]'hk2')
              = eval env.toEnvironment (input_var_schedule[2*k+1]'hk2') from
            (CircuitType.eval_var_fields _ _).symm]
        rw [getElem_eval_vector, h_input_schedule]
        exact h_sched_norm ⟨2*k+1, hk2'⟩ (by change 2*k+1 < 62; omega)
      have h_spec := h_env ⟨by
        intro i
        have h := ih hk' i.val i.isLt
        rw [getElem_eval_vector] at h
        exact h, h2a, h3a, h2b, h3b⟩
      obtain ⟨_, h_norm⟩ := h_spec
      intro j hj
      rw [stateVarPaired]
      rw [getElem_eval_vector]
      exact h_norm ⟨j, hj⟩
  intro i
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro j
    have h := h_inv i.val (le_of_lt i.isLt) j.val j.isLt
    rw [← foldlAcc_eq_stateVarPaired i₀ input_var_state input_var_schedule i.val i.isLt] at h
    rw [getElem_eval_vector] at h
    have heq : (⟨i.val, i.isLt⟩ : Fin 31) = i := Fin.ext rfl
    rw [heq] at h
    exact h
  · exact SHA256Rounds.normalized_constWord32 _ _
  · have hi : 2 * i.val < 64 := by omega
    rw [show Vector.map (Expression.eval env.toEnvironment) (input_var_schedule[2*i.val]'hi)
          = eval env.toEnvironment (input_var_schedule[2*i.val]'hi) from
        (CircuitType.eval_var_fields _ _).symm]
    rw [getElem_eval_vector, h_input_schedule]
    exact h_sched_norm ⟨2*i.val, hi⟩ (by change 2*i.val < 62; omega)
  · exact SHA256Rounds.normalized_constWord32 _ _
  · have hi : 2 * i.val + 1 < 64 := by omega
    rw [show Vector.map (Expression.eval env.toEnvironment) (input_var_schedule[2*i.val+1]'hi)
          = eval env.toEnvironment (input_var_schedule[2*i.val+1]'hi) from
        (CircuitType.eval_var_fields _ _).symm]
    rw [getElem_eval_vector, h_input_schedule]
    exact h_sched_norm ⟨2*i.val+1, hi⟩ (by change 2*i.val+1 < 62; omega)

def circuit62_paired : FormalCircuit (F p) Inputs SHA256State := {
  main := main62_paired, elaborated := elaborated62_paired,
  Assumptions := Assumptions62, Spec := Spec62
  soundness := soundness62_paired
  completeness := by simp only [completeness62_paired]
}

/-- Cheap `rfl` projection of `circuit62_paired`'s output: exposes the concrete
`stateVarPaired` witness layout without unfolding the 31-pair fold (which
whnf-times-out). Used to align the abstract subcircuit hypotheses with the goal
in `soundness63_paired` / `completeness63_paired`. -/
lemma circuit62_paired_output_eq (i₀ : ℕ)
    (s : Var SHA256State (F p)) (sch : Var SHA256Schedule (F p)) :
    circuit62_paired.output ⟨s, sch⟩ i₀ = stateVarPaired i₀ s 31 := rfl

/-- Cheap `rfl` projection of `circuit62_paired`'s local length (31 pairs · 328). -/
lemma circuit62_paired_localLength_eq
    (s : Var SHA256State (F p)) (sch : Var SHA256Schedule (F p)) :
    circuit62_paired.localLength ⟨s, sch⟩ = 10168 := rfl

/-!
## 63-round variant built from 31 pairs + one plain round (drop-in for `circuit`)

`circuit62_paired` (rounds 0..61 as 31 pairs) followed by one uniform `SHA256Round`
for round 62. Same `Assumptions`/`Spec` as `SHA256Rounds63.circuit`
(`valStateAfterRound … 63`), so it is a drop-in replacement for the block-5 fused
compression tail. -/

def main63_paired (input : Var Inputs (F p)) : Circuit (F p) (Var SHA256State (F p)) := do
  let s62 ← circuit62_paired ⟨input.state, input.schedule⟩
  SHA256Round.circuit ⟨s62,
    constWord32 (Specs.SHA256.K[62]'(by norm_num)).toNat, input.schedule[62]'(by norm_num)⟩

instance elaborated63_paired : ElaboratedCircuit (F p) Inputs SHA256State main63_paired := by
  elaborate_circuit

set_option maxHeartbeats 1000000 in
theorem soundness63_paired : Soundness (F p) main63_paired Assumptions Spec := by
  -- Keep `circuit62_paired` abstract (out of the `circuit_proof_start` bracket):
  -- unfolding it forces the 31-pair fold and whnf-times-out. Reason via its
  -- packaged `Spec`/`Assumptions` (defeq to `Spec62`/`Assumptions62`) instead.
  circuit_proof_start [SHA256Round.circuit, SHA256Round.Spec, SHA256Round.Assumptions,
    main63_paired, Spec, Assumptions]
  obtain ⟨h_state_norm, h_sched_norm⟩ := h_assumptions
  obtain ⟨h_input_state, h_input_schedule⟩ := h_input
  obtain ⟨c62, c_round⟩ := h_holds
  have red : ∀ (m : ℕ) (V : ProvableVector (fields 32) m (Expression (F p))) (k : ℕ) (hk : k < m),
      (eval env V)[k]'hk = Vector.map (Expression.eval env) (V[k]'hk) := by
    intro m V k hk
    rw [← getElem_eval_vector env V k hk, CircuitType.eval_var_fields]
  -- `circuit62_paired`'s spec, obtained via its abstract `Spec`/`Assumptions`.
  have s62 := c62 ⟨h_state_norm, fun i _ => h_sched_norm i⟩
  obtain ⟨hs62_val, hs62_norm⟩ := s62
  have hwn : Normalized (Vector.map (Expression.eval env) (input_var_schedule[62]'(by norm_num))) := by
    rw [← red, h_input_schedule]
    exact h_sched_norm 62
  have hk62n : Normalized (Vector.map (Expression.eval env)
      (constWord32 (p := p) (Specs.SHA256.K[62]'(by norm_num)).toNat)) :=
    SHA256Rounds.normalized_constWord32 env _
  -- The final round consumes `circuit62_paired`'s (abstract) output; its
  -- normalization is exactly `hs62_norm`.
  have s_round := c_round ⟨hs62_norm, hk62n, hwn⟩
  obtain ⟨hr_val, hr_norm⟩ := s_round
  -- Reduce the abstract `circuit62_paired.output` / `.localLength` projections to
  -- the concrete `stateVarPaired` / `11284` forms the goal is stated in.
  simp only [circuit62_paired_output_eq, circuit62_paired_localLength_eq] at hr_val hr_norm hs62_val
  refine ⟨⟨?_, ?_⟩, Or.inr ⟨h_state_norm, fun i _ => h_sched_norm i⟩⟩
  · -- Rewrite the `sha256Round` arguments directly (no `congr`, which would whnf
    -- the bare `eval env (stateVarPaired … 31)` and blow up on its 31-level fold).
    rw [hr_val,
      SHA256Rounds.valStateAfterRound_succ (Vector.map valueBits input_state)
        (Vector.map valueBits input_schedule) 62 (by norm_num),
      hs62_val,
      SHA256Rounds.valueBits_constWord32_of_lt env (Specs.SHA256.K[62]'(by norm_num)).toNat_lt,
      show Vector.map (Expression.eval env) (input_var_schedule[62]'(by norm_num))
          = eval env (input_var_schedule[62]'(by norm_num)) from (CircuitType.eval_var_fields env _).symm,
      getElem_eval_vector, h_input_schedule, Vector.getElem_map]
  · exact hr_norm

set_option maxHeartbeats 1000000 in
theorem completeness63_paired : Completeness (F p) main63_paired Assumptions := by
  -- Keep `circuit62_paired` abstract (see `soundness63_paired`): unfolding it
  -- whnf-times-out on the 31-pair fold. Reason via its packaged spec instead.
  circuit_proof_start [SHA256Round.circuit, SHA256Round.Spec, SHA256Round.Assumptions,
    main63_paired, Assumptions]
  obtain ⟨h_state_norm, h_sched_norm⟩ := h_assumptions
  obtain ⟨h_input_state, h_input_schedule⟩ := h_input
  obtain ⟨c62, _⟩ := h_env
  have red : ∀ (m : ℕ) (V : ProvableVector (fields 32) m (Expression (F p))) (k : ℕ) (hk : k < m),
      (eval env.toEnvironment V)[k]'hk = Vector.map (Expression.eval env.toEnvironment) (V[k]'hk) := by
    intro m V k hk
    rw [← getElem_eval_vector env.toEnvironment V k hk, CircuitType.eval_var_fields]
  -- `circuit62_paired`'s output normalization comes straight from its spec; it is
  -- exactly the state-normalization the final round requires (no reduction needed,
  -- the round's input is `circuit62_paired.output` in both).
  obtain ⟨_, hs62_norm⟩ := c62 ⟨h_state_norm, fun i _ => h_sched_norm i⟩
  have hwn : Normalized (Vector.map (Expression.eval env.toEnvironment)
      (input_var_schedule[62]'(by norm_num))) := by
    rw [← red, h_input_schedule]
    exact h_sched_norm 62
  have hk62n : Normalized (Vector.map (Expression.eval env.toEnvironment)
      (constWord32 (p := p) (Specs.SHA256.K[62]'(by norm_num)).toNat)) :=
    SHA256Rounds.normalized_constWord32 _ _
  exact ⟨⟨h_state_norm, fun i _ => h_sched_norm i⟩, hs62_norm, hk62n, hwn⟩

def circuit63_paired : FormalCircuit (F p) Inputs SHA256State := {
  main := main63_paired, elaborated := elaborated63_paired,
  Assumptions := Assumptions, Spec := Spec
  soundness := soundness63_paired
  completeness := by simp only [completeness63_paired]
}

/-- Cheap `rfl` projection of `circuit63_paired`'s local length (31 pairs · 328 + one
plain round · 195). Reduces the abstract subcircuit's witness offset to a literal so
the fused-compression proof's hypotheses line up with the (already-reduced) goal. -/
lemma circuit63_paired_localLength_eq
    (s : Var SHA256State (F p)) (sch : Var SHA256Schedule (F p)) :
    circuit63_paired.localLength ⟨s, sch⟩ = 10363 := rfl

end Paired

end SHA256Rounds63

/-!
## FormalCircuit for full compression: 63 rounds + fused final round + Davies-Meyer

`SHA256Rounds.circuit` now represents the *entire* per-block compression
including the Davies-Meyer feedforward add (previously split across
`SHA256Rounds` + a separate `Add32` chain in `CompressBlock`/`CompressBlock5`).
Folding Davies-Meyer in here lets round 63's `new_a`/`new_e` be produced
*already* fused with the feedforward add, skipping their separate
32-bit-reduced materialization entirely: word 0's Davies-Meyer sum is a single
8-addend `AddMany` (`state[0] + h + Σ₁(e) + Ch(e,f,g) + k₆₃ + w₆₃ + Σ₀(a) +
Maj(a,b,c)`), word 4's is a single 7-addend `AddMany` (`state[4] + d + h +
Σ₁(e) + Ch(e,f,g) + k₆₃ + w₆₃`). `AddMany`'s cost is the constant `⟨34, 35⟩`
for any `n ≤ 8`, so both fused adders cost exactly what the old 6-word
`new_e`-only `AddMany` cost alone.
-/

namespace SHA256Rounds

-- The fused compression now runs its first 63 rounds through `circuit63_paired`
-- (31 cross-round pairs + one plain round), which requires a prime wide enough
-- for the paired gadget's packing.
variable [Fact (p > 2^76)]

structure Inputs (F : Type) where
  state : SHA256State F
  schedule : SHA256Schedule F
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var SHA256State (F p)) := do
  let state63 ← SHA256Rounds63.circuit63_paired ⟨input.state, input.schedule⟩
  let a := state63[0]; let b := state63[1]; let c := state63[2]; let d := state63[3]
  let e := state63[4]; let f := state63[5]; let g := state63[6]; let h := state63[7]
  let sig1 ← UpperSigma1.circuit e
  let ch   ← Ch32.circuit ⟨e, f, g⟩
  let sig0 ← UpperSigma0.circuit a
  let maj  ← Maj32.circuit ⟨a, b, c⟩
  let k63 := constWord32 (Specs.SHA256.K[63]'(by norm_num)).toNat
  let w63 := input.schedule[63]'(by norm_num)
  let out0 ← AddMany.circuit (by norm_num) #v[input.state[0], h, sig1, ch, k63, w63, sig0, maj]
  let out4 ← AddMany.circuit (by norm_num) #v[input.state[4], d, h, sig1, ch, k63, w63]
  let out1 ← Add32.circuit ⟨input.state[1], a⟩
  let out2 ← Add32.circuit ⟨input.state[2], b⟩
  let out3 ← Add32.circuit ⟨input.state[3], c⟩
  let out5 ← Add32.circuit ⟨input.state[5], e⟩
  let out6 ← Add32.circuit ⟨input.state[6], f⟩
  let out7 ← Add32.circuit ⟨input.state[7], g⟩
  return #v[out0, out1, out2, out3, out4, out5, out6, out7]

instance elaborated : ElaboratedCircuit (F p) Inputs SHA256State main := by
  elaborate_circuit

def Assumptions (input : Inputs (F p)) : Prop :=
  (∀ i : Fin 8, Normalized input.state[i]) ∧
  (∀ i : Fin 64, Normalized input.schedule[i])

/-- Spec now covers the *entire* compress-and-feedforward: `out` is the
Davies-Meyer-folded next chaining state, matching `Specs.SHA256.compressBlock`
applied to `state` and the block underlying this schedule. -/
def Spec (input : Inputs (F p)) (out : SHA256State (F p)) : Prop :=
  out.map valueBits =
    Vector.mapFinRange 8 (fun i => _root_.add32 (input.state.map valueBits)[i]
      (Specs.SHA256.sha256Compress (input.state.map valueBits) (input.schedule.map valueBits))[i])
  ∧ ∀ i : Fin 8, Normalized out[i]

/-- One-step unfolding of `sha256Compress` via `valStateAfterRound`, peeling off
round 63 (the last of the 64). -/
theorem sha256Compress_eq_round63 (state : Vector ℕ 8) (schedule : Vector ℕ 64) :
    Specs.SHA256.sha256Compress state schedule =
      Specs.SHA256.sha256Round (valStateAfterRound state schedule 63)
        (Specs.SHA256.K[63]'(by norm_num)).toNat (schedule[63]'(by norm_num)) := by
  rw [sha256Compress_eq_valStateAfterRound]
  show valStateAfterRound state schedule (63 + 1) = _
  rw [valStateAfterRound, dif_pos (by norm_num : (63:ℕ) < 64)]

/-- Whole-round literal form of the spec round (proved by `rfl` on variables; kernel-cheap:
no defeq on `add32`-headed component extractions, no unfolding on `valStateAfterRound`). -/
theorem sha256Round_literal (st : Vector ℕ 8) (k w : ℕ) :
    Specs.SHA256.sha256Round st k w =
      #v[_root_.add32 (_root_.add32 (_root_.add32 (_root_.add32 (_root_.add32 st[7]
              (Specs.SHA256.upperSigma1 st[4])) (Specs.SHA256.Ch st[4] st[5] st[6])) k) w)
           (_root_.add32 (Specs.SHA256.upperSigma0 st[0]) (Specs.SHA256.Maj st[0] st[1] st[2])),
         st[0], st[1], st[2],
         _root_.add32 st[3] (_root_.add32 (_root_.add32 (_root_.add32 (_root_.add32 st[7]
              (Specs.SHA256.upperSigma1 st[4])) (Specs.SHA256.Ch st[4] st[5] st[6])) k) w),
         st[4], st[5], st[6]] := rfl

/-- Kernel-cheap indexing into an 8-element vector literal: elements stay variables,
so the extraction never forces reduction of `add32`-headed components. -/
theorem vec8_get {α : Type*} (a0 a1 a2 a3 a4 a5 a6 a7 : α) :
    ((#v[a0,a1,a2,a3,a4,a5,a6,a7] : Vector α 8)[0]'(by norm_num) = a0) ∧
    ((#v[a0,a1,a2,a3,a4,a5,a6,a7] : Vector α 8)[1]'(by norm_num) = a1) ∧
    ((#v[a0,a1,a2,a3,a4,a5,a6,a7] : Vector α 8)[2]'(by norm_num) = a2) ∧
    ((#v[a0,a1,a2,a3,a4,a5,a6,a7] : Vector α 8)[3]'(by norm_num) = a3) ∧
    ((#v[a0,a1,a2,a3,a4,a5,a6,a7] : Vector α 8)[4]'(by norm_num) = a4) ∧
    ((#v[a0,a1,a2,a3,a4,a5,a6,a7] : Vector α 8)[5]'(by norm_num) = a5) ∧
    ((#v[a0,a1,a2,a3,a4,a5,a6,a7] : Vector α 8)[6]'(by norm_num) = a6) ∧
    ((#v[a0,a1,a2,a3,a4,a5,a6,a7] : Vector α 8)[7]'(by norm_num) = a7) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
theorem soundness : Soundness (F p) main Assumptions Spec := by
  -- The first-63-rounds subcircuit is now `circuit63_paired`; keep it abstract
  -- (its 31-pair fold whnf-times-out if unfolded) and reason via its `Spec`
  -- (definitionally `SHA256Rounds63.Spec`), exactly as the block-1 fused proof does.
  circuit_proof_start [SHA256Rounds63.Spec, SHA256Rounds63.Assumptions,
    UpperSigma1.circuit, UpperSigma1.Spec, UpperSigma1.Assumptions,
    Ch32.circuit, Ch32.Spec, Ch32.Assumptions,
    UpperSigma0.circuit, UpperSigma0.Spec, UpperSigma0.Assumptions,
    Maj32.circuit, Maj32.Spec, Maj32.Assumptions,
    AddMany.circuit, AddMany.Spec, AddMany.Assumptions,
    Add32.circuit, Add32.Spec, Add32.Assumptions]
  obtain ⟨h_state_norm, h_sched_norm⟩ := h_assumptions
  obtain ⟨h_input_state, h_input_schedule⟩ := h_input
  obtain ⟨c_r63, c_sig1, c_ch, c_sig0, c_maj, c_out0, c_out4, c_out1, c_out2, c_out3, c_out5, c_out6, c_out7⟩ :=
    h_holds
  -- indexing-inside-eval reducer (same as SHA256Round.soundness's `red`)
  have red : ∀ (m : ℕ) (V : ProvableVector (fields 32) m (Expression (F p))) (k : ℕ) (hk : k < m),
      (eval env V)[k]'hk = Vector.map (Expression.eval env) (V[k]'hk) := by
    intro m V k hk
    rw [← getElem_eval_vector env V k hk, CircuitType.eval_var_fields]
  have s_r63 := c_r63 ⟨h_state_norm, h_sched_norm⟩
  obtain ⟨hs63_val, hs63_norm⟩ := s_r63
  -- The first-63-rounds output is `circuit63_paired`'s (abstract) output; keeping it
  -- abstract avoids forcing the paired witness fold.
  have hs63n : ∀ i (hi : i < 8),
      Normalized (Vector.map (Expression.eval env)
        ((SHA256Rounds63.circuit63_paired.output ⟨input_var_state, input_var_schedule⟩ i₀)[i]'hi)) := by
    intro i hi
    rw [← red]
    exact hs63_norm ⟨i, hi⟩
  have s_sig1 := c_sig1 (hs63n 4 (by norm_num))
  have s_ch := c_ch ⟨hs63n 4 (by norm_num), hs63n 5 (by norm_num), hs63n 6 (by norm_num)⟩
  have s_sig0 := c_sig0 (hs63n 0 (by norm_num))
  have s_maj := c_maj ⟨hs63n 0 (by norm_num), hs63n 1 (by norm_num), hs63n 2 (by norm_num)⟩
  have hstn : ∀ (i : ℕ) (hi : i < 8),
      Normalized (Vector.map (Expression.eval env) (input_var_state[i]'hi)) := by
    intro i hi
    rw [← red, h_input_state]
    exact h_state_norm ⟨i, hi⟩
  have hwn : Normalized (Vector.map (Expression.eval env) (input_var_schedule[63]'(by norm_num))) := by
    rw [← red, h_input_schedule]
    exact h_sched_norm 63
  have hk63n : Normalized
      (Vector.map (Expression.eval env) (constWord32 (p := p) (Specs.SHA256.K[63]'(by norm_num)).toNat)) :=
    SHA256Rounds.normalized_constWord32 env _
  have s_out0 := c_out0 (by
    intro i
    fin_cases i <;>
      simp only [red, Fin.getElem_fin, Fin.val_mk, Fin.isValue, Vector.getElem_mk,
        List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
    · exact hstn 0 (by norm_num)
    · exact hs63n 7 (by norm_num)
    · exact s_sig1.2
    · exact s_ch.2
    · exact hk63n
    · exact hwn
    · exact s_sig0.2
    · exact s_maj.2)
  have s_out4 := c_out4 (by
    intro i
    fin_cases i <;>
      simp only [red, Fin.getElem_fin, Fin.val_mk, Fin.isValue, Vector.getElem_mk,
        List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
    · exact hstn 4 (by norm_num)
    · exact hs63n 3 (by norm_num)
    · exact hs63n 7 (by norm_num)
    · exact s_sig1.2
    · exact s_ch.2
    · exact hk63n
    · exact hwn)
  have s_out1 := c_out1 ⟨hstn 1 (by norm_num), hs63n 0 (by norm_num)⟩
  have s_out2 := c_out2 ⟨hstn 2 (by norm_num), hs63n 1 (by norm_num)⟩
  have s_out3 := c_out3 ⟨hstn 3 (by norm_num), hs63n 2 (by norm_num)⟩
  have s_out5 := c_out5 ⟨hstn 5 (by norm_num), hs63n 4 (by norm_num)⟩
  have s_out6 := c_out6 ⟨hstn 6 (by norm_num), hs63n 5 (by norm_num)⟩
  have s_out7 := c_out7 ⟨hstn 7 (by norm_num), hs63n 6 (by norm_num)⟩
  -- `circuit63_paired` is abstract, so its `localLength` stays symbolic in the
  -- subcircuit-output offsets; reduce it to the literal `11479` the (elaborated)
  -- goal is stated in, so the per-word adder specs line up.
  simp only [SHA256Rounds63.circuit63_paired_localLength_eq] at s_sig1 s_ch s_sig0 s_maj s_out0 s_out1 s_out2 s_out3 s_out4 s_out5 s_out6 s_out7
  -- value bridges: expression-level `valueBits` facts back to the plain ℕ-vectors used by `Spec`
  have hstv : ∀ i (hi : i < 8), valueBits (Vector.map (Expression.eval env) (input_var_state[i]'hi))
      = (Vector.map valueBits input_state)[i]'hi := by
    intro i hi
    rw [Vector.getElem_map, ← red, h_input_state]
  have hwv : valueBits (Vector.map (Expression.eval env) (input_var_schedule[63]'(by norm_num)))
      = (Vector.map valueBits input_schedule)[63]'(by norm_num) := by
    rw [Vector.getElem_map, ← red, h_input_schedule]
  have hkv : valueBits (Vector.map (Expression.eval env)
      (constWord32 (p := p) (Specs.SHA256.K[63]'(by norm_num)).toNat))
      = (Specs.SHA256.K[63]'(by norm_num)).toNat :=
    SHA256Rounds.valueBits_constWord32_of_lt env (Specs.SHA256.K[63]'(by norm_num)).toNat_lt
  have hs63v : ∀ i (hi : i < 8), valueBits (Vector.map (Expression.eval env)
        ((SHA256Rounds63.circuit63_paired.output ⟨input_var_state, input_var_schedule⟩ i₀)[i]'hi))
      = (SHA256Rounds.valStateAfterRound (Vector.map valueBits input_state)
          (Vector.map valueBits input_schedule) 63)[i]'hi := by
    intro i hi
    rw [← red]
    have hc := congrArg (fun v => v[i]'hi) hs63_val
    simpa only [Vector.getElem_map] using hc
  -- reassociation helpers over plain ℕ (so `omega` never inspects the heavy atoms)
  have mod8dm : ∀ s h σ1 c k w σ0 m : ℕ,
      (s + h + σ1 + c + k + w + σ0 + m) % 2^32 =
        _root_.add32 s (_root_.add32
          (_root_.add32 (_root_.add32 (_root_.add32 (_root_.add32 h σ1) c) k) w)
          (_root_.add32 σ0 m)) := by
    intro s h σ1 c k w σ0 m; unfold _root_.add32; omega
  have mod7dm : ∀ s d h σ1 c k w : ℕ,
      (s + d + h + σ1 + c + k + w) % 2^32 =
        _root_.add32 s (_root_.add32 d
          (_root_.add32 (_root_.add32 (_root_.add32 (_root_.add32 h σ1) c) k) w)) := by
    intro s d h σ1 c k w; unfold _root_.add32; omega
  have modp : ∀ a b : ℕ, (a + b) % 2^32 = _root_.add32 a b := fun _ _ => rfl
  -- `circuit63_paired` is abstract, so its channel/assumptions obligation survives
  -- `circuit_proof_start`; discharge it via `Or.inr` (its `Assumptions` hold).
  refine ⟨⟨?_, ?_⟩, Or.inr ⟨h_state_norm, h_sched_norm⟩⟩
  · apply Vector.ext
    intro i hi
    rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · -- word 0: fused 8-addend Davies-Meyer sum
      rw [Vector.getElem_map, Vector.getElem_mapFinRange, sha256Compress_eq_round63,
        red 8 _ 0 (by norm_num), sha256Round_literal]
      simp only [Fin.getElem_fin, Fin.val_mk]
      rw [(vec8_get _ _ _ _ _ _ _ _).1, (vec8_get _ _ _ _ _ _ _ _).1]
      rw [s_out0.1, Fin.sum_univ_eight]
      simp only [Fin.getElem_fin, red,
        show ((0:Fin 8):ℕ)=0 from rfl, show ((1:Fin 8):ℕ)=1 from rfl,
        show ((2:Fin 8):ℕ)=2 from rfl, show ((3:Fin 8):ℕ)=3 from rfl, show ((4:Fin 8):ℕ)=4 from rfl,
        show ((5:Fin 8):ℕ)=5 from rfl, show ((6:Fin 8):ℕ)=6 from rfl, show ((7:Fin 8):ℕ)=7 from rfl,
        Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
      rw [hstv 0 (by norm_num), hs63v 7 (by norm_num), s_sig1.1, s_ch.1, hkv, hwv, s_sig0.1, s_maj.1,
        hs63v 4 (by norm_num), hs63v 5 (by norm_num), hs63v 6 (by norm_num),
        hs63v 0 (by norm_num), hs63v 1 (by norm_num), hs63v 2 (by norm_num)]
      simp only [Vector.getElem_map]
      exact mod8dm _ _ _ _ _ _ _ _
    · -- word 1
      rw [Vector.getElem_map, Vector.getElem_mapFinRange, sha256Compress_eq_round63,
        red 8 _ 1 (by norm_num), sha256Round_literal]
      simp only [Fin.getElem_fin, Fin.val_mk]
      rw [(vec8_get _ _ _ _ _ _ _ _).2.1, (vec8_get _ _ _ _ _ _ _ _).2.1]
      rw [s_out1.1, hstv 1 (by norm_num), hs63v 0 (by norm_num)]
      simp only [Vector.getElem_map]
      exact modp _ _
    · -- word 2
      rw [Vector.getElem_map, Vector.getElem_mapFinRange, sha256Compress_eq_round63,
        red 8 _ 2 (by norm_num), sha256Round_literal]
      simp only [Fin.getElem_fin, Fin.val_mk]
      rw [(vec8_get _ _ _ _ _ _ _ _).2.2.1, (vec8_get _ _ _ _ _ _ _ _).2.2.1]
      rw [s_out2.1, hstv 2 (by norm_num), hs63v 1 (by norm_num)]
      simp only [Vector.getElem_map]
      exact modp _ _
    · -- word 3
      rw [Vector.getElem_map, Vector.getElem_mapFinRange, sha256Compress_eq_round63,
        red 8 _ 3 (by norm_num), sha256Round_literal]
      simp only [Fin.getElem_fin, Fin.val_mk]
      rw [(vec8_get _ _ _ _ _ _ _ _).2.2.2.1, (vec8_get _ _ _ _ _ _ _ _).2.2.2.1]
      rw [s_out3.1, hstv 3 (by norm_num), hs63v 2 (by norm_num)]
      simp only [Vector.getElem_map]
      exact modp _ _
    · -- word 4: fused 7-addend Davies-Meyer sum
      rw [Vector.getElem_map, Vector.getElem_mapFinRange, sha256Compress_eq_round63,
        red 8 _ 4 (by norm_num), sha256Round_literal]
      simp only [Fin.getElem_fin, Fin.val_mk]
      rw [(vec8_get _ _ _ _ _ _ _ _).2.2.2.2.1, (vec8_get _ _ _ _ _ _ _ _).2.2.2.2.1]
      rw [s_out4.1, Fin.sum_univ_seven]
      simp only [Fin.getElem_fin, red,
        show ((0:Fin 7):ℕ)=0 from rfl, show ((1:Fin 7):ℕ)=1 from rfl,
        show ((2:Fin 7):ℕ)=2 from rfl, show ((3:Fin 7):ℕ)=3 from rfl, show ((4:Fin 7):ℕ)=4 from rfl,
        show ((5:Fin 7):ℕ)=5 from rfl, show ((6:Fin 7):ℕ)=6 from rfl,
        Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
      rw [hstv 4 (by norm_num), hs63v 3 (by norm_num), hs63v 7 (by norm_num), s_sig1.1, s_ch.1, hkv, hwv,
        hs63v 4 (by norm_num), hs63v 5 (by norm_num), hs63v 6 (by norm_num)]
      simp only [Vector.getElem_map]
      exact mod7dm _ _ _ _ _ _ _
    · -- word 5
      rw [Vector.getElem_map, Vector.getElem_mapFinRange, sha256Compress_eq_round63,
        red 8 _ 5 (by norm_num), sha256Round_literal]
      simp only [Fin.getElem_fin, Fin.val_mk]
      rw [(vec8_get _ _ _ _ _ _ _ _).2.2.2.2.2.1, (vec8_get _ _ _ _ _ _ _ _).2.2.2.2.2.1]
      rw [s_out5.1, hstv 5 (by norm_num), hs63v 4 (by norm_num)]
      simp only [Vector.getElem_map]
      exact modp _ _
    · -- word 6
      rw [Vector.getElem_map, Vector.getElem_mapFinRange, sha256Compress_eq_round63,
        red 8 _ 6 (by norm_num), sha256Round_literal]
      simp only [Fin.getElem_fin, Fin.val_mk]
      rw [(vec8_get _ _ _ _ _ _ _ _).2.2.2.2.2.2.1, (vec8_get _ _ _ _ _ _ _ _).2.2.2.2.2.2.1]
      rw [s_out6.1, hstv 6 (by norm_num), hs63v 5 (by norm_num)]
      simp only [Vector.getElem_map]
      exact modp _ _
    · -- word 7
      rw [Vector.getElem_map, Vector.getElem_mapFinRange, sha256Compress_eq_round63,
        red 8 _ 7 (by norm_num), sha256Round_literal]
      simp only [Fin.getElem_fin, Fin.val_mk]
      rw [(vec8_get _ _ _ _ _ _ _ _).2.2.2.2.2.2.2, (vec8_get _ _ _ _ _ _ _ _).2.2.2.2.2.2.2]
      rw [s_out7.1, hstv 7 (by norm_num), hs63v 6 (by norm_num)]
      simp only [Vector.getElem_map]
      exact modp _ _
  · intro i
    fin_cases i <;>
      simp only [red, Fin.getElem_fin, Fin.val_mk, Fin.isValue, Vector.getElem_mk,
        List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
    · exact s_out0.2
    · exact s_out1.2
    · exact s_out2.2
    · exact s_out3.2
    · exact s_out4.2
    · exact s_out5.2
    · exact s_out6.2
    · exact s_out7.2

set_option maxHeartbeats 1000000 in
theorem completeness : Completeness (F p) main Assumptions := by
  -- `circuit63_paired` kept abstract (see `soundness`).
  circuit_proof_start [SHA256Rounds63.Spec, SHA256Rounds63.Assumptions,
    UpperSigma1.circuit, UpperSigma1.Spec, UpperSigma1.Assumptions,
    Ch32.circuit, Ch32.Spec, Ch32.Assumptions,
    UpperSigma0.circuit, UpperSigma0.Spec, UpperSigma0.Assumptions,
    Maj32.circuit, Maj32.Spec, Maj32.Assumptions,
    AddMany.circuit, AddMany.Spec, AddMany.Assumptions,
    Add32.circuit, Add32.Spec, Add32.Assumptions]
  obtain ⟨h_state_norm, h_sched_norm⟩ := h_assumptions
  obtain ⟨h_input_state, h_input_schedule⟩ := h_input
  obtain ⟨e_r63, e_sig1, e_ch, e_sig0, e_maj, -⟩ := h_env
  have red : ∀ (m : ℕ) (V : ProvableVector (fields 32) m (Expression (F p))) (k : ℕ) (hk : k < m),
      (eval env.toEnvironment V)[k]'hk = Vector.map (Expression.eval env.toEnvironment) (V[k]'hk) := by
    intro m V k hk
    rw [← getElem_eval_vector env.toEnvironment V k hk, CircuitType.eval_var_fields]
  obtain ⟨-, hs63_norm⟩ := e_r63 ⟨h_state_norm, h_sched_norm⟩
  have hs63n : ∀ i (hi : i < 8),
      Normalized (Vector.map (Expression.eval env.toEnvironment)
        ((SHA256Rounds63.circuit63_paired.output ⟨input_var_state, input_var_schedule⟩ i₀)[i]'hi)) := by
    intro i hi
    rw [← red]
    exact hs63_norm ⟨i, hi⟩
  have hstn : ∀ (i : ℕ) (hi : i < 8),
      Normalized (Vector.map (Expression.eval env.toEnvironment) (input_var_state[i]'hi)) := by
    intro i hi
    rw [← red, h_input_state]
    exact h_state_norm ⟨i, hi⟩
  have hwn : Normalized (Vector.map (Expression.eval env.toEnvironment)
      (input_var_schedule[63]'(by norm_num))) := by
    rw [← red, h_input_schedule]
    exact h_sched_norm 63
  have hk63n : Normalized (Vector.map (Expression.eval env.toEnvironment)
      (constWord32 (p := p) (Specs.SHA256.K[63]'(by norm_num)).toNat)) :=
    SHA256Rounds.normalized_constWord32 _ _
  have s_sig1 := e_sig1 (hs63n 4 (by norm_num))
  have s_ch := e_ch ⟨hs63n 4 (by norm_num), hs63n 5 (by norm_num), hs63n 6 (by norm_num)⟩
  have s_sig0 := e_sig0 (hs63n 0 (by norm_num))
  have s_maj := e_maj ⟨hs63n 0 (by norm_num), hs63n 1 (by norm_num), hs63n 2 (by norm_num)⟩
  refine ⟨⟨h_state_norm, h_sched_norm⟩, hs63n 4 (by norm_num),
    ⟨hs63n 4 (by norm_num), hs63n 5 (by norm_num), hs63n 6 (by norm_num)⟩,
    hs63n 0 (by norm_num),
    ⟨hs63n 0 (by norm_num), hs63n 1 (by norm_num), hs63n 2 (by norm_num)⟩,
    ?_, ?_,
    ⟨hstn 1 (by norm_num), hs63n 0 (by norm_num)⟩,
    ⟨hstn 2 (by norm_num), hs63n 1 (by norm_num)⟩,
    ⟨hstn 3 (by norm_num), hs63n 2 (by norm_num)⟩,
    ⟨hstn 5 (by norm_num), hs63n 4 (by norm_num)⟩,
    ⟨hstn 6 (by norm_num), hs63n 5 (by norm_num)⟩,
    hstn 7 (by norm_num), hs63n 6 (by norm_num)⟩
  · intro i
    fin_cases i <;>
      simp only [red, Fin.getElem_fin, Fin.val_mk, Fin.isValue, Vector.getElem_mk,
        List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
    · exact hstn 0 (by norm_num)
    · exact hs63n 7 (by norm_num)
    · exact s_sig1.2
    · exact s_ch.2
    · exact hk63n
    · exact hwn
    · exact s_sig0.2
    · exact s_maj.2
  · intro i
    fin_cases i <;>
      simp only [red, Fin.getElem_fin, Fin.val_mk, Fin.isValue, Vector.getElem_mk,
        List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
    · exact hstn 4 (by norm_num)
    · exact hs63n 3 (by norm_num)
    · exact hs63n 7 (by norm_num)
    · exact s_sig1.2
    · exact s_ch.2
    · exact hk63n
    · exact hwn

def circuit : FormalCircuit (F p) Inputs SHA256State := {
  main, elaborated, Assumptions, Spec, soundness
  completeness := by simp only [completeness]
}

end SHA256Rounds
end Solution.SHA256
end
