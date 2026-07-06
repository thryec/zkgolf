import Solution.SHA256.ScheduleStep
import Solution.SHA256.MessageScheduleTheorems
import Challenge.Specs.SHA256

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^35)]

namespace Solution.SHA256

/-!
# SHA-256 Message Schedule

Expands a 16-word block into a 64-word message schedule.

For i in 16..63:
  w[i] = σ₁(w[i−2]) + w[i−7] + σ₀(w[i−15]) + w[i−16]  (mod 2^32)

`main` inlines a 48-step `Circuit.foldlRange` over the `ScheduleStep` gadget: each
step reads four schedule words, runs `ScheduleStep.circuit` (91 witnesses /
output word at relative offset 58) and `set`s the new word into the accumulator.
The accumulator descriptions (`varSchedule` / `valSchedule`) and the bridging
lemmas live in `MessageScheduleTheorems`.
-/

namespace MessageSchedule

/-- Explicit `ConstantLength` for the inlined fold body (91 witnesses per step).
    Naming it lets `Cost.lean` pass the same instance `main` folds with (the body is
    still inlined into `main`, so `circuit_proof_start` is unaffected). -/
def constantLength :
    Circuit.ConstantLength (fun (x : SHA256Schedule (Expression (F p)) × Fin 48) => do
      let wj ← ScheduleStep.circuit
        ⟨x.1.get ⟨x.2.val + 16 - 2, by omega⟩, x.1.get ⟨x.2.val + 16 - 7, by omega⟩,
         x.1.get ⟨x.2.val + 16 - 15, by omega⟩, x.1.get ⟨x.2.val + 16 - 16, by omega⟩⟩
      return x.1.set (x.2.val + 16) wj (by omega)) where
  localLength := 91
  localLength_eq _ _ := by
    simp [circuit_norm, ScheduleStep.circuit, ScheduleStep.elaborated]

def main (block : SHA256Block (Expression (F p))) : Circuit (F p) (SHA256Schedule (Expression (F p))) := do
  let zero32 : Var (fields 32) (F p) := Vector.replicate 32 (0 : Expression (F p))
  let init : SHA256Schedule (Expression (F p)) := block.append (Vector.replicate 48 zero32)
  Circuit.foldlRange 48 init (fun w i => do
    let wj ← ScheduleStep.circuit
      ⟨w.get ⟨i.val + 16 - 2, by omega⟩, w.get ⟨i.val + 16 - 7, by omega⟩,
       w.get ⟨i.val + 16 - 15, by omega⟩, w.get ⟨i.val + 16 - 16, by omega⟩⟩
    return w.set (i.val + 16) wj (by omega)) constantLength

def Assumptions (block : SHA256Block (F p)) : Prop :=
  ∀ i : Fin 16, Normalized block[i]

def Spec (block : SHA256Block (F p)) (sched : SHA256Schedule (F p)) : Prop :=
  let block_val : Vector ℕ 16 := block.map valueBits
  let expected := Specs.SHA256.messageSchedule block_val
  ∀ i : Fin 64, valueBits sched[i] = expected[i] ∧ Normalized sched[i]

instance elaborated : ElaboratedCircuit (F p) SHA256Block SHA256Schedule main := by
  elaborate_circuit_with {
    output input i₀ := varSchedule i₀ input 48
  } using by
    simp only [circuit_norm]
    intros
    exact finFoldl_eq_varSchedule_48 _ _

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [main]
  -- Inductive invariant: at every step `k`, the variable-level schedule matches the
  -- value-level schedule and is normalized.
  have h_inv : ∀ (k : ℕ) (_ : k ≤ 48),
      (∀ (j : ℕ) (hj : j < 64),
        valueBits (eval env ((varSchedule i₀ input_var k)[j]'hj)) =
          (valSchedule (input.map valueBits) k)[j]'hj) ∧
      (∀ (j : ℕ) (hj : j < 64),
        Normalized (eval env ((varSchedule i₀ input_var k)[j]'hj))) := by
    intro k hk
    induction k with
    | zero =>
      refine ⟨?_, ?_⟩
      · intro j hj
        simp only [varSchedule, valSchedule]
        by_cases hj16 : j < 16
        · change valueBits (eval env (input_var ++
            Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p))))[j]) = _
          rw [Vector.getElem_append_left hj16]
          simp only [Vector.getElem_mapFinRange, hj16, dif_pos]
          rw [show (Vector.map valueBits input).get ⟨j, hj16⟩ =
                (Vector.map valueBits input)[j]'hj16 from rfl]
          rw [Vector.getElem_map]
          congr 1
          rw [getElem_eval_vector, h_input]
        · change valueBits (eval env (input_var ++
            Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p))))[j]) = _
          have hj' : j < 16 + 48 := by omega
          rw [show (input_var ++ Vector.replicate 48
                (Vector.replicate 32 (0 : Expression (F p))))[j]'hj' =
              (Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p))))[j - 16]'(by omega)
              from Vector.getElem_append_right hj' (by omega : (16 : ℕ) ≤ j)]
          rw [Vector.getElem_replicate]
          simp only [Vector.getElem_mapFinRange, hj16, dif_neg, not_false_eq_true]
          have h_eval_repl :
              eval env (Vector.replicate 32 (0 : Expression (F p))) =
                Vector.replicate 32 (0 : F p) := by
            rw [CircuitType.eval_var_fields, Vector.map_replicate]; rfl
          unfold valueBits
          rw [h_eval_repl]
          simp [Vector.getElem_replicate]
      · intro j hj
        simp only [varSchedule]
        by_cases hj16 : j < 16
        · change Normalized (eval env (input_var ++
            Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p))))[j])
          rw [Vector.getElem_append_left hj16]
          have h_ev : eval env (input_var[j]'hj16) = input[j]'hj16 := by
            rw [getElem_eval_vector, h_input]
          rw [h_ev]
          exact h_assumptions ⟨j, hj16⟩
        · change Normalized (eval env (input_var ++
            Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p))))[j])
          have hj' : j < 16 + 48 := by omega
          rw [show (input_var ++ Vector.replicate 48
                (Vector.replicate 32 (0 : Expression (F p))))[j]'hj' =
              (Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p))))[j - 16]'(by omega)
              from Vector.getElem_append_right hj' (by omega : (16 : ℕ) ≤ j)]
          rw [Vector.getElem_replicate]
          have h_eval_repl :
              eval env (Vector.replicate 32 (0 : Expression (F p))) =
                Vector.replicate 32 (0 : F p) := by
            rw [CircuitType.eval_var_fields, Vector.map_replicate]; rfl
          rw [h_eval_repl]
          intro i; left; simp [Vector.getElem_replicate]
    | succ k ih =>
      have hk' : k ≤ 48 := by omega
      have hk'' : k < 48 := by omega
      obtain ⟨ih_val, ih_norm⟩ := ih hk'
      have h_step := h_holds ⟨k, hk''⟩
      rw [foldlAcc_eq_varSchedule i₀ input_var k hk''] at h_step
      simp only [ScheduleStep.circuit, ScheduleStep.elaborated, ScheduleStep.Assumptions,
        ScheduleStep.Spec, circuit_norm] at h_step
      have h_norm_m2 := ih_norm (k + 16 - 2) (by omega)
      have h_norm_m7 := ih_norm (k + 16 - 7) (by omega)
      have h_norm_m15 := ih_norm (k + 16 - 15) (by omega)
      have h_norm_m16 := ih_norm (k + 16 - 16) (by omega)
      rw [CircuitType.eval_var_fields] at h_norm_m2 h_norm_m7 h_norm_m15 h_norm_m16
      obtain ⟨v_wj, n_wj⟩ := h_step ⟨h_norm_m2, h_norm_m7, h_norm_m15, h_norm_m16⟩
      have ih_val' : ∀ (j : ℕ) (hj : j < 64),
          valueBits (Vector.map (Expression.eval env)
            (Vector.get (varSchedule i₀ input_var k) ⟨j, hj⟩)) =
            (valSchedule (input.map valueBits) k)[j]'hj := by
        intro j hj
        rw [show Vector.get (varSchedule i₀ input_var k) ⟨j, hj⟩ =
              (varSchedule i₀ input_var k)[j]'hj from rfl, ← CircuitType.eval_var_fields]
        exact ih_val j hj
      refine ⟨?_, ?_⟩
      · intro j hj
        simp only [varSchedule, valSchedule, dif_pos hk'']
        by_cases hjk : j = k + 16
        · subst hjk
          rw [Vector.getElem_set_self, Vector.getElem_set_self]
          rw [show (varFromOffset (fields 32) (i₀ + k * 91 + 58) : Vector (Expression (F p)) 32) =
                Vector.mapRange 32 (fun i => (var { index := i₀ + k * 91 + 58 + i } : Expression (F p)))
              from by simp [varFromOffset, ProvableType.varFromOffset, fromElements, size]]
          rw [CircuitType.eval_var_fields, v_wj,
            ih_val' (k + 16 - 2) (by omega), ih_val' (k + 16 - 7) (by omega),
            ih_val' (k + 16 - 15) (by omega), ih_val' (k + 16 - 16) (by omega)]
        · rw [Vector.getElem_set_ne (by omega : k + 16 < 64) hj (by omega : k + 16 ≠ j)]
          rw [Vector.getElem_set_ne (by omega : k + 16 < 64) hj (by omega : k + 16 ≠ j)]
          exact ih_val j hj
      · intro j hj
        simp only [varSchedule, dif_pos hk'']
        by_cases hjk : j = k + 16
        · subst hjk
          rw [Vector.getElem_set_self]
          rw [show (i₀ + k * 91 + 58 : ℕ) = i₀ + k * 91 + 29 + 22 + 6 + 1 from by omega]
          rw [show (varFromOffset (fields 32) (i₀ + k * 91 + 29 + 22 + 6 + 1) :
                Vector (Expression (F p)) 32) =
                Vector.mapRange 32 (fun i =>
                  (var { index := i₀ + k * 91 + 29 + 22 + 6 + 1 + i } : Expression (F p)))
              from by simp [varFromOffset, ProvableType.varFromOffset, fromElements, size]]
          rw [CircuitType.eval_var_fields]
          exact n_wj
        · rw [Vector.getElem_set_ne (by omega : k + 16 < 64) hj (by omega : k + 16 ≠ j)]
          exact ih_norm j hj
  obtain ⟨h_val_48, h_norm_48⟩ := h_inv 48 (le_refl 48)
  refine ⟨?_, ?_⟩
  · intro i
    have h_bridge :
        (eval env (varSchedule i₀ input_var 48))[i.val] =
          eval env ((varSchedule i₀ input_var 48)[i.val]'i.isLt) :=
      (getElem_eval_vector (α := fields 32) (n := 64) env (varSchedule i₀ input_var 48) i.val i.isLt).symm
    refine ⟨?_, ?_⟩
    · rw [h_bridge, messageSchedule_eq_valSchedule]
      exact h_val_48 i.val i.isLt
    · rw [h_bridge]
      exact h_norm_48 i.val i.isLt
  · intro i
    simp [ScheduleStep.circuit, circuit_norm]

theorem completeness : Completeness (F p) (Input := SHA256Block) (Output := SHA256Schedule) main Assumptions := by
  circuit_proof_start [main]
  -- Inductive invariant: at every step k, every slot of `varSchedule i₀ input_var k`
  -- is Normalized.
  have h_inv : ∀ (k : ℕ) (_ : k ≤ 48),
      ∀ (j : ℕ) (hj : j < 64),
        Normalized (eval env.toEnvironment ((varSchedule i₀ input_var k)[j]'hj)) := by
    intro k hk
    induction k with
    | zero =>
      intro j hj
      simp only [varSchedule]
      by_cases hj16 : j < 16
      · change Normalized (eval env.toEnvironment (input_var ++
          Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p))))[j])
        rw [Vector.getElem_append_left hj16]
        have h_ev : eval env.toEnvironment (input_var[j]'hj16) = input[j]'hj16 := by
          rw [getElem_eval_vector, h_input]
        rw [h_ev]
        exact h_assumptions ⟨j, hj16⟩
      · change Normalized (eval env.toEnvironment (input_var ++
          Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p))))[j])
        have hj' : j < 16 + 48 := by omega
        rw [show (input_var ++ Vector.replicate 48
              (Vector.replicate 32 (0 : Expression (F p))))[j]'hj' =
            (Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p))))[j - 16]'(by omega)
            from Vector.getElem_append_right hj' (by omega : (16 : ℕ) ≤ j)]
        rw [Vector.getElem_replicate]
        have h_eval_repl :
            eval env.toEnvironment (Vector.replicate 32 (0 : Expression (F p))) =
              Vector.replicate 32 (0 : F p) := by
          rw [CircuitType.eval_var_fields, Vector.map_replicate]; rfl
        rw [h_eval_repl]
        intro i; left; simp [Vector.getElem_replicate]
    | succ k ih =>
      have hk' : k ≤ 48 := by omega
      have hk'' : k < 48 := by omega
      specialize ih hk'
      have h_step := h_env ⟨k, hk''⟩
      rw [foldlAcc_eq_varSchedule i₀ input_var k hk''] at h_step
      simp only [ScheduleStep.circuit, ScheduleStep.elaborated, ScheduleStep.Assumptions,
        ScheduleStep.Spec, circuit_norm] at h_step
      have h_norm_m2 := ih (k + 16 - 2) (by omega)
      have h_norm_m7 := ih (k + 16 - 7) (by omega)
      have h_norm_m15 := ih (k + 16 - 15) (by omega)
      have h_norm_m16 := ih (k + 16 - 16) (by omega)
      rw [CircuitType.eval_var_fields] at h_norm_m2 h_norm_m7 h_norm_m15 h_norm_m16
      obtain ⟨_, n_wj⟩ := h_step ⟨h_norm_m2, h_norm_m7, h_norm_m15, h_norm_m16⟩
      intro j hj
      simp only [varSchedule, dif_pos hk'']
      by_cases hjk : j = k + 16
      · subst hjk
        rw [Vector.getElem_set_self, CircuitType.eval_var_fields]
        exact n_wj
      · rw [Vector.getElem_set_ne (by omega : k + 16 < 64) hj (by omega : k + 16 ≠ j)]
        exact ih j hj
  -- Discharge the per-step assumptions chain.
  intro i
  have hk : i.val < 48 := i.isLt
  have ih := h_inv i.val (le_of_lt hk)
  rw [foldlAcc_eq_varSchedule i₀ input_var i.val hk]
  simp only [ScheduleStep.circuit, ScheduleStep.elaborated, ScheduleStep.Assumptions,
    circuit_norm]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := ih (i.val + 16 - 2) (by omega); rw [CircuitType.eval_var_fields] at h; exact h
  · have h := ih (i.val + 16 - 7) (by omega); rw [CircuitType.eval_var_fields] at h; exact h
  · have h := ih (i.val + 16 - 15) (by omega); rw [CircuitType.eval_var_fields] at h; exact h
  · have h := ih (i.val + 16 - 16) (by omega); rw [CircuitType.eval_var_fields] at h; exact h

def circuit : FormalCircuit (F p) SHA256Block SHA256Schedule where
  main; elaborated; Assumptions; Spec; soundness;
  completeness := by simp only [completeness]

/-!
## 46-step variant (produces `w[16..61]`; slots 62/63 stay at their initial zeros)

Ported from bufferhe4d's 166,935 submission
(`/Users/simon/Documents/dev/Projects/zk.golf/solutions/sha-bufferhe4d-166935/MessageSchedule.lean`).

Identical fold body, `Circuit.foldlRange 46`. Downstream users must not read
slots 62/63 — they are DEAD (they keep the accumulator's initial zero words),
which is why `Spec46` only speaks about indices `< 62`.

Cost (for `Cost.lean` integration): 46 `ScheduleStep` instances, i.e.
`46 × (91 witnesses, 92 constraints) = (4186, 4232)`; cf. `scheduleStepCost`.
The witness count is verified by the `localLength` example below `main46`.
-/

/-- `ConstantLength` for the inlined 46-step fold body (91 witnesses per step);
    the `Fin 46` analogue of `constantLength`. -/
def constantLength46 :
    Circuit.ConstantLength (fun (x : SHA256Schedule (Expression (F p)) × Fin 46) => do
      let wj ← ScheduleStep.circuit
        ⟨x.1.get ⟨x.2.val + 16 - 2, by omega⟩, x.1.get ⟨x.2.val + 16 - 7, by omega⟩,
         x.1.get ⟨x.2.val + 16 - 15, by omega⟩, x.1.get ⟨x.2.val + 16 - 16, by omega⟩⟩
      return x.1.set (x.2.val + 16) wj (by omega)) where
  localLength := 91
  localLength_eq _ _ := by
    simp [circuit_norm, ScheduleStep.circuit, ScheduleStep.elaborated]

def main46 (block : SHA256Block (Expression (F p))) : Circuit (F p) (SHA256Schedule (Expression (F p))) := do
  let zero32 : Var (fields 32) (F p) := Vector.replicate 32 (0 : Expression (F p))
  let init : SHA256Schedule (Expression (F p)) := block.append (Vector.replicate 48 zero32)
  Circuit.foldlRange 46 init (fun w i => do
    let wj ← ScheduleStep.circuit
      ⟨w.get ⟨i.val + 16 - 2, by omega⟩, w.get ⟨i.val + 16 - 7, by omega⟩,
       w.get ⟨i.val + 16 - 15, by omega⟩, w.get ⟨i.val + 16 - 16, by omega⟩⟩
    return w.set (i.val + 16) wj (by omega)) constantLength46

/-- Witness-count check: `46 × 91 = 4186`. -/
example (block : SHA256Block (Expression (F p))) (n : ℕ) :
    (main46 block).localLength n = 4186 := by
  simp [circuit_norm, main46, ScheduleStep.circuit, ScheduleStep.elaborated]

/-- The current `Spec`, restricted to the first 62 words (same per-index shape,
    with the `i.val < 62` guard; slots 62/63 are dead). -/
def Spec46 (block : SHA256Block (F p)) (sched : SHA256Schedule (F p)) : Prop :=
  let block_val : Vector ℕ 16 := block.map valueBits
  let expected := Specs.SHA256.messageSchedule block_val
  ∀ i : Fin 64, i.val < 62 →
    valueBits sched[i] = expected[i] ∧ Normalized sched[i]

instance elaborated46 : ElaboratedCircuit (F p) SHA256Block SHA256Schedule main46 := by
  elaborate_circuit_with {
    output input i₀ := varSchedule i₀ input 46
  } using by
    simp only [circuit_norm]
    intros
    exact finFoldl_eq_varSchedule_46 _ _

theorem soundness46 : Soundness (F p) main46 Assumptions Spec46 := by
  -- `circuit_proof_start` only auto-unfolds definitions literally named `main` / `Spec`,
  -- so we pass `main46` / `Spec46` explicitly.
  circuit_proof_start [main46, Spec46]
  -- Inductive invariant: at every step `k ≤ 46`, the variable-level schedule matches
  -- the value-level schedule and is normalized. Identical to the 48-step invariant,
  -- with the induction bound changed to 46 (the `k < 48` guards follow by `omega`).
  have h_inv : ∀ (k : ℕ) (_ : k ≤ 46),
      (∀ (j : ℕ) (hj : j < 64),
        valueBits (eval env ((varSchedule i₀ input_var k)[j]'hj)) =
          (valSchedule (input.map valueBits) k)[j]'hj) ∧
      (∀ (j : ℕ) (hj : j < 64),
        Normalized (eval env ((varSchedule i₀ input_var k)[j]'hj))) := by
    intro k hk
    induction k with
    | zero =>
      refine ⟨?_, ?_⟩
      · intro j hj
        simp only [varSchedule, valSchedule]
        by_cases hj16 : j < 16
        · change valueBits (eval env (input_var ++
            Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p))))[j]) = _
          rw [Vector.getElem_append_left hj16]
          simp only [Vector.getElem_mapFinRange, hj16, dif_pos]
          rw [show (Vector.map valueBits input).get ⟨j, hj16⟩ =
                (Vector.map valueBits input)[j]'hj16 from rfl]
          rw [Vector.getElem_map]
          congr 1
          rw [getElem_eval_vector, h_input]
        · change valueBits (eval env (input_var ++
            Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p))))[j]) = _
          have hj' : j < 16 + 48 := by omega
          rw [show (input_var ++ Vector.replicate 48
                (Vector.replicate 32 (0 : Expression (F p))))[j]'hj' =
              (Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p))))[j - 16]'(by omega)
              from Vector.getElem_append_right hj' (by omega : (16 : ℕ) ≤ j)]
          rw [Vector.getElem_replicate]
          simp only [Vector.getElem_mapFinRange, hj16, dif_neg, not_false_eq_true]
          have h_eval_repl :
              eval env (Vector.replicate 32 (0 : Expression (F p))) =
                Vector.replicate 32 (0 : F p) := by
            rw [CircuitType.eval_var_fields, Vector.map_replicate]; rfl
          unfold valueBits
          rw [h_eval_repl]
          simp [Vector.getElem_replicate]
      · intro j hj
        simp only [varSchedule]
        by_cases hj16 : j < 16
        · change Normalized (eval env (input_var ++
            Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p))))[j])
          rw [Vector.getElem_append_left hj16]
          have h_ev : eval env (input_var[j]'hj16) = input[j]'hj16 := by
            rw [getElem_eval_vector, h_input]
          rw [h_ev]
          exact h_assumptions ⟨j, hj16⟩
        · change Normalized (eval env (input_var ++
            Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p))))[j])
          have hj' : j < 16 + 48 := by omega
          rw [show (input_var ++ Vector.replicate 48
                (Vector.replicate 32 (0 : Expression (F p))))[j]'hj' =
              (Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p))))[j - 16]'(by omega)
              from Vector.getElem_append_right hj' (by omega : (16 : ℕ) ≤ j)]
          rw [Vector.getElem_replicate]
          have h_eval_repl :
              eval env (Vector.replicate 32 (0 : Expression (F p))) =
                Vector.replicate 32 (0 : F p) := by
            rw [CircuitType.eval_var_fields, Vector.map_replicate]; rfl
          rw [h_eval_repl]
          intro i; left; simp [Vector.getElem_replicate]
    | succ k ih =>
      have hk' : k ≤ 46 := by omega
      have hk'' : k < 46 := by omega
      have hk48 : k < 48 := by omega
      obtain ⟨ih_val, ih_norm⟩ := ih hk'
      have h_step := h_holds ⟨k, hk''⟩
      rw [foldlAcc_eq_varSchedule46 i₀ input_var k hk''] at h_step
      simp only [ScheduleStep.circuit, ScheduleStep.elaborated, ScheduleStep.Assumptions,
        ScheduleStep.Spec, circuit_norm] at h_step
      have h_norm_m2 := ih_norm (k + 16 - 2) (by omega)
      have h_norm_m7 := ih_norm (k + 16 - 7) (by omega)
      have h_norm_m15 := ih_norm (k + 16 - 15) (by omega)
      have h_norm_m16 := ih_norm (k + 16 - 16) (by omega)
      rw [CircuitType.eval_var_fields] at h_norm_m2 h_norm_m7 h_norm_m15 h_norm_m16
      obtain ⟨v_wj, n_wj⟩ := h_step ⟨h_norm_m2, h_norm_m7, h_norm_m15, h_norm_m16⟩
      have ih_val' : ∀ (j : ℕ) (hj : j < 64),
          valueBits (Vector.map (Expression.eval env)
            (Vector.get (varSchedule i₀ input_var k) ⟨j, hj⟩)) =
            (valSchedule (input.map valueBits) k)[j]'hj := by
        intro j hj
        rw [show Vector.get (varSchedule i₀ input_var k) ⟨j, hj⟩ =
              (varSchedule i₀ input_var k)[j]'hj from rfl, ← CircuitType.eval_var_fields]
        exact ih_val j hj
      refine ⟨?_, ?_⟩
      · intro j hj
        simp only [varSchedule, valSchedule, dif_pos hk48]
        by_cases hjk : j = k + 16
        · subst hjk
          rw [Vector.getElem_set_self, Vector.getElem_set_self]
          rw [show (varFromOffset (fields 32) (i₀ + k * 91 + 58) : Vector (Expression (F p)) 32) =
                Vector.mapRange 32 (fun i => (var { index := i₀ + k * 91 + 58 + i } : Expression (F p)))
              from by simp [varFromOffset, ProvableType.varFromOffset, fromElements, size]]
          rw [CircuitType.eval_var_fields, v_wj,
            ih_val' (k + 16 - 2) (by omega), ih_val' (k + 16 - 7) (by omega),
            ih_val' (k + 16 - 15) (by omega), ih_val' (k + 16 - 16) (by omega)]
        · rw [Vector.getElem_set_ne (by omega : k + 16 < 64) hj (by omega : k + 16 ≠ j)]
          rw [Vector.getElem_set_ne (by omega : k + 16 < 64) hj (by omega : k + 16 ≠ j)]
          exact ih_val j hj
      · intro j hj
        simp only [varSchedule, dif_pos hk48]
        by_cases hjk : j = k + 16
        · subst hjk
          rw [Vector.getElem_set_self]
          rw [show (i₀ + k * 91 + 58 : ℕ) = i₀ + k * 91 + 29 + 22 + 6 + 1 from by omega]
          rw [show (varFromOffset (fields 32) (i₀ + k * 91 + 29 + 22 + 6 + 1) :
                Vector (Expression (F p)) 32) =
                Vector.mapRange 32 (fun i =>
                  (var { index := i₀ + k * 91 + 29 + 22 + 6 + 1 + i } : Expression (F p)))
              from by simp [varFromOffset, ProvableType.varFromOffset, fromElements, size]]
          rw [CircuitType.eval_var_fields]
          exact n_wj
        · rw [Vector.getElem_set_ne (by omega : k + 16 < 64) hj (by omega : k + 16 ≠ j)]
          exact ih_norm j hj
  obtain ⟨h_val_46, h_norm_46⟩ := h_inv 46 (le_refl 46)
  refine ⟨?_, ?_⟩
  · intro i hi
    have h_bridge :
        (eval env (varSchedule i₀ input_var 46))[i.val] =
          eval env ((varSchedule i₀ input_var 46)[i.val]'i.isLt) :=
      (getElem_eval_vector (α := fields 32) (n := 64) env (varSchedule i₀ input_var 46) i.val i.isLt).symm
    refine ⟨?_, ?_⟩
    · rw [h_bridge]
      exact (h_val_46 i.val i.isLt).trans
        (messageSchedule_getElem_eq_valSchedule_46 (input.map valueBits) i.val hi).symm
    · rw [h_bridge]
      exact h_norm_46 i.val i.isLt
  · intro i
    simp [ScheduleStep.circuit, circuit_norm]

theorem completeness46 : Completeness (F p) (Input := SHA256Block) (Output := SHA256Schedule) main46 Assumptions := by
  circuit_proof_start [main46]
  -- Inductive invariant: at every step k ≤ 46, every slot of `varSchedule i₀ input_var k`
  -- is Normalized.
  have h_inv : ∀ (k : ℕ) (_ : k ≤ 46),
      ∀ (j : ℕ) (hj : j < 64),
        Normalized (eval env.toEnvironment ((varSchedule i₀ input_var k)[j]'hj)) := by
    intro k hk
    induction k with
    | zero =>
      intro j hj
      simp only [varSchedule]
      by_cases hj16 : j < 16
      · change Normalized (eval env.toEnvironment (input_var ++
          Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p))))[j])
        rw [Vector.getElem_append_left hj16]
        have h_ev : eval env.toEnvironment (input_var[j]'hj16) = input[j]'hj16 := by
          rw [getElem_eval_vector, h_input]
        rw [h_ev]
        exact h_assumptions ⟨j, hj16⟩
      · change Normalized (eval env.toEnvironment (input_var ++
          Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p))))[j])
        have hj' : j < 16 + 48 := by omega
        rw [show (input_var ++ Vector.replicate 48
              (Vector.replicate 32 (0 : Expression (F p))))[j]'hj' =
            (Vector.replicate 48 (Vector.replicate 32 (0 : Expression (F p))))[j - 16]'(by omega)
            from Vector.getElem_append_right hj' (by omega : (16 : ℕ) ≤ j)]
        rw [Vector.getElem_replicate]
        have h_eval_repl :
            eval env.toEnvironment (Vector.replicate 32 (0 : Expression (F p))) =
              Vector.replicate 32 (0 : F p) := by
          rw [CircuitType.eval_var_fields, Vector.map_replicate]; rfl
        rw [h_eval_repl]
        intro i; left; simp [Vector.getElem_replicate]
    | succ k ih =>
      have hk' : k ≤ 46 := by omega
      have hk'' : k < 46 := by omega
      have hk48 : k < 48 := by omega
      specialize ih hk'
      have h_step := h_env ⟨k, hk''⟩
      rw [foldlAcc_eq_varSchedule46 i₀ input_var k hk''] at h_step
      simp only [ScheduleStep.circuit, ScheduleStep.elaborated, ScheduleStep.Assumptions,
        ScheduleStep.Spec, circuit_norm] at h_step
      have h_norm_m2 := ih (k + 16 - 2) (by omega)
      have h_norm_m7 := ih (k + 16 - 7) (by omega)
      have h_norm_m15 := ih (k + 16 - 15) (by omega)
      have h_norm_m16 := ih (k + 16 - 16) (by omega)
      rw [CircuitType.eval_var_fields] at h_norm_m2 h_norm_m7 h_norm_m15 h_norm_m16
      obtain ⟨_, n_wj⟩ := h_step ⟨h_norm_m2, h_norm_m7, h_norm_m15, h_norm_m16⟩
      intro j hj
      simp only [varSchedule, dif_pos hk48]
      by_cases hjk : j = k + 16
      · subst hjk
        rw [Vector.getElem_set_self, CircuitType.eval_var_fields]
        exact n_wj
      · rw [Vector.getElem_set_ne (by omega : k + 16 < 64) hj (by omega : k + 16 ≠ j)]
        exact ih j hj
  -- Discharge the per-step assumptions chain.
  intro i
  have hk : i.val < 46 := i.isLt
  have ih := h_inv i.val (le_of_lt hk)
  rw [foldlAcc_eq_varSchedule46 i₀ input_var i.val hk]
  simp only [ScheduleStep.circuit, ScheduleStep.elaborated, ScheduleStep.Assumptions,
    circuit_norm]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := ih (i.val + 16 - 2) (by omega); rw [CircuitType.eval_var_fields] at h; exact h
  · have h := ih (i.val + 16 - 7) (by omega); rw [CircuitType.eval_var_fields] at h; exact h
  · have h := ih (i.val + 16 - 15) (by omega); rw [CircuitType.eval_var_fields] at h; exact h
  · have h := ih (i.val + 16 - 16) (by omega); rw [CircuitType.eval_var_fields] at h; exact h

def circuit46 : FormalCircuit (F p) SHA256Block SHA256Schedule where
  main := main46
  elaborated := elaborated46
  Assumptions
  Spec := Spec46
  soundness := soundness46
  completeness := by simp only [completeness46]

end MessageSchedule
end Solution.SHA256
end
