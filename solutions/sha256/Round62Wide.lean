import Solution.SHA256.AddManyWide
import Solution.SHA256.SHA256Round
import Solution.SHA256.Round63DM
import Challenge.Specs.SHA256
import Challenge.Utils.CostR1CS
import Challenge.Instances.SHA256.Interface

section
variable {p : ℕ} [Fact p.Prime]

namespace Solution.SHA256

variable [Fact (p > 2^35)] [Fact (p > 2^37)]

/-!
# Round 62 with a wide (unreduced) schedule-word addend

Standard SHA-256 round specialized to round index 62, whose schedule word
arrives as a *single wide field element* `wide` carrying the unreduced
schedule sum (`wide.val < 2^34`, as produced by `ScheduleStepLast`). The
`new_e` adder is the fused `AddManyWide` gadget over the 5 bit-decomposed
words `[d, h, Σ₁(e), Ch(e,f,g), K₆₂]` plus the wide addend; `new_a` reuses the
decomposed `new_e` via the two's-complement trick exactly as `SHA256Round`.

Cost: 4 × (32,32) bitwise gadgets + AddManyWide (35,36) + AddMany2c (33,34)
= 196 allocations, 198 constraints.
-/

namespace Round62Wide

structure Inputs (F : Type) where
  state : SHA256State F
  wide : field F
deriving ProvableStruct

/-- The round-62 constant `K[62] = 0xbef9a3f7` as a `ℕ` literal. Using
`Specs.SHA256.K[62].toNat` directly inside `main` makes `elaborate_circuit`'s
normalization + kernel check blow up (deep recursion reducing the `UInt32`
vector lookup under `constWord32`), so `main` uses this literal and the
soundness proof bridges to the spec's `Specs.SHA256.K[62].toNat` via
`k62Nat_eq`. -/
def k62Nat : ℕ := 0xbef9a3f7

lemma k62Nat_eq : k62Nat = Specs.SHA256.K[62].toNat := by decide

lemma k62Nat_lt : k62Nat < 2^32 := by norm_num [k62Nat]

/-- Round 62: standard round shape, with the schedule word supplied as the
wide unreduced addend `input.wide` (value `< 2^34`). -/
def main (input : Var Inputs (F p)) : Circuit (F p) (Var SHA256State (F p)) := do
  let a := input.state[0]; let b := input.state[1]; let c := input.state[2]
  let d := input.state[3]; let e := input.state[4]; let f := input.state[5]
  let g := input.state[6]; let h := input.state[7]
  let sig1 ← UpperSigma1.circuit e
  let ch   ← Ch32.circuit ⟨e, f, g⟩
  let sig0 ← UpperSigma0.circuit a
  let maj  ← Maj32.circuit ⟨a, b, c⟩
  let k62 := constWord32 (p := p) k62Nat
  -- new_e = d + h + Σ₁(e) + Ch(e,f,g) + K₆₂ + wide   (mod 2^32)
  let new_e ← subcircuit (AddManyWide.circuit (by norm_num : 5 ≤ 7))
    ⟨#v[d, h, sig1, ch, k62], input.wide⟩
  -- new_a = new_e + Σ₀(a) + Maj(a,b,c) + ¬d + 1   (mod 2^32)
  let new_a ← AddMany.circuit2c (by norm_num) #v[new_e, sig0, maj, not32 d]
  return #v[new_a, a, b, c, new_e, e, f, g]

def Assumptions (input : Inputs (F p)) : Prop :=
  (∀ i : Fin 8, Normalized input.state[i]) ∧ input.wide.val < 2^34

def Spec (input : Inputs (F p)) (out : SHA256State (F p)) : Prop :=
  out.map valueBits =
    Specs.SHA256.sha256Round (input.state.map valueBits) (Specs.SHA256.K[62].toNat)
      (input.wide.val % 2^32)
  ∧ ∀ i : Fin 8, Normalized out[i]

instance elaborated : ElaboratedCircuit (F p) Inputs SHA256State main := by
  elaborate_circuit

set_option maxHeartbeats 4000000 in
theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [UpperSigma1.circuit, UpperSigma0.circuit,
    Ch32.circuit, Maj32.circuit, AddManyWide.circuit, AddMany.circuit2c]
  obtain ⟨h_state_norm, h_wide_lt⟩ := h_assumptions
  obtain ⟨h_input_state, -⟩ := h_input
  have h_eval : ∀ (i : ℕ) (hi : i < 8),
      Vector.map (Expression.eval env) (input_var_state[i]'hi) = input_state[i]'hi := by
    intro i hi
    have h := getElem_eval_vector env input_var_state i hi
    rw [h_input_state] at h
    rw [← CircuitType.eval_var_fields env (input_var_state[i]'hi)]
    exact h
  simp only [UpperSigma1.Assumptions, UpperSigma0.Assumptions, Ch32.Assumptions,
    Maj32.Assumptions, UpperSigma1.Spec, UpperSigma0.Spec, Ch32.Spec, Maj32.Spec,
    AddManyWide.Assumptions, AddManyWide.Spec, AddMany.Assumptions, AddMany.Spec2c,
    and_imp] at h_holds
  obtain ⟨c_sig1, c_ch, c_sig0, c_maj, c_newe, c_newa⟩ := h_holds
  have s_sig1 := c_sig1 (by rw [h_eval 4 (by omega)]; exact h_state_norm 4)
  have s_ch := c_ch (by rw [h_eval 4 (by omega)]; exact h_state_norm 4)
    (by rw [h_eval 5 (by omega)]; exact h_state_norm 5)
    (by rw [h_eval 6 (by omega)]; exact h_state_norm 6)
  have s_sig0 := c_sig0 (by rw [h_eval 0 (by omega)]; exact h_state_norm 0)
  have s_maj := c_maj (by rw [h_eval 0 (by omega)]; exact h_state_norm 0)
    (by rw [h_eval 1 (by omega)]; exact h_state_norm 1)
    (by rw [h_eval 2 (by omega)]; exact h_state_norm 2)
  have red : ∀ (m : ℕ) (V : ProvableVector (fields 32) m (Expression (F p))) (k : ℕ) (hk : k < m),
      (eval env V)[k]'hk = Vector.map (Expression.eval env) (V[k]'hk) := by
    intro m V k hk
    rw [← getElem_eval_vector env V k hk, CircuitType.eval_var_fields]
  have s_newe := c_newe (by
    intro i
    fin_cases i <;>
      (rw [Fin.getElem_fin, red];
        simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
          List.getElem_cons_succ])
    · rw [h_eval 3 (by omega)]; exact h_state_norm 3
    · rw [h_eval 7 (by omega)]; exact h_state_norm 7
    · exact s_sig1.2
    · exact s_ch.2
    · exact SHA256Rounds.normalized_constWord32 env _) h_wide_lt
  have s_newa := c_newa (by
    intro i
    fin_cases i <;>
      (rw [Fin.getElem_fin, red];
        simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
          List.getElem_cons_succ])
    · exact s_newe.2
    · exact s_sig0.2
    · exact s_maj.2
    · rw [SHA256Round.not32_eval env (input_var_state[3]'(by norm_num)), h_eval 3 (by omega)]
      exact SHA256Round.normalized_not _ (h_state_norm 3))
  -- The large subcircuit-constraint hypotheses are fully consumed.
  clear c_sig1 c_ch c_sig0 c_maj c_newe c_newa
  -- Reassociate the flat modular sum (with the wide addend reduced) into the
  -- spec's nested `add32` shape (pure ℕ): the `% 2^32` on the wide value is
  -- absorbed because `add32` reduces at each step.
  have mod5w : ∀ x0 x1 x2 x3 x4 W : ℕ,
      (x0 + x1 + x2 + x3 + x4 + W) % 2 ^ 32 =
        _root_.add32 x0 (_root_.add32
          (_root_.add32 (_root_.add32 (_root_.add32 x1 x2) x3) x4) (W % 2^32)) := by
    intro x0 x1 x2 x3 x4 W; unfold _root_.add32; omega
  -- Two's-complement reassociation, verbatim from `SHA256Round`:
  -- `new_e ≡ d + t1` implies `new_e + y5 + y6 + ¬d + 1 ≡ t1 + y5 + y6 (mod 2^32)`.
  have modc : ∀ dv t1 y5 y6 : ℕ, dv < 2^32 →
      (_root_.add32 dv t1 + y5 + y6 + (2^32 - 1 - dv) + 1) % 2 ^ 32 =
        _root_.add32 t1 (_root_.add32 y5 y6) := by
    intro dv t1 y5 y6 hdv; unfold _root_.add32; omega
  have hd_lt : valueBits (input_state[3]'(by norm_num)) < 2^32 :=
    valueBits_lt_two_pow _ (h_state_norm 3)
  -- Massage the two fused-adder outputs into the spec's `add32` shape.
  have v_newe : valueBits (Vector.map (Expression.eval env)
        (Vector.mapRange 32 fun i ↦ var { index := i₀ + 32 + 32 + 32 + 32 + i })) =
      _root_.add32 (valueBits (input_state[3]'(by norm_num)))
        (_root_.add32 (_root_.add32 (_root_.add32 (_root_.add32 (valueBits (input_state[7]'(by norm_num)))
            (Specs.SHA256.upperSigma1 (valueBits (input_state[4]'(by norm_num)))))
            (Specs.SHA256.Ch (valueBits (input_state[4]'(by norm_num))) (valueBits (input_state[5]'(by norm_num))) (valueBits (input_state[6]'(by norm_num)))))
            k62Nat) (input_wide.val % 2^32)) := by
    rw [s_newe.1, Fin.sum_univ_five]
    simp only [Fin.getElem_fin, red,
      show ((0:Fin 5):ℕ)=0 from rfl, show ((1:Fin 5):ℕ)=1 from rfl, show ((2:Fin 5):ℕ)=2 from rfl,
      show ((3:Fin 5):ℕ)=3 from rfl, show ((4:Fin 5):ℕ)=4 from rfl,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
    rw [s_sig1.1, s_ch.1,
      SHA256Rounds.valueBits_constWord32_of_lt env k62Nat_lt,
      h_eval 3 (by norm_num), h_eval 4 (by norm_num), h_eval 5 (by norm_num),
      h_eval 6 (by norm_num), h_eval 7 (by norm_num)]
    exact mod5w _ _ _ _ _ _
  have v_newa : valueBits (Vector.map (Expression.eval env)
        (Vector.mapRange 32 fun i ↦ var { index := i₀ + 32 + 32 + 32 + 32 + 35 + i })) =
      _root_.add32
        (_root_.add32 (_root_.add32 (_root_.add32 (_root_.add32 (valueBits (input_state[7]'(by norm_num)))
            (Specs.SHA256.upperSigma1 (valueBits (input_state[4]'(by norm_num)))))
            (Specs.SHA256.Ch (valueBits (input_state[4]'(by norm_num))) (valueBits (input_state[5]'(by norm_num))) (valueBits (input_state[6]'(by norm_num)))))
            k62Nat) (input_wide.val % 2^32))
        (_root_.add32 (Specs.SHA256.upperSigma0 (valueBits (input_state[0]'(by norm_num))))
            (Specs.SHA256.Maj (valueBits (input_state[0]'(by norm_num))) (valueBits (input_state[1]'(by norm_num))) (valueBits (input_state[2]'(by norm_num))))) := by
    rw [s_newa.1, Fin.sum_univ_four]
    simp only [Fin.getElem_fin, red,
      show ((0:Fin 4):ℕ)=0 from rfl, show ((1:Fin 4):ℕ)=1 from rfl, show ((2:Fin 4):ℕ)=2 from rfl,
      show ((3:Fin 4):ℕ)=3 from rfl,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
    rw [v_newe, s_sig0.1, s_maj.1, h_eval 0 (by norm_num), h_eval 1 (by norm_num),
      h_eval 2 (by norm_num),
      SHA256Round.not32_eval env (input_var_state[3]'(by norm_num)), h_eval 3 (by norm_num),
      SHA256Round.valueBits_not (input_state[3]'(by norm_num)) (h_state_norm 3)]
    exact modc _ _ _ _ hd_lt
  have e : ∀ (i : ℕ) (hi : i < 8),
      valueBits (Vector.map (Expression.eval env) (input_var_state[i]'hi)) = valueBits (input_state[i]'hi) :=
    fun i hi => congrArg valueBits (h_eval i hi)
  refine ⟨?_, ?_⟩
  · simp only [eval_vector, Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, circuit_norm]
    simp only [Specs.SHA256.sha256Round, Vector.getElem_map]
    rw [← k62Nat_eq, v_newa, v_newe, e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num),
      e 4 (by norm_num), e 5 (by norm_num), e 6 (by norm_num)]
  · intro i
    fin_cases i <;>
      (rw [red];
        simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
          List.getElem_cons_succ])
    · exact s_newa.2
    · rw [h_eval 0 (by norm_num)]; exact h_state_norm 0
    · rw [h_eval 1 (by norm_num)]; exact h_state_norm 1
    · rw [h_eval 2 (by norm_num)]; exact h_state_norm 2
    · exact s_newe.2
    · rw [h_eval 4 (by norm_num)]; exact h_state_norm 4
    · rw [h_eval 5 (by norm_num)]; exact h_state_norm 5
    · rw [h_eval 6 (by norm_num)]; exact h_state_norm 6

set_option maxHeartbeats 4000000 in
theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [UpperSigma1.circuit, UpperSigma0.circuit,
    Ch32.circuit, Maj32.circuit, AddManyWide.circuit, AddMany.circuit2c]
  obtain ⟨h_state_norm, h_wide_lt⟩ := h_assumptions
  obtain ⟨h_input_state, -⟩ := h_input
  have h_eval : ∀ (i : ℕ) (hi : i < 8),
      Vector.map (Expression.eval env.toEnvironment) (input_var_state[i]'hi) = input_state[i]'hi := by
    intro i hi
    have h := getElem_eval_vector env.toEnvironment input_var_state i hi
    rw [h_input_state] at h
    rw [← CircuitType.eval_var_fields env.toEnvironment (input_var_state[i]'hi)]
    exact h
  simp only [UpperSigma1.Assumptions, UpperSigma0.Assumptions, Ch32.Assumptions,
    Maj32.Assumptions, UpperSigma1.Spec, UpperSigma0.Spec, Ch32.Spec, Maj32.Spec,
    AddManyWide.Assumptions, AddManyWide.Spec, AddMany.Assumptions, AddMany.Spec2c,
    and_imp] at h_env ⊢
  obtain ⟨e_sig1, e_ch, e_sig0, e_maj, e_newe, -⟩ := h_env
  have red : ∀ (m : ℕ) (V : ProvableVector (fields 32) m (Expression (F p))) (k : ℕ) (hk : k < m),
      (eval env.toEnvironment V)[k]'hk = Vector.map (Expression.eval env.toEnvironment) (V[k]'hk) := by
    intro m V k hk
    rw [← getElem_eval_vector env.toEnvironment V k hk, CircuitType.eval_var_fields]
  have n0 : Normalized (Vector.map (Expression.eval env.toEnvironment) input_var_state[0]) := by
    rw [h_eval 0 (by norm_num)]; exact h_state_norm 0
  have n1 : Normalized (Vector.map (Expression.eval env.toEnvironment) input_var_state[1]) := by
    rw [h_eval 1 (by norm_num)]; exact h_state_norm 1
  have n2 : Normalized (Vector.map (Expression.eval env.toEnvironment) input_var_state[2]) := by
    rw [h_eval 2 (by norm_num)]; exact h_state_norm 2
  have n4 : Normalized (Vector.map (Expression.eval env.toEnvironment) input_var_state[4]) := by
    rw [h_eval 4 (by norm_num)]; exact h_state_norm 4
  have n5 : Normalized (Vector.map (Expression.eval env.toEnvironment) input_var_state[5]) := by
    rw [h_eval 5 (by norm_num)]; exact h_state_norm 5
  have n6 : Normalized (Vector.map (Expression.eval env.toEnvironment) input_var_state[6]) := by
    rw [h_eval 6 (by norm_num)]; exact h_state_norm 6
  have s_sig1 := e_sig1 n4
  have s_ch := e_ch n4 n5 n6
  have s_sig0 := e_sig0 n0
  have s_maj := e_maj n0 n1 n2
  have s_newe := e_newe (by
    intro i
    fin_cases i <;>
      (rw [Fin.getElem_fin, red];
        simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
          List.getElem_cons_succ])
    · rw [h_eval 3 (by norm_num)]; exact h_state_norm 3
    · rw [h_eval 7 (by norm_num)]; exact h_state_norm 7
    · exact s_sig1.2
    · exact s_ch.2
    · exact SHA256Rounds.normalized_constWord32 _ _) h_wide_lt
  refine ⟨n4, ⟨n4, n5, n6⟩, n0, ⟨n0, n1, n2⟩, ⟨?_, h_wide_lt⟩, ?_⟩
  · intro i
    fin_cases i <;>
      (rw [Fin.getElem_fin, red];
        simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
          List.getElem_cons_succ])
    · rw [h_eval 3 (by norm_num)]; exact h_state_norm 3
    · rw [h_eval 7 (by norm_num)]; exact h_state_norm 7
    · exact s_sig1.2
    · exact s_ch.2
    · exact SHA256Rounds.normalized_constWord32 _ _
  · intro i
    fin_cases i <;>
      (rw [Fin.getElem_fin, red];
        simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
          List.getElem_cons_succ])
    · exact s_newe.2
    · exact s_sig0.2
    · exact s_maj.2
    · rw [SHA256Round.not32_eval env.toEnvironment (input_var_state[3]'(by norm_num)),
        h_eval 3 (by norm_num)]
      exact SHA256Round.normalized_not _ (h_state_norm 3)

def circuit : FormalCircuit (F p) Inputs SHA256State where
  main; elaborated; Assumptions; Spec; soundness; completeness

/-! ## Cost lemmas (self-contained; the integrator merges these into `Cost.lean`)

Leaf `CostIs` facts for the four bitwise gadgets are reused from
`Round63DM`'s Cost section (same house style as `Cost.lean`); the two new
leaves here are the `AddManyWide` subcircuit (35,36) and the `+1` fused adder
`AddMany.circuit2c` (33,34). -/

section CostLemmas
open Challenge.Instances.SHA256.Interface
open Challenge.CostR1CS

theorem costIs_sub_addManyWide {n : ℕ} (hn : n ≤ 7)
    (b : Var (AddManyWide.Inputs n) (F circomPrime)) :
    CostIs (subcircuit (AddManyWide.circuit hn) b) ⟨35, 36⟩ :=
  CostIs.subcircuit (AddManyWide.costIs_addManyWide hn b.words b.wide)

theorem costIs_sub_addMany2c {n : ℕ} (hn : n ≤ 4)
    (b : Var (AddMany.Inputs n) (F circomPrime)) :
    CostIs (subcircuit (AddMany.circuit2c hn) b) ⟨33, 34⟩ :=
  CostIs.subcircuit (AddMany.costIs_addMany2c hn _)

/-- `Round62Wide.main` costs exactly 196 allocations and 198 constraints:
4 × (32,32) bitwise gadgets + AddManyWide n=5 (35,36) + AddMany2c n=4 (33,34). -/
theorem costIs_main (input : Var Inputs (F circomPrime)) :
    CostIs (main input) ⟨196, 198⟩ :=
  CostIs.bind (Round63DM.costIs_sub_upperSigma1 _) fun _ =>
  CostIs.bind (Round63DM.costIs_sub_ch32 _) fun _ =>
  CostIs.bind (Round63DM.costIs_sub_upperSigma0 _) fun _ =>
  CostIs.bind (Round63DM.costIs_sub_maj32 _) fun _ =>
  CostIs.bind (costIs_sub_addManyWide _ _) fun _ =>
  CostIs.bind (costIs_sub_addMany2c _ _) fun _ => CostIs.pure _

end CostLemmas

end Round62Wide
end Solution.SHA256
end
