import Solution.SHA256.Add32
import Solution.SHA256.AddMany
import Solution.SHA256.Ch32
import Solution.SHA256.Maj32
import Solution.SHA256.UpperSigma0
import Solution.SHA256.UpperSigma1
import Challenge.Specs.SHA256

section
variable {p : ℕ} [Fact p.Prime]

namespace Solution.SHA256

variable [Fact (p > 2^35)]

/-!
# SHA-256 Round Function

Implements one round of the SHA-256 compression function at the bit level,
using only R1CS constraints (no lookup tables).

State convention: `Vector (Var (fields 32) (F p)) 8` holds [a, b, c, d, e, f, g, h],
where each word is a 32-bit vector with LSB at index 0.

Witness count per round (fused additions):
  upperSigma1 = 32, ch32 = 32, upperSigma0 = 32, maj32 = 32
  new_e = fused add of 6 words = 34, new_a = fused `+1` add of 4 words = 33
  Total: 32 + 32 + 32 + 32 + 34 + 33 = 195

The additions are fused: rather than chaining two-input `Add32` gadgets (each a
separate 32-bit decomposition + carry), each of `new_e` and `new_a` is computed
with a single multi-word `AddMany` decomposition. For `new_a = t1 + t2` we reuse
the already-decomposed `new_e`: modulo `2^32`, `t1 ≡ new_e − d ≡ new_e + ¬d + 1`
(two's complement), so `new_a ≡ new_e + Σ₀ + Maj + ¬d + 1` — a 4-word `+1` adder
(`AddMany.circuit2c`), where `¬d` is the free affine bit-complement of `d`.
-/

namespace SHA256Round

/-- One round of SHA-256 compression.

    state = [a, b, c, d, e, f, g, h], each a 32-bit word (fields 32).
    k: round constant as a 32-bit word.
    w: message schedule word as a 32-bit word.
-/
def sha256Round
    (state : Vector (Var (fields 32) (F p)) 8)
    (k w : Var (fields 32) (F p))
    : Circuit (F p) (Vector (Var (fields 32) (F p)) 8) := do
  let a := state[0]; let b := state[1]; let c := state[2]; let d := state[3]
  let e := state[4]; let f := state[5]; let g := state[6]; let h := state[7]
  let sig1  ← UpperSigma1.circuit e
  let ch    ← Ch32.circuit ⟨e, f, g⟩
  let sig0  ← UpperSigma0.circuit a
  let maj   ← Maj32.circuit ⟨a, b, c⟩
  -- new_e = d + h + Σ₁(e) + Ch(e,f,g) + k + w   (mod 2^32)
  let new_e ← AddMany.circuit (n := 6) (by norm_num) #v[d, h, sig1, ch, k, w]
  -- new_a = new_e + Σ₀(a) + Maj(a,b,c) + ¬d + 1   (mod 2^32)
  --       ≡ h + Σ₁(e) + Ch(e,f,g) + k + w + Σ₀(a) + Maj(a,b,c)
  let new_a ← AddMany.circuit2c (n := 4) (by norm_num) #v[new_e, sig0, maj, not32 d]
  return #v[new_a, a, b, c, new_e, e, f, g]

structure Inputs (F : Type) where
  state : SHA256State F
  k : fields 32 F
  w : fields 32 F
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var SHA256State (F p)) :=
  sha256Round input.state input.k input.w

def Assumptions (input : Inputs (F p)) : Prop :=
  (∀ i : Fin 8, Normalized input.state[i]) ∧ Normalized input.k ∧ Normalized input.w

def Spec (input : Inputs (F p)) (out : SHA256State (F p)) : Prop :=
  out.map valueBits =
    Specs.SHA256.sha256Round (input.state.map valueBits) (valueBits input.k) (valueBits input.w)
  ∧ ∀ i : Fin 8, Normalized out[i]

instance elaborated : ElaboratedCircuit (F p) _ _ main := by
  elaborate_circuit

/-- Evaluating the pure `not32` combinator gives the elementwise complement. -/
lemma not32_eval (env : Environment (F p)) (x_var : Var (fields 32) (F p)) :
    Vector.map (Expression.eval env) (not32 x_var) =
      (Vector.map (Expression.eval env) x_var).map (fun xi => 1 - xi) := by
  ext i hi
  simp [not32, Vector.getElem_map, circuit_norm]
  ring

/-- The complement of a normalized word is normalized. -/
lemma normalized_not (x : fields 32 (F p)) (hx : Normalized x) :
    Normalized (x.map fun xi => 1 - xi) := by
  intro i
  simp only [Fin.getElem_fin, Vector.getElem_map]
  rcases hx i with h | h
  · rw [Fin.getElem_fin] at h; rw [h]; right; norm_num
  · rw [Fin.getElem_fin] at h; rw [h]; left; norm_num

/-- Sum of the first `n` powers of two. -/
private lemma sum_two_pow (n : ℕ) : ∑ i : Fin n, (2:ℕ)^i.val = 2^n - 1 := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih]
    have h2m : (2:ℕ)^(m+1) = 2 * 2^m := by ring
    have h1 : (1:ℕ) ≤ 2^m := Nat.one_le_two_pow
    omega

/-- The complement of a normalized word has the two's-complement value. -/
lemma valueBits_not (x : fields 32 (F p)) (hx : Normalized x) :
    valueBits (x.map fun xi => 1 - xi) = 2^32 - 1 - valueBits x := by
  have key : valueBits (x.map fun xi => 1 - xi) + valueBits x = 2^32 - 1 := by
    simp only [valueBits]
    rw [← Finset.sum_add_distrib]
    have hterm : ∀ i : Fin 32,
        ((x.map fun xi => 1 - xi)[i]).val * 2^i.val + (x[i]).val * 2^i.val = 2^i.val := by
      intro i
      simp only [Fin.getElem_fin, Vector.getElem_map]
      rcases hx i with h | h <;> rw [Fin.getElem_fin] at h <;> rw [h] <;>
        norm_num [ZMod.val_zero, ZMod.val_one]
    rw [Finset.sum_congr rfl (fun i _ => hterm i)]
    exact sum_two_pow 32
  omega

set_option maxHeartbeats 4000000 in
theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [sha256Round, UpperSigma1.circuit, UpperSigma0.circuit,
    Ch32.circuit, Maj32.circuit, AddMany.circuit, AddMany.circuit2c]
  obtain ⟨h_state_norm, h_k_norm, h_w_norm⟩ := h_assumptions
  obtain ⟨h_input_state, h_input_k, h_input_w⟩ := h_input
  have h_eval : ∀ (i : ℕ) (hi : i < 8),
      Vector.map (Expression.eval env) (input_var_state[i]'hi) = input_state[i]'hi := by
    intro i hi
    have h := getElem_eval_vector env input_var_state i hi
    rw [h_input_state] at h
    rw [← CircuitType.eval_var_fields env (input_var_state[i]'hi)]
    exact h
  simp only [UpperSigma1.Assumptions, UpperSigma0.Assumptions, Ch32.Assumptions,
    Maj32.Assumptions, UpperSigma1.Spec, UpperSigma0.Spec, Ch32.Spec, Maj32.Spec,
    AddMany.Assumptions, AddMany.Spec, AddMany.Spec2c, and_imp] at h_holds
  obtain ⟨c_sig1, c_ch, c_sig0, c_maj, c_newe, c_newa⟩ := h_holds
  have s_sig1 := c_sig1 (by rw [h_eval 4 (by omega)]; exact h_state_norm 4)
  have s_ch := c_ch (by rw [h_eval 4 (by omega)]; exact h_state_norm 4)
    (by rw [h_eval 5 (by omega)]; exact h_state_norm 5) (by rw [h_eval 6 (by omega)]; exact h_state_norm 6)
  have s_sig0 := c_sig0 (by rw [h_eval 0 (by omega)]; exact h_state_norm 0)
  have s_maj := c_maj (by rw [h_eval 0 (by omega)]; exact h_state_norm 0)
    (by rw [h_eval 1 (by omega)]; exact h_state_norm 1) (by rw [h_eval 2 (by omega)]; exact h_state_norm 2)
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
    · rw [h_input_k]; exact h_k_norm
    · rw [h_input_w]; exact h_w_norm)
  have s_newa := c_newa (by
    intro i
    fin_cases i <;>
      (rw [Fin.getElem_fin, red];
        simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
          List.getElem_cons_succ])
    · exact s_newe.2
    · exact s_sig0.2
    · exact s_maj.2
    · rw [not32_eval env (input_var_state[3]'(by norm_num)), h_eval 3 (by omega)]
      exact normalized_not _ (h_state_norm 3))
  -- The large subcircuit-constraint hypotheses are fully consumed; clearing them keeps the
  -- `get_elem_tactic` bound synthesis for `input_state[i]` from scanning a huge context.
  clear c_sig1 c_ch c_sig0 c_maj c_newe c_newa
  -- Reassociate a flat modular sum into the spec's nested `add32` shape (over plain ℕ,
  -- so `omega` never inspects the heavy `valueBits`/`Specs` atoms).
  have mod6 : ∀ x0 x1 x2 x3 x4 x5 : ℕ,
      (x0 + x1 + x2 + x3 + x4 + x5) % 2 ^ 32 =
        _root_.add32 x0 (_root_.add32 (_root_.add32 (_root_.add32 (_root_.add32 x1 x2) x3) x4) x5) := by
    intro x0 x1 x2 x3 x4 x5; unfold _root_.add32; omega
  -- Two's-complement reassociation: `new_e ≡ d + t1` implies
  -- `new_e + y5 + y6 + ¬d + 1 ≡ t1 + y5 + y6 (mod 2^32)`.
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
            (valueBits input_k)) (valueBits input_w)) := by
    rw [s_newe.1, Fin.sum_univ_six]
    simp only [Fin.getElem_fin, red,
      show ((0:Fin 6):ℕ)=0 from rfl, show ((1:Fin 6):ℕ)=1 from rfl, show ((2:Fin 6):ℕ)=2 from rfl,
      show ((3:Fin 6):ℕ)=3 from rfl, show ((4:Fin 6):ℕ)=4 from rfl, show ((5:Fin 6):ℕ)=5 from rfl,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
    rw [s_sig1.1, s_ch.1, h_eval 3 (by norm_num), h_eval 4 (by norm_num), h_eval 5 (by norm_num),
      h_eval 6 (by norm_num), h_eval 7 (by norm_num), h_input_k, h_input_w]
    exact mod6 _ _ _ _ _ _
  have v_newa : valueBits (Vector.map (Expression.eval env)
        (Vector.mapRange 32 fun i ↦ var { index := i₀ + 32 + 32 + 32 + 32 + 34 + i })) =
      _root_.add32
        (_root_.add32 (_root_.add32 (_root_.add32 (_root_.add32 (valueBits (input_state[7]'(by norm_num)))
            (Specs.SHA256.upperSigma1 (valueBits (input_state[4]'(by norm_num)))))
            (Specs.SHA256.Ch (valueBits (input_state[4]'(by norm_num))) (valueBits (input_state[5]'(by norm_num))) (valueBits (input_state[6]'(by norm_num)))))
            (valueBits input_k)) (valueBits input_w))
        (_root_.add32 (Specs.SHA256.upperSigma0 (valueBits (input_state[0]'(by norm_num))))
            (Specs.SHA256.Maj (valueBits (input_state[0]'(by norm_num))) (valueBits (input_state[1]'(by norm_num))) (valueBits (input_state[2]'(by norm_num))))) := by
    rw [s_newa.1, Fin.sum_univ_four]
    simp only [Fin.getElem_fin, red,
      show ((0:Fin 4):ℕ)=0 from rfl, show ((1:Fin 4):ℕ)=1 from rfl, show ((2:Fin 4):ℕ)=2 from rfl,
      show ((3:Fin 4):ℕ)=3 from rfl,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
    rw [v_newe, s_sig0.1, s_maj.1, h_eval 0 (by norm_num), h_eval 1 (by norm_num),
      h_eval 2 (by norm_num),
      not32_eval env (input_var_state[3]'(by norm_num)), h_eval 3 (by norm_num),
      valueBits_not (input_state[3]'(by norm_num)) (h_state_norm 3)]
    exact modc _ _ _ _ hd_lt
  have e : ∀ (i : ℕ) (hi : i < 8),
      valueBits (Vector.map (Expression.eval env) (input_var_state[i]'hi)) = valueBits (input_state[i]'hi) :=
    fun i hi => congrArg valueBits (h_eval i hi)
  refine ⟨?_, ?_⟩
  · simp only [eval_vector, Vector.map_mk, List.map_toArray, List.map_cons, List.map_nil, circuit_norm]
    simp only [Specs.SHA256.sha256Round, Vector.getElem_map]
    rw [v_newa, v_newe, e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num),
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
  circuit_proof_start [sha256Round, UpperSigma1.circuit, UpperSigma0.circuit,
    Ch32.circuit, Maj32.circuit, AddMany.circuit, AddMany.circuit2c]
  obtain ⟨h_state_norm, h_k_norm, h_w_norm⟩ := h_assumptions
  obtain ⟨h_input_state, h_input_k, h_input_w⟩ := h_input
  have h_eval : ∀ (i : ℕ) (hi : i < 8),
      Vector.map (Expression.eval env.toEnvironment) (input_var_state[i]'hi) = input_state[i]'hi := by
    intro i hi
    have h := getElem_eval_vector env.toEnvironment input_var_state i hi
    rw [h_input_state] at h
    rw [← CircuitType.eval_var_fields env.toEnvironment (input_var_state[i]'hi)]
    exact h
  simp only [UpperSigma1.Assumptions, UpperSigma0.Assumptions, Ch32.Assumptions,
    Maj32.Assumptions, UpperSigma1.Spec, UpperSigma0.Spec, Ch32.Spec, Maj32.Spec,
    AddMany.Assumptions, AddMany.Spec, AddMany.Spec2c, and_imp] at h_env ⊢
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
    · rw [h_input_k]; exact h_k_norm
    · rw [h_input_w]; exact h_w_norm)
  refine ⟨n4, ⟨n4, n5, n6⟩, n0, ⟨n0, n1, n2⟩, ?_, ?_⟩
  · intro i
    fin_cases i <;>
      (rw [Fin.getElem_fin, red];
        simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
          List.getElem_cons_succ])
    · rw [h_eval 3 (by norm_num)]; exact h_state_norm 3
    · rw [h_eval 7 (by norm_num)]; exact h_state_norm 7
    · exact s_sig1.2
    · exact s_ch.2
    · rw [h_input_k]; exact h_k_norm
    · rw [h_input_w]; exact h_w_norm
  · intro i
    fin_cases i <;>
      (rw [Fin.getElem_fin, red];
        simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
          List.getElem_cons_succ])
    · exact s_newe.2
    · exact s_sig0.2
    · exact s_maj.2
    · rw [not32_eval env.toEnvironment (input_var_state[3]'(by norm_num)), h_eval 3 (by norm_num)]
      exact normalized_not _ (h_state_norm 3)

def circuit : FormalCircuit (F p) Inputs SHA256State where
  main; elaborated; Assumptions; Spec; soundness; completeness

end SHA256Round
end Solution.SHA256
end
