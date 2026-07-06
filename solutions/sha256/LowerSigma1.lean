import Solution.SHA256.Xor3
import Solution.SHA256.Theorems

section
variable {p : ℕ} [Fact p.Prime] [Fact (p > 2^35)]

namespace Solution.SHA256

/-!
# σ₁ (lower sigma 1) for SHA-256

σ₁(x) = ROTR17(x) XOR ROTR19(x) XOR SHR10(x)

One xor3 call = 32 witnesses total.

Mirrors `LowerSigma0` with constants 17, 19, 10 instead of 7, 18, 3.
Reuses the shared helper lemmas in `Theorems`.
-/

namespace LowerSigma1

/-- σ₁(x) = ROTR17(x) XOR ROTR19(x) XOR SHR10(x) -/
def lowerSigma1 (x : Var (fields 32) (F p)) : Circuit (F p) (Var (fields 32) (F p)) := do
  Xor3.circuit ⟨rotr32 17 x, rotr32 19 x, shr32 10 x⟩

def main (x : Var (fields 32) (F p)) : Circuit (F p) (Var (fields 32) (F p)) :=
  lowerSigma1 x

def Assumptions (x : fields 32 (F p)) : Prop := Normalized x

def Spec (x : fields 32 (F p)) (z : fields 32 (F p)) : Prop :=
  valueBits z = Specs.SHA256.lowerSigma1 (valueBits x) ∧ Normalized z

/-! ## Soundness / Completeness

This gadget composes one `Xor3.circuit` subcircuit over `rotr32`/`shr32` of the
input. Both proofs reuse `Xor3`'s `Assumptions`/`Spec` and the shared
`Normalized_eval_*` / `valueBits_eval_*` bridges in `Theorems`; they never touch
witness indices. -/

instance elaborated : ElaboratedCircuit (F p) (fields 32) (fields 32) main := by
  elaborate_circuit

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [lowerSigma1, Xor3.circuit]
  simp only [Xor3.Assumptions, Xor3.Spec, and_imp] at h_holds
  have nr17 := Normalized_eval_rotr32 env input_var input h_input h_assumptions 17
  have nr19 := Normalized_eval_rotr32 env input_var input h_input h_assumptions 19
  have ns10 := Normalized_eval_shr32 env input_var input h_input h_assumptions 10
  obtain ⟨v, n⟩ := h_holds nr17 nr19 ns10
  refine ⟨?_, n⟩
  rw [v, valueBits_eval_rotr32 env input_var input h_input h_assumptions 17,
    valueBits_eval_rotr32 env input_var input h_input h_assumptions 19,
    valueBits_eval_shr32 env input_var input h_input h_assumptions 10]
  rfl

theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [lowerSigma1, Xor3.circuit]
  simp only [Xor3.Assumptions, Xor3.Spec, and_imp] at h_env ⊢
  have nr17 := Normalized_eval_rotr32 env.toEnvironment input_var input h_input h_assumptions 17
  have nr19 := Normalized_eval_rotr32 env.toEnvironment input_var input h_input h_assumptions 19
  have ns10 := Normalized_eval_shr32 env.toEnvironment input_var input h_input h_assumptions 10
  exact ⟨nr17, nr19, ns10⟩

def circuit : FormalCircuit (F p) (fields 32) (fields 32) where
  main; elaborated; Assumptions; Spec; soundness; completeness

end LowerSigma1
end Solution.SHA256
end
