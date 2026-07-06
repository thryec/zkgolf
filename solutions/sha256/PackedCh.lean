import Solution.SHA256.BitwiseOps
import Solution.SHA256.Theorems
import Solution.SHA256.Ch32Theorems
import Solution.SHA256.PackedChRow
import Challenge.Specs.SHA256

section
variable {p : ℕ} [Fact p.Prime]

namespace Solution.SHA256

variable [Fact (p > 2^35)]

/-!
# Cross-round packed `Ch` gadget (design §6.3)

Superimposes the two rounds' choice columns into a single 32-witness column `z`,
at weights `1` and `λ = 2^40`:

  `z[j] = ch(e[j], f[j], g[j]) + 2^40 · ch(u[j], e[j], f[j])`,

where `(e, f, g)` are the round-`t` registers and `u = e_{t+1} = new_e_t`. One
R1CS row per lane (the CLASS-P `chRow`, whose unique root pins `z`). The output is
NOT a normalized bit vector: each lane holds `ch_t[j] + 2^40·ch_{t+1}[j]`.

Separated out as its own `FormalCircuit` (like `Ch32`) so the round-pair gadget
consumes it as one clean subcircuit `Spec` conjunct rather than 32 inline rows.
-/

namespace PackedCh

/-- The packed cross-round `Ch` gadget. One `chRow` (design §6.3) per lane. -/
def packedCh (e f g u : Var (fields 32) (F p)) : Circuit (F p) (Var (fields 32) (F p)) := do
  let z ← witnessVector 32 fun env =>
    Vector.ofFn fun (j : Fin 32) =>
      PackedChRow.chBit (env e[j.val]) (env f[j.val]) (env g[j.val])
        + (2^40 : F p) * PackedChRow.chBit (env u[j.val]) (env e[j.val]) (env f[j.val])
  Circuit.forEach (Vector.finRange 32) fun j =>
    assertZero
      ((-3 * e[j.val]'j.isLt + 2 * f[j.val]'j.isLt + 4 * g[j.val]'j.isLt
          + 2 * ((2^40 : F p) : Expression (F p)) * u[j.val]'j.isLt)
        * (e[j.val]'j.isLt - 2 * f[j.val]'j.isLt + 4 * g[j.val]'j.isLt
          - 2 * ((2^40 : F p) : Expression (F p)) * u[j.val]'j.isLt)
        + (3 * e[j.val]'j.isLt + (8 * ((2^40 : F p) : Expression (F p)) + 4) * f[j.val]'j.isLt
          - 8 * g[j.val]'j.isLt
          + 4 * (((2^40 : F p) : Expression (F p)) * ((2^40 : F p) : Expression (F p))) * u[j.val]'j.isLt
          - 8 * z[j.val]'j.isLt))
  return z

structure Inputs (F : Type) where
  e : fields 32 F
  f : fields 32 F
  g : fields 32 F
  u : fields 32 F
deriving ProvableStruct

def main (input : Var Inputs (F p)) : Circuit (F p) (Var (fields 32) (F p)) :=
  packedCh input.e input.f input.g input.u

def Assumptions (input : Inputs (F p)) : Prop :=
  Normalized input.e ∧ Normalized input.f ∧ Normalized input.g ∧ Normalized input.u

/-- The output column is pinned lanewise to the packed value
    `ch(e,f,g)[j] + 2^40·ch(u,e,f)[j]`. -/
def Spec (input : Inputs (F p)) (z : fields 32 (F p)) : Prop :=
  ∀ j : Fin 32, z[j] =
    PackedChRow.chBit input.e[j] input.f[j] input.g[j]
      + (2^40 : F p) * PackedChRow.chBit input.u[j] input.e[j] input.f[j]

instance elaborated : ElaboratedCircuit (F p) Inputs (fields 32) main := by
  elaborate_circuit

theorem soundness : Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [packedCh]
  obtain ⟨he, hf, hg, hu⟩ := h_assumptions
  obtain ⟨h_input_e, h_input_f, h_input_g, h_input_u⟩ := h_input
  have h_ei : ∀ i : Fin 32, Expression.eval env input_var_e[i.val] = input_e[i] := by
    intro i; have := Vector.ext_iff.mp h_input_e i i.isLt; simp [Vector.getElem_map] at this; exact this
  have h_fi : ∀ i : Fin 32, Expression.eval env input_var_f[i.val] = input_f[i] := by
    intro i; have := Vector.ext_iff.mp h_input_f i i.isLt; simp [Vector.getElem_map] at this; exact this
  have h_gi : ∀ i : Fin 32, Expression.eval env input_var_g[i.val] = input_g[i] := by
    intro i; have := Vector.ext_iff.mp h_input_g i i.isLt; simp [Vector.getElem_map] at this; exact this
  have h_ui : ∀ i : Fin 32, Expression.eval env input_var_u[i.val] = input_u[i] := by
    intro i; have := Vector.ext_iff.mp h_input_u i i.isLt; simp [Vector.getElem_map] at this; exact this
  intro j
  have h := h_holds j
  rw [h_ei j, h_fi j, h_gi j, h_ui j] at h
  exact PackedChRow.chRow_unique (he j) (hf j) (hg j) (hu j) (by linear_combination h)

theorem completeness : Completeness (F p) main Assumptions := by
  circuit_proof_start [packedCh]
  obtain ⟨he, hf, hg, hu⟩ := h_assumptions
  obtain ⟨h_input_e, h_input_f, h_input_g, h_input_u⟩ := h_input
  have h_ei : ∀ i : Fin 32, Expression.eval env.toEnvironment input_var_e[i.val] = input_e[i] := by
    intro i; have := Vector.ext_iff.mp h_input_e i i.isLt; simp [Vector.getElem_map] at this; exact this
  have h_fi : ∀ i : Fin 32, Expression.eval env.toEnvironment input_var_f[i.val] = input_f[i] := by
    intro i; have := Vector.ext_iff.mp h_input_f i i.isLt; simp [Vector.getElem_map] at this; exact this
  have h_gi : ∀ i : Fin 32, Expression.eval env.toEnvironment input_var_g[i.val] = input_g[i] := by
    intro i; have := Vector.ext_iff.mp h_input_g i i.isLt; simp [Vector.getElem_map] at this; exact this
  have h_ui : ∀ i : Fin 32, Expression.eval env.toEnvironment input_var_u[i.val] = input_u[i] := by
    intro i; have := Vector.ext_iff.mp h_input_u i i.isLt; simp [Vector.getElem_map] at this; exact this
  intro j
  have henv := h_env j
  simp only [Vector.getElem_ofFn] at henv
  rw [h_ei j, h_fi j, h_gi j, h_ui j] at henv
  rw [henv]
  have key : ∀ s x y u' : F p, IsBool s → IsBool x → IsBool y → IsBool u' →
      (-3 * s + 2 * x + 4 * y + 2 * (2^40 : F p) * u')
        * (s - 2 * x + 4 * y - 2 * (2^40 : F p) * u')
        + (3 * s + (8 * (2^40 : F p) + 4) * x - 8 * y
            + 4 * ((2^40 : F p) * (2^40 : F p)) * u'
            - 8 * (PackedChRow.chBit s x y + (2^40 : F p) * PackedChRow.chBit u' s x)) = 0 := by
    intro s x y u' hs hx hy hu'
    simp only [PackedChRow.chBit]
    rcases hs with h | h <;> rcases hx with h' | h' <;> rcases hy with h'' | h'' <;>
      rcases hu' with h''' | h''' <;> subst h h' h'' h''' <;> ring
  rw [h_ei j, h_fi j, h_gi j, h_ui j]
  have := key (input_e[j]) (input_f[j]) (input_g[j]) (input_u[j]) (he j) (hf j) (hg j) (hu j)
  linear_combination this

def circuit : FormalCircuit (F p) Inputs (fields 32) where
  main; elaborated; Assumptions; Spec; soundness; completeness

end PackedCh
end Solution.SHA256
end
