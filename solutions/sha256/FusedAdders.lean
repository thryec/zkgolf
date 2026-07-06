import Solution.SHA256.SHA256Round
import Solution.SHA256.BaseLambda
import Solution.SHA256.PackedChRow
import Solution.SHA256.PackedCh
import Solution.SHA256.PackedMajRow
import Solution.SHA256.Ch32Theorems
import Solution.SHA256.Maj32Theorems
import Challenge.Instances.SHA256.Interface
import Challenge.Specs.SHA256

section
variable {p : ℕ} [Fact p.Prime]

namespace Solution.SHA256

variable [Fact (p > 2^35)]

open Challenge.Instances.SHA256.Interface (circomPrime) in
instance (priority := 100) factCircomPrimeGt2pow76 : Fact (circomPrime > 2^76) :=
  ⟨by norm_num [circomPrime]⟩

open Utils.Bits (fieldFromBits fieldFromBitsExpr)

namespace RPShared

def witBits (s : ℕ) : Vector (F p) 32 :=
  Vector.ofFn fun (j : Fin 32) => ((s % 2^32 / 2^j.val % 2 : ℕ) : F p)

def witCarry (s : ℕ) : Vector (F p) 3 :=
  Vector.ofFn fun (j : Fin 3) => ((s / 2^32 / 2^j.val % 2 : ℕ) : F p)

/-- The 2-bit carry witness: the fused A-adder derives each `new_a` lane from the
already-materialized `new_e` of its own round (a 4-term sum with the free affine
`¬d` complement), so its carry is below 4 and fits in two bits. -/
def witCarry2 (s : ℕ) : Vector (F p) 2 :=
  Vector.ofFn fun (j : Fin 2) => ((s / 2^32 / 2^j.val % 2 : ℕ) : F p)

/-- The two HIGH bits (weights 2,4) of a ≤3-bit carry; the low bit is derived
affinely from the fused recomposition row. -/
def witCarryHigh (s : ℕ) : Vector (F p) 2 :=
  Vector.ofFn fun (j : Fin 2) => ((s / 2^32 / 2^(j.val + 1) % 2 : ℕ) : F p)

/-- The single HIGH bit (weight 2) of a ≤2-bit carry; the low bit is derived
affinely from the fused recomposition row. -/
def witCarryHigh1 (s : ℕ) : Vector (F p) 1 :=
  Vector.ofFn fun (j : Fin 1) => ((s / 2^32 / 2^(j.val + 1) % 2 : ℕ) : F p)

local notation "λE" => (((2^40 : F p) : Expression (F p)))
local notation "w32E" => (((2^32 : F p) : Expression (F p)))

def carryE (c : Var (fields 3) (F p)) : Expression (F p) :=
  c[0]'(by norm_num) + (2 : Expression (F p)) * c[1]'(by norm_num)
    + (4 : Expression (F p)) * c[2]'(by norm_num)

def carryE2 (c : Var (fields 2) (F p)) : Expression (F p) :=
  c[0]'(by norm_num) + (2 : Expression (F p)) * c[1]'(by norm_num)

/-! ## Shared helper lemmas -/

lemma fused_extract [Fact (p > 2^76)] {A B nt ntp cA cB : ℕ}
    (hA : A < 2^35) (hB : B < 2^35) (hnt : nt < 2^32) (hntp : ntp < 2^32)
    (hcA : cA ≤ 7) (hcB : cB ≤ 7)
    (hfield : (A : F p) + 2^40 * (B : F p)
      = ((nt + 2^32 * cA : ℕ) : F p) + 2^40 * ((ntp + 2^32 * cB : ℕ) : F p)) :
    nt = A % 2^32 ∧ ntp = B % 2^32 := by
  have h35 : ∀ x c : ℕ, x < 2^32 → c ≤ 7 → x + 2^32 * c < 2^35 := by
    intro x c hx hc
    have e32 : (2:ℕ)^32 = 4294967296 := by norm_num
    have e35 : (2:ℕ)^35 = 34359738368 := by norm_num
    rw [e32] at hx; rw [e32, e35]; omega
  obtain ⟨e1, e2⟩ := baseLambda_sep hA hB (h35 _ _ hnt hcA) (h35 _ _ hntp hcB) hfield
  have p32 : (2:ℕ)^32 = 4294967296 := by norm_num
  rw [p32] at e1 e2
  refine ⟨?_, ?_⟩
  · rw [p32]; omega
  · rw [p32]; omega

lemma fromBitsExpr_eval_sum (env : Environment (F p)) (v : Var (fields 32) (F p)) :
    Expression.eval env (fromBitsExpr v) =
      ∑ j : Fin 32, Expression.eval env (v[j.val]'j.isLt) * (2^j.val : F p) := by
  show Expression.eval env (fieldFromBitsExpr v) = _
  rw [fieldFromBitsExpr]
  rw [AddMany.eval_foldl_add env 32 (fun j : Fin 32 => v[j.val]'j.isLt * ((2^j.val : F p) : Expression (F p)))]
  apply Finset.sum_congr rfl
  intro j _
  show Expression.eval env (Expression.mul (v[j.val]'j.isLt) (Expression.const ((2^j.val : F p)))) = _
  rw [eval_mul]
  rfl

lemma sum_bits_eq_valueBits (v : Vector (F p) 32) (hv : Normalized v) :
    (∑ j : Fin 32, v[j.val]'j.isLt * (2^j.val : F p)) = ((valueBits v : ℕ) : F p) := by
  rw [valueBits]
  push_cast
  apply Finset.sum_congr rfl
  intro j _
  rcases hv j with h | h <;> rw [Fin.getElem_fin] at h ⊢ <;> rw [h] <;>
    simp [ZMod.val_zero, ZMod.val_one]

lemma isbool_of_ringnf {x : F p} (h : -x + x ^ 2 = 0) : IsBool x :=
  Add32.isbool_of_bool_constraint (by linear_combination h)

lemma isBool_val_cases {x : F p} (h : IsBool x) : x.val = 0 ∨ x.val = 1 := by
  rcases h with h | h <;> rw [h] <;> simp [ZMod.val_zero, ZMod.val_one]

lemma isBool_cast_val {x : F p} (h : IsBool x) : x = ((x.val : ℕ) : F p) := by
  rcases h with h | h <;> rw [h] <;> simp [ZMod.val_zero, ZMod.val_one]

lemma w32_ne_zero [Fact (p > 2^76)] : (2^32 : F p) ≠ 0 := by
  have hp : (2:ℕ)^76 < p := Fact.out
  intro hcon
  have hnat : ((4294967296 : ℕ) : F p) = 0 := by exact_mod_cast hcon
  have hv := congrArg ZMod.val hnat
  rw [ZMod.val_natCast_of_lt (Nat.lt_trans (by norm_num) hp), ZMod.val_zero] at hv
  omega

lemma w32_mul_inv [Fact (p > 2^76)] : (2^32 : F p) * (2^32 : F p)⁻¹ = 1 :=
  mul_inv_cancel₀ w32_ne_zero

/-- Booleanity facts for a 2-column carry witness (values and casts). -/
lemma carry2_facts (env : Environment (F p)) (O : ℕ)
    (hb : ∀ i : Fin 2, env.get (O + i.val) * (env.get (O + i.val) + -1) = 0) :
    (∀ j : ℕ, j < 2 → (env.get (O + j)).val = 0 ∨ (env.get (O + j)).val = 1)
    ∧ (∀ j : ℕ, j < 2 → env.get (O + j) = (((env.get (O + j)).val : ℕ) : F p)) := by
  have hb' : ∀ j : ℕ, j < 2 → -env.get (O + j) + env.get (O + j) ^ 2 = 0 :=
    fun j hj => by have := hb ⟨j, hj⟩; linear_combination this
  constructor <;> intro j hj <;>
    rcases isbool_of_ringnf (hb' j hj) with h | h <;> rw [h] <;>
      simp [ZMod.val_zero, ZMod.val_one]

lemma carry_facts (env : Environment (F p)) (O : ℕ)
    (hb : ∀ i : Fin 3, env.get (O + i.val) * (env.get (O + i.val) + -1) = 0) :
    Expression.eval env (carryE (Vector.mapRange 3 fun i => var { index := O + i }))
        = (((env.get (O + 0)).val + 2 * (env.get (O + 1)).val + 4 * (env.get (O + 2)).val : ℕ) : F p)
      ∧ (env.get (O + 0)).val + 2 * (env.get (O + 1)).val + 4 * (env.get (O + 2)).val ≤ 7 := by
  have hb' : ∀ j : ℕ, j < 3 → -env.get (O + j) + env.get (O + j) ^ 2 = 0 :=
    fun j hj => by have := hb ⟨j, hj⟩; linear_combination this
  have hv : ∀ j : ℕ, j < 3 → (env.get (O + j)).val = 0 ∨ (env.get (O + j)).val = 1 := by
    intro j hj
    rcases isbool_of_ringnf (hb' j hj) with h | h <;> rw [h] <;>
      simp [ZMod.val_zero, ZMod.val_one]
  have he : ∀ j : ℕ, j < 3 → env.get (O + j) = ((env.get (O + j)).val : F p) := by
    intro j hj
    rcases isbool_of_ringnf (hb' j hj) with h | h <;> rw [h] <;>
      simp [ZMod.val_zero, ZMod.val_one]
  refine ⟨?_, ?_⟩
  · have hL : Expression.eval env (carryE (Vector.mapRange 3 fun i => var { index := O + i }))
        = env.get (O + 0) + 2 * env.get (O + 1) + 4 * env.get (O + 2) := by
      simp only [carryE]
      rw [Vector.getElem_mapRange 0 (by norm_num), Vector.getElem_mapRange 1 (by norm_num),
        Vector.getElem_mapRange 2 (by norm_num)]
      simp only [Expression.eval]
    rw [hL]
    conv_lhs => rw [he 0 (by norm_num), he 1 (by norm_num), he 2 (by norm_num)]
    push_cast
    ring
  · have h0 := hv 0 (by norm_num); have h1 := hv 1 (by norm_num); have h2 := hv 2 (by norm_num)
    omega

lemma carry_facts2 (env : Environment (F p)) (O : ℕ)
    (hb : ∀ i : Fin 2, env.get (O + i.val) * (env.get (O + i.val) + -1) = 0) :
    Expression.eval env (carryE2 (Vector.mapRange 2 fun i => var { index := O + i }))
        = (((env.get (O + 0)).val + 2 * (env.get (O + 1)).val : ℕ) : F p)
      ∧ (env.get (O + 0)).val + 2 * (env.get (O + 1)).val ≤ 3 := by
  have hb' : ∀ j : ℕ, j < 2 → -env.get (O + j) + env.get (O + j) ^ 2 = 0 :=
    fun j hj => by have := hb ⟨j, hj⟩; linear_combination this
  have hv : ∀ j : ℕ, j < 2 → (env.get (O + j)).val = 0 ∨ (env.get (O + j)).val = 1 := by
    intro j hj
    rcases isbool_of_ringnf (hb' j hj) with h | h <;> rw [h] <;>
      simp [ZMod.val_zero, ZMod.val_one]
  have he : ∀ j : ℕ, j < 2 → env.get (O + j) = ((env.get (O + j)).val : F p) := by
    intro j hj
    rcases isbool_of_ringnf (hb' j hj) with h | h <;> rw [h] <;>
      simp [ZMod.val_zero, ZMod.val_one]
  refine ⟨?_, ?_⟩
  · have hL : Expression.eval env (carryE2 (Vector.mapRange 2 fun i => var { index := O + i }))
        = env.get (O + 0) + 2 * env.get (O + 1) := by
      simp only [carryE2]
      rw [Vector.getElem_mapRange 0 (by norm_num), Vector.getElem_mapRange 1 (by norm_num)]
      simp only [Expression.eval]
    rw [hL]
    conv_lhs => rw [he 0 (by norm_num), he 1 (by norm_num)]
    push_cast
    ring
  · have h0 := hv 0 (by norm_num); have h1 := hv 1 (by norm_num)
    omega

lemma normalized_of_bool_gen (env : Environment (F p)) (o : ℕ)
    (hb : ∀ i : Fin 32, env.get (o + i.val) * (env.get (o + i.val) + -1) = 0) :
    Normalized (Vector.ofFn fun i : Fin 32 => env.get (o + i.val)) := by
  intro i
  simp only [Fin.getElem_fin, Vector.getElem_ofFn]
  exact isbool_of_ringnf (by linear_combination hb i)

lemma mod6' (x0 x1 x2 x3 x4 x5 : ℕ) :
    (x0 + x1 + x2 + x3 + x4 + x5) % 2 ^ 32 =
      _root_.add32 x0 (_root_.add32 (_root_.add32 (_root_.add32 (_root_.add32 x1 x2) x3) x4) x5) := by
  unfold _root_.add32; omega

lemma mod7' (x0 x1 x2 x3 x4 x5 x6 : ℕ) :
    (x0 + x1 + x2 + x3 + x4 + x5 + x6) % 2 ^ 32 =
      _root_.add32 (_root_.add32 (_root_.add32 (_root_.add32 (_root_.add32 x0 x1) x2) x3) x4)
        (_root_.add32 x5 x6) := by
  unfold _root_.add32; omega

/-- Two's-complement reassociation for the fused A-adder (soundness direction):
`new_e ≡ d + t1` gives `new_e + y5 + y6 + ¬d + 1 ≡ t1 + y5 + y6 (mod 2^32)`. Mirrors
the plain round's `modc` fold (`SHA256Round.lean`). -/
lemma modc' (dv t1 y5 y6 : ℕ) (hdv : dv < 2 ^ 32) :
    (_root_.add32 dv t1 + y5 + y6 + (2 ^ 32 - 1 - dv) + 1) % 2 ^ 32 =
      _root_.add32 t1 (_root_.add32 y5 y6) := by
  unfold _root_.add32; omega

/-- Two's-complement reassociation for the fused A-adder (completeness direction):
the honest 7-term `new_a` witness value equals the 4-term `¬d`-complement value once
`new_e ≡ d + t1`. -/
lemma modc_wit (dv t1 y5 y6 : ℕ) (hdv : dv < 2 ^ 32) :
    (t1 + y5 + y6) % 2 ^ 32 =
      ((dv + t1) % 2 ^ 32 + y5 + y6 + (2 ^ 32 - 1 - dv) + 1) % 2 ^ 32 := by
  omega

lemma chBit_isBool {e f g : F p} (he : IsBool e) (hf : IsBool f) (hg : IsBool g) :
    IsBool (PackedChRow.chBit e f g) := by
  unfold PackedChRow.chBit IsBool
  rcases he with h | h <;> rcases hf with h' | h' <;> rcases hg with h'' | h'' <;>
    subst h h' h'' <;> norm_num

/-- Packed column value from the per-bit pin (subcircuit-output form). -/
lemma packedZ_eval_var (env : Environment (F p)) (zvar : Var (fields 32) (F p))
    (VA VB : Vector (F p) 32) (hA : Normalized VA) (hB : Normalized VB)
    (hz : ∀ j : Fin 32,
      (Vector.map (Expression.eval env) zvar)[j.val]'j.isLt = VA[j.val]'j.isLt + (2^40 : F p) * VB[j.val]'j.isLt) :
    Expression.eval env (fromBitsExpr zvar)
      = ((valueBits VA : ℕ) : F p) + (2^40 : F p) * ((valueBits VB : ℕ) : F p) := by
  rw [fromBitsExpr_eval_sum]
  have step2 : (∑ i : Fin 32, Expression.eval env (zvar[i.val]'i.isLt) * (2^i.val : F p))
      = (∑ i : Fin 32, VA[i.val]'i.isLt * (2^i.val : F p))
        + (2^40 : F p) * (∑ i : Fin 32, VB[i.val]'i.isLt * (2^i.val : F p)) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    have hzi := hz i
    simp only [Vector.getElem_map] at hzi
    rw [hzi]; ring
  rw [step2, sum_bits_eq_valueBits VA hA, sum_bits_eq_valueBits VB hB]

lemma mapRange_eval (env : Environment (F p)) (o : ℕ) :
    Vector.map (Expression.eval env) (Vector.mapRange 32 fun i => var { index := o + i })
      = Vector.ofFn fun i : Fin 32 => env.get (o + i.val) := by
  ext i hi
  simp [Vector.getElem_map, Vector.getElem_mapRange, Vector.getElem_ofFn, Expression.eval]

/-- The 3-bit carry column recomposes to `s / 2^32` (given the honest carry witness
    and `s / 2^32 < 8`). -/
lemma carry_recompose (env : Environment (F p)) (O s : ℕ) (hs : s / 2^32 < 8)
    (hc : ∀ i : Fin 3, env.get (O + i.val) = ((s / 2^32 / 2^i.val % 2 : ℕ) : F p)) :
    Expression.eval env (carryE (Vector.mapRange 3 fun i => var { index := O + i }))
      = ((s / 2^32 : ℕ) : F p) := by
  have hL : Expression.eval env (carryE (Vector.mapRange 3 fun i => var { index := O + i }))
      = env.get (O + 0) + 2 * env.get (O + 1) + 4 * env.get (O + 2) := by
    simp only [carryE]
    rw [Vector.getElem_mapRange 0 (by norm_num), Vector.getElem_mapRange 1 (by norm_num),
      Vector.getElem_mapRange 2 (by norm_num)]
    simp only [Expression.eval]
  have c0 : env.get (O + 0) = ((s / 2^32 / 2^0 % 2 : ℕ) : F p) := hc 0
  have c1 : env.get (O + 1) = ((s / 2^32 / 2^1 % 2 : ℕ) : F p) := hc 1
  have c2 : env.get (O + 2) = ((s / 2^32 / 2^2 % 2 : ℕ) : F p) := hc 2
  rw [hL, c0, c1, c2]
  have hnat : s / 2^32 / 2^0 % 2 + 2 * (s / 2^32 / 2^1 % 2) + 4 * (s / 2^32 / 2^2 % 2) = s / 2^32 := by
    have e1 : (2:ℕ)^0 = 1 := by norm_num
    have e2 : (2:ℕ)^1 = 2 := by norm_num
    have e4 : (2:ℕ)^2 = 4 := by norm_num
    rw [e1, e2, e4]; omega
  have hc' := congrArg (Nat.cast (R := F p)) hnat
  push_cast at hc'
  linear_combination hc'

/-- The 2-bit carry column recomposes to `s / 2^32` (given the honest carry witness
    and `s / 2^32 < 4`). -/
lemma carry_recompose2 (env : Environment (F p)) (O s : ℕ) (hs : s / 2^32 < 4)
    (hc : ∀ i : Fin 2, env.get (O + i.val) = ((s / 2^32 / 2^i.val % 2 : ℕ) : F p)) :
    Expression.eval env (carryE2 (Vector.mapRange 2 fun i => var { index := O + i }))
      = ((s / 2^32 : ℕ) : F p) := by
  have hL : Expression.eval env (carryE2 (Vector.mapRange 2 fun i => var { index := O + i }))
      = env.get (O + 0) + 2 * env.get (O + 1) := by
    simp only [carryE2]
    rw [Vector.getElem_mapRange 0 (by norm_num), Vector.getElem_mapRange 1 (by norm_num)]
    simp only [Expression.eval]
  have c0 : env.get (O + 0) = ((s / 2^32 / 2^0 % 2 : ℕ) : F p) := hc 0
  have c1 : env.get (O + 1) = ((s / 2^32 / 2^1 % 2 : ℕ) : F p) := hc 1
  rw [hL, c0, c1]
  have hnat : s / 2^32 / 2^0 % 2 + 2 * (s / 2^32 / 2^1 % 2) = s / 2^32 := by
    have e1 : (2:ℕ)^0 = 1 := by norm_num
    have e2 : (2:ℕ)^1 = 2 := by norm_num
    rw [e1, e2]; omega
  have hc' := congrArg (Nat.cast (R := F p)) hnat
  push_cast at hc'
  linear_combination hc'

end RPShared

/-! # BoolVec32: assert booleanity of a 32-bit witness column -/
namespace BoolVec32

def main (v : Var (fields 32) (F p)) : Circuit (F p) Unit :=
  Circuit.forEach (Vector.finRange 32) fun i => assertZero (v[i] * (v[i] - 1))

def Assumptions (_ : fields 32 (F p)) : Prop := True

def Spec (v : fields 32 (F p)) : Prop := Normalized v

instance elaborated : ElaboratedCircuit (F p) (fields 32) unit main := by
  elaborate_circuit

theorem soundness : FormalAssertion.Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [main, Spec]
  intro i
  have hi : Expression.eval env (input_var[i.val]'i.isLt) = input[i.val]'i.isLt := by
    have h2 := congrArg (fun w => w[i.val]'i.isLt) h_input
    simpa only [Vector.getElem_map] using h2
  have h := h_holds i
  rw [hi] at h
  exact RPShared.isbool_of_ringnf (by linear_combination h)

theorem completeness : FormalAssertion.Completeness (F p) main Assumptions Spec := by
  circuit_proof_start [main, Spec]
  intro i
  have hi : Expression.eval env.toEnvironment (input_var[i.val]'i.isLt) = input[i.val]'i.isLt := by
    have h2 := congrArg (fun w => w[i.val]'i.isLt) h_input
    simpa only [Vector.getElem_map] using h2
  rw [hi]
  rcases h_spec i with h | h <;> rw [Fin.getElem_fin] at h <;> rw [h] <;> ring

attribute [irreducible] main

def circuit : FormalAssertion (F p) (fields 32) where
  main; elaborated; Assumptions; Spec; soundness; completeness

end BoolVec32

/-! # FusedEAdder -/
namespace FusedEAdder

open RPShared
local notation "λE" => (((2^40 : F p) : Expression (F p)))
local notation "w32E" => (((2^32 : F p) : Expression (F p)))

structure Inputs (F : Type) where
  newE : fields 32 F
  newEp : fields 32 F
  z : fields 32 F
  e : fields 32 F
  f : fields 32 F
  g : fields 32 F
  sig1t : fields 32 F
  sig1tp : fields 32 F
  d : fields 32 F
  h : fields 32 F
  k0 : fields 32 F
  w0 : fields 32 F
  c : fields 32 F
  k1 : fields 32 F
  w1 : fields 32 F
deriving ProvableStruct

/-- The affine derived low carry bit of the round-`t` sum: the fused
recomposition solved for the weight-1 carry bit. -/
def lowCarry (inp : Var Inputs (F p)) (ce_t : Var (fields 2) (F p))
    (ce_tp : Var (fields 3) (F p)) : Expression (F p) :=
  (((2^32 : F p)⁻¹ : F p) : Expression (F p)) *
    ((fromBitsExpr inp.d + fromBitsExpr inp.h + fromBitsExpr inp.sig1t + fromBitsExpr inp.k0 + fromBitsExpr inp.w0)
      + fromBitsExpr inp.z
      + λE * (fromBitsExpr inp.c + fromBitsExpr inp.g + fromBitsExpr inp.sig1tp + fromBitsExpr inp.k1 + fromBitsExpr inp.w1)
      - fromBitsExpr inp.newE
      - λE * (fromBitsExpr inp.newEp + w32E * RPShared.carryE ce_tp))
  - (2 : Expression (F p)) * ce_t[0]'(by norm_num) - (4 : Expression (F p)) * ce_t[1]'(by norm_num)

def main (inp : Var Inputs (F p)) : Circuit (F p) Unit := do
  let ce_t ← witnessVector 2 fun env =>
    RPShared.witCarryHigh (evalBitsNat env inp.d + evalBitsNat env inp.h + evalBitsNat env inp.sig1t
      + Specs.SHA256.Ch (evalBitsNat env inp.e) (evalBitsNat env inp.f) (evalBitsNat env inp.g)
      + evalBitsNat env inp.k0 + evalBitsNat env inp.w0)
  Circuit.forEach (Vector.finRange 2) fun i => assertZero (ce_t[i] * (ce_t[i] - 1))
  let ce_tp ← witnessVector 3 fun env =>
    RPShared.witCarry (evalBitsNat env inp.c + evalBitsNat env inp.g + evalBitsNat env inp.sig1tp
      + Specs.SHA256.Ch (evalBitsNat env inp.newE) (evalBitsNat env inp.e) (evalBitsNat env inp.f)
      + evalBitsNat env inp.k1 + evalBitsNat env inp.w1)
  Circuit.forEach (Vector.finRange 3) fun i => assertZero (ce_tp[i] * (ce_tp[i] - 1))
  assertZero (lowCarry inp ce_t ce_tp * (lowCarry inp ce_t ce_tp - 1))

def Assumptions (inp : Inputs (F p)) : Prop :=
  Normalized inp.newE ∧ Normalized inp.newEp ∧
  Normalized inp.e ∧ Normalized inp.f ∧ Normalized inp.g ∧
  Normalized inp.sig1t ∧ Normalized inp.sig1tp ∧ Normalized inp.d ∧ Normalized inp.h ∧
  Normalized inp.k0 ∧ Normalized inp.w0 ∧ Normalized inp.c ∧ Normalized inp.k1 ∧ Normalized inp.w1 ∧
  (∀ j : Fin 32, inp.z[j] = PackedChRow.chBit inp.e[j] inp.f[j] inp.g[j]
      + (2^40 : F p) * PackedChRow.chBit inp.newE[j] inp.e[j] inp.f[j])

def Spec (inp : Inputs (F p)) : Prop :=
  valueBits inp.newE = (valueBits inp.d + valueBits inp.h + valueBits inp.sig1t
      + Specs.SHA256.Ch (valueBits inp.e) (valueBits inp.f) (valueBits inp.g)
      + valueBits inp.k0 + valueBits inp.w0) % 2^32
  ∧ valueBits inp.newEp = (valueBits inp.c + valueBits inp.g + valueBits inp.sig1tp
      + Specs.SHA256.Ch (valueBits inp.newE) (valueBits inp.e) (valueBits inp.f)
      + valueBits inp.k1 + valueBits inp.w1) % 2^32

instance elaborated : ElaboratedCircuit (F p) Inputs unit main := by
  elaborate_circuit

variable [Fact (p > 2^76)]

theorem soundness : FormalAssertion.Soundness (F p) main Assumptions Spec := by
    circuit_proof_start [main, lowCarry, Assumptions, Spec]
    obtain ⟨hne_norm, hnep_norm, he_norm, hf_norm, hg_norm, hs1t_norm, hs1tp_norm, hd_norm, hh_norm,
      hk0_norm, hw0_norm, hc_norm, hk1_norm, hw1_norm, hzeq⟩ := h_assumptions
    obtain ⟨h_ne, h_nep, h_z, h_e, h_f, h_g, h_s1t, h_s1tp, h_d, h_h, h_k0, h_w0, h_c, h_k1, h_w1⟩ := h_input
    simp only [Nat.mul_zero, Nat.add_zero] at h_holds
    obtain ⟨c_cet_b, c_cetp_b, c_fused⟩ := h_holds
    set VA : fields 32 (F p) := Vector.ofFn fun j : Fin 32 => PackedChRow.chBit input_e[j.val] input_f[j.val] input_g[j.val] with hVA
    set VB : fields 32 (F p) := Vector.ofFn fun j : Fin 32 => PackedChRow.chBit input_newE[j.val] input_e[j.val] input_f[j.val] with hVB
    have hVAnorm : Normalized VA := by
      intro i; simp only [hVA, Fin.getElem_fin, Vector.getElem_ofFn]
      exact chBit_isBool (he_norm i) (hf_norm i) (hg_norm i)
    have hVBnorm : Normalized VB := by
      intro i; simp only [hVB, Fin.getElem_fin, Vector.getElem_ofFn]
      exact chBit_isBool (hne_norm i) (he_norm i) (hf_norm i)
    have hVAval : valueBits VA = Specs.SHA256.Ch (valueBits input_e) (valueBits input_f) (valueBits input_g) :=
      (Ch32.spec_of_constraint input_e input_f input_g VA he_norm hf_norm hg_norm
        (fun i => by simp only [hVA, Fin.getElem_fin, Vector.getElem_ofFn, PackedChRow.chBit])).1
    have hVBval : valueBits VB = Specs.SHA256.Ch (valueBits input_newE) (valueBits input_e) (valueBits input_f) :=
      (Ch32.spec_of_constraint input_newE input_e input_f VB hne_norm he_norm hf_norm
        (fun i => by simp only [hVB, Fin.getElem_fin, Vector.getElem_ofFn, PackedChRow.chBit])).1
    have hz' : ∀ j : Fin 32,
        (Vector.map (Expression.eval env) input_var_z)[j.val]'j.isLt = VA[j.val]'j.isLt + (2^40 : F p) * VB[j.val]'j.isLt := by
      intro j
      have hzj : (Vector.map (Expression.eval env) input_var_z)[j.val]'j.isLt = input_z[j.val]'j.isLt := by rw [h_z]
      rw [hzj, hzeq j]
      simp only [hVA, hVB, Vector.getElem_ofFn, Fin.getElem_fin]
    have hZch := packedZ_eval_var env input_var_z VA VB hVAnorm hVBnorm hz'
    have fbv : ∀ (X : Var (fields 32) (F p)) (w : fields 32 (F p)),
        Vector.map (Expression.eval env) X = w →
        Expression.eval env (fromBitsExpr X) = ((valueBits w : ℕ) : F p) :=
      fun X w h => Add32.fromBitsExpr_eval_normalized env X w h
    have ed := fbv _ _ h_d; have eh := fbv _ _ h_h; have es1t := fbv _ _ h_s1t
    have ek0 := fbv _ _ h_k0; have ew0 := fbv _ _ h_w0; have ec := fbv _ _ h_c
    have eg := fbv _ _ h_g; have es1tp := fbv _ _ h_s1tp; have ek1 := fbv _ _ h_k1
    have ew1 := fbv _ _ h_w1; have enet := fbv _ _ h_ne; have enetp := fbv _ _ h_nep
    obtain ⟨hcetp_eval, hcetp_le⟩ := carry_facts env (i₀ + 2) c_cetp_b
    rw [ed, eh, es1t, ek0, ew0, ec, eg, es1tp, ek1, ew1, enet, enetp, hZch, hcetp_eval] at c_fused
    obtain ⟨hv2, he2⟩ := carry2_facts env i₀ c_cet_b
    -- the derived low carry bit
    set E0 : F p := (2^32 : F p)⁻¹ *
        ((((valueBits input_d : ℕ) : F p) + ((valueBits input_h : ℕ) : F p) + ((valueBits input_sig1t : ℕ) : F p)
            + ((valueBits input_k0 : ℕ) : F p) + ((valueBits input_w0 : ℕ) : F p))
          + (((valueBits VA : ℕ) : F p) + (2^40 : F p) * ((valueBits VB : ℕ) : F p))
          + (2^40 : F p) * (((valueBits input_c : ℕ) : F p) + ((valueBits input_g : ℕ) : F p)
            + ((valueBits input_sig1tp : ℕ) : F p) + ((valueBits input_k1 : ℕ) : F p) + ((valueBits input_w1 : ℕ) : F p))
          - ((valueBits input_newE : ℕ) : F p)
          - (2^40 : F p) * (((valueBits input_newEp : ℕ) : F p)
            + (2^32 : F p) * (((env.get (i₀ + 2 + 0)).val + 2 * (env.get (i₀ + 2 + 1)).val
                + 4 * (env.get (i₀ + 2 + 2)).val : ℕ) : F p)))
      - 2 * env.get i₀ - 4 * env.get (i₀ + 1) with hE0
    have hE0b : IsBool E0 := isbool_of_ringnf (by rw [hE0]; linear_combination c_fused)
    have hE0cast := isBool_cast_val hE0b
    have hE0v := isBool_val_cases hE0b
    have hg0cast : env.get i₀ = ((ZMod.val (env.get i₀) : ℕ) : F p) := by
      simpa using he2 0 (by norm_num)
    have hg1cast : env.get (i₀ + 1) = ((ZMod.val (env.get (i₀ + 1)) : ℕ) : F p) :=
      he2 1 (by norm_num)
    have hg0v : ZMod.val (env.get i₀) = 0 ∨ ZMod.val (env.get i₀) = 1 := by
      simpa using hv2 0 (by norm_num)
    have hg1v := hv2 1 (by norm_num)
    have hcet_le : E0.val + 2 * ZMod.val (env.get i₀) + 4 * ZMod.val (env.get (i₀ + 1)) ≤ 7 := by
      rcases hE0v with h | h <;> rcases hg0v with h0 | h0 <;> rcases hg1v with h1 | h1 <;> omega
    have bnet : valueBits input_newE < 2^32 := valueBits_lt_two_pow _ hne_norm
    have bnetp : valueBits input_newEp < 2^32 := valueBits_lt_two_pow _ hnep_norm
    have bd : valueBits input_d < 2^32 := valueBits_lt_two_pow _ hd_norm
    have bh : valueBits input_h < 2^32 := valueBits_lt_two_pow _ hh_norm
    have bs1t : valueBits input_sig1t < 2^32 := valueBits_lt_two_pow _ hs1t_norm
    have bk0 : valueBits input_k0 < 2^32 := valueBits_lt_two_pow _ hk0_norm
    have bw0 : valueBits input_w0 < 2^32 := valueBits_lt_two_pow _ hw0_norm
    have bc : valueBits input_c < 2^32 := valueBits_lt_two_pow _ hc_norm
    have bg : valueBits input_g < 2^32 := valueBits_lt_two_pow _ hg_norm
    have bs1tp : valueBits input_sig1tp < 2^32 := valueBits_lt_two_pow _ hs1tp_norm
    have bk1 : valueBits input_k1 < 2^32 := valueBits_lt_two_pow _ hk1_norm
    have bw1 : valueBits input_w1 < 2^32 := valueBits_lt_two_pow _ hw1_norm
    have bVA : valueBits VA < 2^32 := valueBits_lt_two_pow _ hVAnorm
    have bVB : valueBits VB < 2^32 := valueBits_lt_two_pow _ hVBnorm
    have hXeq : (2^32 : F p) * (E0 + 2 * env.get i₀ + 4 * env.get (i₀ + 1))
        = (((valueBits input_d : ℕ) : F p) + ((valueBits input_h : ℕ) : F p) + ((valueBits input_sig1t : ℕ) : F p)
              + ((valueBits input_k0 : ℕ) : F p) + ((valueBits input_w0 : ℕ) : F p))
            + (((valueBits VA : ℕ) : F p) + (2^40 : F p) * ((valueBits VB : ℕ) : F p))
            + (2^40 : F p) * (((valueBits input_c : ℕ) : F p) + ((valueBits input_g : ℕ) : F p)
              + ((valueBits input_sig1tp : ℕ) : F p) + ((valueBits input_k1 : ℕ) : F p) + ((valueBits input_w1 : ℕ) : F p))
            - ((valueBits input_newE : ℕ) : F p)
            - (2^40 : F p) * (((valueBits input_newEp : ℕ) : F p)
              + (2^32 : F p) * ((ZMod.val (env.get (i₀ + 2 + 0)) + 2 * ZMod.val (env.get (i₀ + 2 + 1))
                  + 4 * ZMod.val (env.get (i₀ + 2 + 2)) : ℕ) : F p)) := by
      rw [hE0]
      have hX : ∀ x g0 g1 : F p,
          (2^32 : F p) * ((2^32 : F p)⁻¹ * x - 2 * g0 - 4 * g1 + 2 * g0 + 4 * g1) = x := by
        intro x g0 g1
        have hr : (2^32 : F p) * ((2^32 : F p)⁻¹ * x - 2 * g0 - 4 * g1 + 2 * g0 + 4 * g1)
            = (2^32 : F p) * ((2^32 : F p)⁻¹ * x) := by ring
        rw [hr, ← mul_assoc, w32_mul_inv, one_mul]
      exact hX _ _ _
    have hfe : ((valueBits input_d + valueBits input_h + valueBits input_sig1t + valueBits VA
          + valueBits input_k0 + valueBits input_w0 : ℕ) : F p)
        + 2^40 * ((valueBits input_c + valueBits input_g + valueBits input_sig1tp + valueBits VB
          + valueBits input_k1 + valueBits input_w1 : ℕ) : F p)
        = ((valueBits input_newE + 2^32 * (E0.val + 2 * ZMod.val (env.get i₀)
            + 4 * ZMod.val (env.get (i₀ + 1))) : ℕ) : F p)
          + 2^40 * ((valueBits input_newEp + 2^32 * (ZMod.val (env.get (i₀ + 2 + 0)) + 2 * ZMod.val (env.get (i₀ + 2 + 1))
            + 4 * ZMod.val (env.get (i₀ + 2 + 2))) : ℕ) : F p) := by
      rw [hE0cast, hg0cast, hg1cast] at hXeq
      push_cast
      push_cast at hXeq
      linear_combination -hXeq
    obtain ⟨hne_mod, hnetp_mod⟩ := fused_extract (by omega) (by omega) bnet bnetp hcet_le hcetp_le hfe
    refine ⟨?_, ?_⟩
    · rw [hne_mod, hVAval]
    · rw [hnetp_mod, hVBval]

theorem completeness : FormalAssertion.Completeness (F p) main Assumptions Spec := by
  circuit_proof_start [main, lowCarry, Assumptions, Spec]
  obtain ⟨hne_norm, hnep_norm, he_norm, hf_norm, hg_norm, hs1t_norm, hs1tp_norm, hd_norm, hh_norm,
    hk0_norm, hw0_norm, hc_norm, hk1_norm, hw1_norm, hzeq⟩ := h_assumptions
  obtain ⟨h_ne, h_nep, h_z, h_e, h_f, h_g, h_s1t, h_s1tp, h_d, h_h, h_k0, h_w0, h_c, h_k1, h_w1⟩ := h_input
  obtain ⟨hspec_e, hspec_ep⟩ := h_spec
  simp only [Nat.mul_zero, Nat.add_zero, Nat.zero_add] at h_env ⊢
  obtain ⟨h_ct, h_ctp, -⟩ := h_env
  set VA : fields 32 (F p) := Vector.ofFn fun j : Fin 32 => PackedChRow.chBit input_e[j.val] input_f[j.val] input_g[j.val] with hVA
  set VB : fields 32 (F p) := Vector.ofFn fun j : Fin 32 => PackedChRow.chBit input_newE[j.val] input_e[j.val] input_f[j.val] with hVB
  have hVAnorm : Normalized VA := by
    intro i; simp only [hVA, Fin.getElem_fin, Vector.getElem_ofFn]
    exact chBit_isBool (he_norm i) (hf_norm i) (hg_norm i)
  have hVBnorm : Normalized VB := by
    intro i; simp only [hVB, Fin.getElem_fin, Vector.getElem_ofFn]
    exact chBit_isBool (hne_norm i) (he_norm i) (hf_norm i)
  have hVAval : valueBits VA = Specs.SHA256.Ch (valueBits input_e) (valueBits input_f) (valueBits input_g) :=
    (Ch32.spec_of_constraint input_e input_f input_g VA he_norm hf_norm hg_norm
      (fun i => by simp only [hVA, Fin.getElem_fin, Vector.getElem_ofFn, PackedChRow.chBit])).1
  have hVBval : valueBits VB = Specs.SHA256.Ch (valueBits input_newE) (valueBits input_e) (valueBits input_f) :=
    (Ch32.spec_of_constraint input_newE input_e input_f VB hne_norm he_norm hf_norm
      (fun i => by simp only [hVB, Fin.getElem_fin, Vector.getElem_ofFn, PackedChRow.chBit])).1
  have evd := Add32.evalBitsNat_eq_valueBits env _ _ h_d
  have evh := Add32.evalBitsNat_eq_valueBits env _ _ h_h
  have evs1t := Add32.evalBitsNat_eq_valueBits env _ _ h_s1t
  have eve := Add32.evalBitsNat_eq_valueBits env _ _ h_e
  have evf := Add32.evalBitsNat_eq_valueBits env _ _ h_f
  have evg := Add32.evalBitsNat_eq_valueBits env _ _ h_g
  have evk0 := Add32.evalBitsNat_eq_valueBits env _ _ h_k0
  have evw0 := Add32.evalBitsNat_eq_valueBits env _ _ h_w0
  have evc := Add32.evalBitsNat_eq_valueBits env _ _ h_c
  have evne := Add32.evalBitsNat_eq_valueBits env _ _ h_ne
  have evs1tp := Add32.evalBitsNat_eq_valueBits env _ _ h_s1tp
  have evk1 := Add32.evalBitsNat_eq_valueBits env _ _ h_k1
  have evw1 := Add32.evalBitsNat_eq_valueBits env _ _ h_w1
  set Se : ℕ := valueBits input_d + valueBits input_h + valueBits input_sig1t + valueBits VA
    + valueBits input_k0 + valueBits input_w0 with hSe
  set Setp : ℕ := valueBits input_c + valueBits input_g + valueBits input_sig1tp + valueBits VB
    + valueBits input_k1 + valueBits input_w1 with hSetp
  have hgenE : evalBitsNat env input_var_d + evalBitsNat env input_var_h + evalBitsNat env input_var_sig1t
      + Specs.SHA256.Ch (evalBitsNat env input_var_e) (evalBitsNat env input_var_f) (evalBitsNat env input_var_g)
      + evalBitsNat env input_var_k0 + evalBitsNat env input_var_w0 = Se := by
    rw [evd, evh, evs1t, eve, evf, evg, evk0, evw0, hSe, hVAval]
  have hgenEp : evalBitsNat env input_var_c + evalBitsNat env input_var_g + evalBitsNat env input_var_sig1tp
      + Specs.SHA256.Ch (evalBitsNat env input_var_newE) (evalBitsNat env input_var_e) (evalBitsNat env input_var_f)
      + evalBitsNat env input_var_k1 + evalBitsNat env input_var_w1 = Setp := by
    rw [evc, evg, evs1tp, evne, eve, evf, evk1, evw1, hSetp, hVBval]
  have bd : valueBits input_d < 2^32 := valueBits_lt_two_pow _ hd_norm
  have bh : valueBits input_h < 2^32 := valueBits_lt_two_pow _ hh_norm
  have bs1t : valueBits input_sig1t < 2^32 := valueBits_lt_two_pow _ hs1t_norm
  have bk0 : valueBits input_k0 < 2^32 := valueBits_lt_two_pow _ hk0_norm
  have bw0 : valueBits input_w0 < 2^32 := valueBits_lt_two_pow _ hw0_norm
  have bVA : valueBits VA < 2^32 := valueBits_lt_two_pow _ hVAnorm
  have bc : valueBits input_c < 2^32 := valueBits_lt_two_pow _ hc_norm
  have bg : valueBits input_g < 2^32 := valueBits_lt_two_pow _ hg_norm
  have bs1tp : valueBits input_sig1tp < 2^32 := valueBits_lt_two_pow _ hs1tp_norm
  have bk1 : valueBits input_k1 < 2^32 := valueBits_lt_two_pow _ hk1_norm
  have bw1 : valueBits input_w1 < 2^32 := valueBits_lt_two_pow _ hw1_norm
  have bVB : valueBits VB < 2^32 := valueBits_lt_two_pow _ hVBnorm
  have e832 : (2:ℕ)^32 = 4294967296 := by norm_num
  have hSe8 : Se / 2^32 < 8 := by rw [hSe] at *; rw [e832] at bd bh bs1t bk0 bw0 bVA ⊢; omega
  have hSetp8 : Setp / 2^32 < 8 := by rw [hSetp] at *; rw [e832] at bc bg bs1tp bk1 bw1 bVB ⊢; omega
  have hct' : ∀ i : Fin 2, env.get (i₀ + i.val) = ((Se / 2^32 / 2^(i.val + 1) % 2 : ℕ) : F p) := by
    intro i; have h := h_ct i; rw [hgenE, witCarryHigh, Vector.getElem_ofFn] at h; exact h
  have hctp' : ∀ i : Fin 3, env.get (i₀ + 2 + i.val) = ((Setp / 2^32 / 2^i.val % 2 : ℕ) : F p) := by
    intro i; have h := h_ctp i; rw [hgenEp, witCarry, Vector.getElem_ofFn] at h; exact h
  refine ⟨fun i => ?_, fun i => ?_, ?_⟩
  · rw [hct' i]
    rcases Nat.mod_two_eq_zero_or_one (Se / 2^32 / 2^(i.val + 1)) with h0 | h0 <;> rw [h0] <;> push_cast <;> ring
  · rw [hctp' i]
    rcases Nat.mod_two_eq_zero_or_one (Setp / 2^32 / 2^i.val) with h0 | h0 <;> rw [h0] <;> push_cast <;> ring
  · -- the fused low-carry row
    have fbv : ∀ (X : Var (fields 32) (F p)) (w : fields 32 (F p)),
        Vector.map (Expression.eval env.toEnvironment) X = w →
        Expression.eval env.toEnvironment (fromBitsExpr X) = ((valueBits w : ℕ) : F p) :=
      fun X w h => Add32.fromBitsExpr_eval_normalized env.toEnvironment X w h
    have hz' : ∀ j : Fin 32,
        (Vector.map (Expression.eval env.toEnvironment) input_var_z)[j.val]'j.isLt = VA[j.val]'j.isLt + (2^40 : F p) * VB[j.val]'j.isLt := by
      intro j
      have hzj : (Vector.map (Expression.eval env.toEnvironment) input_var_z)[j.val]'j.isLt = input_z[j.val]'j.isLt := by rw [h_z]
      rw [hzj, hzeq j]; simp only [hVA, hVB, Vector.getElem_ofFn, Fin.getElem_fin]
    rw [fbv _ _ h_d, fbv _ _ h_h, fbv _ _ h_s1t, fbv _ _ h_k0, fbv _ _ h_w0, packedZ_eval_var env.toEnvironment input_var_z VA VB hVAnorm hVBnorm hz',
      fbv _ _ h_c, fbv _ _ h_g, fbv _ _ h_s1tp, fbv _ _ h_k1, fbv _ _ h_w1, fbv _ _ h_ne, fbv _ _ h_nep,
      carry_recompose env.toEnvironment (i₀ + 2) Setp hSetp8 hctp']
    have hg0 := hct' 0
    have hg1 := hct' 1
    simp only [Fin.val_zero, Fin.val_one, Nat.add_zero] at hg0 hg1
    rw [show env.get i₀ = ((Se / 2^32 / 2 % 2 : ℕ) : F p) by simpa using hg0,
      show env.get (i₀ + 1) = ((Se / 2^32 / 4 % 2 : ℕ) : F p) by
        have := hg1; norm_num at this ⊢; exact this]
    have hveq : valueBits input_newE = Se % 2^32 := by rw [hspec_e, hSe, hVAval]
    have hvepq : valueBits input_newEp = Setp % 2^32 := by rw [hspec_ep, hSetp, hVBval]
    have hSecast : ((Se : ℕ) : F p) = ((valueBits input_d : ℕ) : F p) + ((valueBits input_h : ℕ) : F p)
        + ((valueBits input_sig1t : ℕ) : F p) + ((valueBits VA : ℕ) : F p)
        + ((valueBits input_k0 : ℕ) : F p) + ((valueBits input_w0 : ℕ) : F p) := by
      rw [hSe]; push_cast; ring
    have hSetpcast : ((Setp : ℕ) : F p) = ((valueBits input_c : ℕ) : F p) + ((valueBits input_g : ℕ) : F p)
        + ((valueBits input_sig1tp : ℕ) : F p) + ((valueBits VB : ℕ) : F p)
        + ((valueBits input_k1 : ℕ) : F p) + ((valueBits input_w1 : ℕ) : F p) := by
      rw [hSetp]; push_cast; ring
    have h1 : ((valueBits input_newE : ℕ) : F p) + (2^32 : F p) * ((Se / 2^32 : ℕ) : F p) = ((Se : ℕ) : F p) := by
      have := congrArg (Nat.cast (R := F p)) (Nat.mod_add_div Se (2^32))
      rw [← hveq] at this
      push_cast at this
      linear_combination this
    have h2 : ((valueBits input_newEp : ℕ) : F p) + (2^32 : F p) * ((Setp / 2^32 : ℕ) : F p) = ((Setp : ℕ) : F p) := by
      have := congrArg (Nat.cast (R := F p)) (Nat.mod_add_div Setp (2^32))
      rw [← hvepq] at this
      push_cast at this
      linear_combination this
    have hqsplit : ((Se / 2^32 : ℕ) : F p) = ((Se / 2^32 % 2 : ℕ) : F p)
        + 2 * ((Se / 2^32 / 2 % 2 : ℕ) : F p) + 4 * ((Se / 2^32 / 4 % 2 : ℕ) : F p) := by
      have hnat : Se / 2^32 = Se / 2^32 % 2 + 2 * (Se / 2^32 / 2 % 2) + 4 * (Se / 2^32 / 4 % 2) := by
        omega
      have := congrArg (Nat.cast (R := F p)) hnat
      push_cast at this
      linear_combination this
    have hL : ((2 ^ 32 : F p)⁻¹ *
          (((valueBits input_d : ℕ) : F p) + ((valueBits input_h : ℕ) : F p) + ((valueBits input_sig1t : ℕ) : F p)
              + ((valueBits input_k0 : ℕ) : F p) + ((valueBits input_w0 : ℕ) : F p)
            + (((valueBits VA : ℕ) : F p) + 2 ^ 40 * ((valueBits VB : ℕ) : F p))
            + 2 ^ 40 * (((valueBits input_c : ℕ) : F p) + ((valueBits input_g : ℕ) : F p)
              + ((valueBits input_sig1tp : ℕ) : F p) + ((valueBits input_k1 : ℕ) : F p) + ((valueBits input_w1 : ℕ) : F p))
            + -((valueBits input_newE : ℕ) : F p)
            + -(2 ^ 40 * (((valueBits input_newEp : ℕ) : F p) + 2 ^ 32 * ((Setp / 2 ^ 32 : ℕ) : F p))))
          + -(2 * ((Se / 2 ^ 32 / 2 % 2 : ℕ) : F p)) + -(4 * ((Se / 2 ^ 32 / 4 % 2 : ℕ) : F p)))
        = ((Se / 2 ^ 32 % 2 : ℕ) : F p) := by
      have hbr : (((valueBits input_d : ℕ) : F p) + ((valueBits input_h : ℕ) : F p) + ((valueBits input_sig1t : ℕ) : F p)
              + ((valueBits input_k0 : ℕ) : F p) + ((valueBits input_w0 : ℕ) : F p)
            + (((valueBits VA : ℕ) : F p) + 2 ^ 40 * ((valueBits VB : ℕ) : F p))
            + 2 ^ 40 * (((valueBits input_c : ℕ) : F p) + ((valueBits input_g : ℕ) : F p)
              + ((valueBits input_sig1tp : ℕ) : F p) + ((valueBits input_k1 : ℕ) : F p) + ((valueBits input_w1 : ℕ) : F p))
            + -((valueBits input_newE : ℕ) : F p)
            + -(2 ^ 40 * (((valueBits input_newEp : ℕ) : F p) + 2 ^ 32 * ((Setp / 2 ^ 32 : ℕ) : F p))))
          = (2 ^ 32 : F p) * ((Se / 2 ^ 32 : ℕ) : F p) := by
        linear_combination (-1 : F p) * hSecast - h1 - (2 ^ 40 : F p) * hSetpcast - (2 ^ 40 : F p) * h2
      rw [hbr, ← mul_assoc, inv_mul_cancel₀ (w32_ne_zero (p := p)), one_mul]
      linear_combination hqsplit
    rw [hL]
    rcases Nat.mod_two_eq_zero_or_one (Se / 2 ^ 32) with h0 | h0 <;> rw [h0] <;> push_cast <;> ring

attribute [irreducible] main

def circuit : FormalAssertion (F p) Inputs where
  main; elaborated; Assumptions; Spec; soundness; completeness

end FusedEAdder

/-! # FusedAAdder -/
namespace FusedAAdder

open RPShared
local notation "λE" => (((2^40 : F p) : Expression (F p)))
local notation "w32E" => (((2^32 : F p) : Expression (F p)))

/-- The fused A-adder now derives each `new_a` lane from the already-materialized
`new_e` of its own round, mirroring the plain round's fold (`SHA256Round.lean`):
`new_a ≡ new_e + Σ₀ + Maj + ¬d + 1 (mod 2^32)`, where `¬d` is the free affine
complement of the round's `d`. Each lane is a 4-term sum (carry below 4), so only
two carry bits are witnessed per lane. Lane `t` uses `d = state[3]`; lane `t+1`
uses `d = state[2] = c`.

The two rounds' `Maj` columns are supplied packed into the single witnessed column
`z[j] = maj(a,b,c)[j] + 2^40·maj(newA,a,b)[j]` (`PackedMaj.circuit`), consumed at
weights `1` and `2^40` exactly like the packed `Ch` column of `FusedEAdder`. The
underlying registers `a = state[0]`, `b = state[1]`, `c = state[2]` are threaded so
the recomposition can pin `Maj` semantically; `c` doubles as lane `t+1`'s `¬d`. -/
structure Inputs (F : Type) where
  newA : fields 32 F
  newAp : fields 32 F
  newE : fields 32 F
  newEp : fields 32 F
  sig0t : fields 32 F
  sig0tp : fields 32 F
  z : fields 32 F
  a : fields 32 F
  b : fields 32 F
  c : fields 32 F
  d : fields 32 F
deriving ProvableStruct

/-- The affine derived low carry bit of the round-`t` sum (fused recomposition):
the recomposition solved for the weight-1 carry bit, minus the single witnessed
weight-2 high bit. The packed `Maj` column `z` enters standalone at weight 1 (it
already carries lane `t+1`'s `Maj` internally at weight `2^40`). -/
def lowCarry (inp : Var Inputs (F p)) (ca_t : Var (fields 1) (F p))
    (ca_tp : Var (fields 2) (F p)) : Expression (F p) :=
  (((2^32 : F p)⁻¹ : F p) : Expression (F p)) *
    ((fromBitsExpr inp.newE + fromBitsExpr inp.sig0t
        + fromBitsExpr (not32 inp.d) + (1 : Expression (F p)))
      + fromBitsExpr inp.z
      + λE * (fromBitsExpr inp.newEp + fromBitsExpr inp.sig0tp
        + fromBitsExpr (not32 inp.c) + (1 : Expression (F p)))
      - fromBitsExpr inp.newA
      - λE * (fromBitsExpr inp.newAp + w32E * RPShared.carryE2 ca_tp))
  - (2 : Expression (F p)) * ca_t[0]'(by norm_num)

def main (inp : Var Inputs (F p)) : Circuit (F p) Unit := do
  let ca_t ← witnessVector 1 fun env =>
    RPShared.witCarryHigh1 (evalBitsNat env inp.newE + evalBitsNat env inp.sig0t
      + Specs.SHA256.Maj (evalBitsNat env inp.a) (evalBitsNat env inp.b) (evalBitsNat env inp.c)
      + (2^32 - 1 - evalBitsNat env inp.d) + 1)
  Circuit.forEach (Vector.finRange 1) fun i => assertZero (ca_t[i] * (ca_t[i] - 1))
  let ca_tp ← witnessVector 2 fun env =>
    RPShared.witCarry2 (evalBitsNat env inp.newEp + evalBitsNat env inp.sig0tp
      + Specs.SHA256.Maj (evalBitsNat env inp.newA) (evalBitsNat env inp.a) (evalBitsNat env inp.b)
      + (2^32 - 1 - evalBitsNat env inp.c) + 1)
  Circuit.forEach (Vector.finRange 2) fun i => assertZero (ca_tp[i] * (ca_tp[i] - 1))
  assertZero (lowCarry inp ca_t ca_tp * (lowCarry inp ca_t ca_tp - 1))

def Assumptions (inp : Inputs (F p)) : Prop :=
  Normalized inp.newA ∧ Normalized inp.newAp ∧
  Normalized inp.newE ∧ Normalized inp.newEp ∧
  Normalized inp.sig0t ∧ Normalized inp.sig0tp ∧
  Normalized inp.a ∧ Normalized inp.b ∧ Normalized inp.c ∧ Normalized inp.d ∧
  (∀ j : Fin 32, inp.z[j] = PackedMajRow.majBit inp.a[j] inp.b[j] inp.c[j]
      + (2^40 : F p) * PackedMajRow.majBit inp.newA[j] inp.a[j] inp.b[j])

def Spec (inp : Inputs (F p)) : Prop :=
  valueBits inp.newA = (valueBits inp.newE + valueBits inp.sig0t
      + Specs.SHA256.Maj (valueBits inp.a) (valueBits inp.b) (valueBits inp.c)
      + (2^32 - 1 - valueBits inp.d) + 1) % 2^32
  ∧ valueBits inp.newAp = (valueBits inp.newEp + valueBits inp.sig0tp
      + Specs.SHA256.Maj (valueBits inp.newA) (valueBits inp.a) (valueBits inp.b)
      + (2^32 - 1 - valueBits inp.c) + 1) % 2^32

instance elaborated : ElaboratedCircuit (F p) Inputs unit main := by
  elaborate_circuit

variable [Fact (p > 2^76)]

theorem soundness : FormalAssertion.Soundness (F p) main Assumptions Spec := by
  circuit_proof_start [main, lowCarry, Assumptions, Spec]
  obtain ⟨hna_norm, hnap_norm, hne_norm, hnep_norm, hs0t_norm, hs0tp_norm,
    ha_norm, hb_norm, hc_norm, hd_norm, hzeq⟩ := h_assumptions
  obtain ⟨h_na, h_nap, h_ne, h_nep, h_s0t, h_s0tp, h_z, h_a, h_b, h_c, h_d⟩ := h_input
  obtain ⟨c_cat_b, c_catp_b, c_fused⟩ := h_holds
  set VA : fields 32 (F p) := Vector.ofFn fun j : Fin 32 => PackedMajRow.majBit input_a[j.val] input_b[j.val] input_c[j.val] with hVA
  set VB : fields 32 (F p) := Vector.ofFn fun j : Fin 32 => PackedMajRow.majBit input_newA[j.val] input_a[j.val] input_b[j.val] with hVB
  have hVAnorm : Normalized VA := by
    intro i; simp only [hVA, Fin.getElem_fin, Vector.getElem_ofFn]
    exact PackedMajRow.majBit_isBool (ha_norm i) (hb_norm i) (hc_norm i)
  have hVBnorm : Normalized VB := by
    intro i; simp only [hVB, Fin.getElem_fin, Vector.getElem_ofFn]
    exact PackedMajRow.majBit_isBool (hna_norm i) (ha_norm i) (hb_norm i)
  have hVAval : valueBits VA = Specs.SHA256.Maj (valueBits input_a) (valueBits input_b) (valueBits input_c) :=
    (Maj32.spec_of_constraint input_a input_b input_c VA ha_norm hb_norm hc_norm
      (fun i => by simp only [hVA, Fin.getElem_fin, Vector.getElem_ofFn, PackedMajRow.majBit])).1
  have hVBval : valueBits VB = Specs.SHA256.Maj (valueBits input_newA) (valueBits input_a) (valueBits input_b) :=
    (Maj32.spec_of_constraint input_newA input_a input_b VB hna_norm ha_norm hb_norm
      (fun i => by simp only [hVB, Fin.getElem_fin, Vector.getElem_ofFn, PackedMajRow.majBit])).1
  have hz' : ∀ j : Fin 32,
      (Vector.map (Expression.eval env) input_var_z)[j.val]'j.isLt = VA[j.val]'j.isLt + (2^40 : F p) * VB[j.val]'j.isLt := by
    intro j
    have hzj : (Vector.map (Expression.eval env) input_var_z)[j.val]'j.isLt = input_z[j.val]'j.isLt := by rw [h_z]
    rw [hzj, hzeq j]
    simp only [hVA, hVB, Vector.getElem_ofFn, Fin.getElem_fin]
  have hZmaj := packedZ_eval_var env input_var_z VA VB hVAnorm hVBnorm hz'
  have fbv : ∀ (X : Var (fields 32) (F p)) (w : fields 32 (F p)),
      Vector.map (Expression.eval env) X = w →
      Expression.eval env (fromBitsExpr X) = ((valueBits w : ℕ) : F p) :=
    fun X w h => Add32.fromBitsExpr_eval_normalized env X w h
  have ene := fbv _ _ h_ne; have es0t := fbv _ _ h_s0t
  have enep := fbv _ _ h_nep; have es0tp := fbv _ _ h_s0tp
  have ena := fbv _ _ h_na; have enap := fbv _ _ h_nap
  have hd_map_norm : Normalized (Vector.map (Expression.eval env) input_var_d) := by
    rw [h_d]; exact hd_norm
  have hc_map_norm : Normalized (Vector.map (Expression.eval env) input_var_c) := by
    rw [h_c]; exact hc_norm
  have endd : Expression.eval env (fromBitsExpr (not32 input_var_d))
      = ((2^32 - 1 - valueBits input_d : ℕ) : F p) := by
    rw [fbv _ _ (SHA256Round.not32_eval env input_var_d),
      SHA256Round.valueBits_not _ hd_map_norm, h_d]
  have encc : Expression.eval env (fromBitsExpr (not32 input_var_c))
      = ((2^32 - 1 - valueBits input_c : ℕ) : F p) := by
    rw [fbv _ _ (SHA256Round.not32_eval env input_var_c),
      SHA256Round.valueBits_not _ hc_map_norm, h_c]
  obtain ⟨hcatp_eval, hcatp_le⟩ := carry_facts2 env (i₀ + 1) c_catp_b
  rw [ene, es0t, endd, hZmaj, enep, es0tp, encc, ena, enap, hcatp_eval] at c_fused
  have hcatb : IsBool (env.get i₀) := isbool_of_ringnf (by linear_combination c_cat_b)
  -- the derived low carry bit
  set E0 : F p := (2^32 : F p)⁻¹ *
      ((((valueBits input_newE : ℕ) : F p) + ((valueBits input_sig0t : ℕ) : F p)
          + ((2^32 - 1 - valueBits input_d : ℕ) : F p) + 1)
        + (((valueBits VA : ℕ) : F p) + (2^40 : F p) * ((valueBits VB : ℕ) : F p))
        + (2^40 : F p) * (((valueBits input_newEp : ℕ) : F p) + ((valueBits input_sig0tp : ℕ) : F p)
          + ((2^32 - 1 - valueBits input_c : ℕ) : F p) + 1)
        - ((valueBits input_newA : ℕ) : F p)
        - (2^40 : F p) * (((valueBits input_newAp : ℕ) : F p)
          + (2^32 : F p) * (((env.get (i₀ + 1 + 0)).val + 2 * (env.get (i₀ + 1 + 1)).val : ℕ) : F p)))
    - 2 * env.get i₀ with hE0
  have hE0b : IsBool E0 := isbool_of_ringnf (by rw [hE0]; linear_combination c_fused)
  have hE0cast := isBool_cast_val hE0b
  have hE0v := isBool_val_cases hE0b
  have hg0cast : env.get i₀ = ((ZMod.val (env.get i₀) : ℕ) : F p) := isBool_cast_val hcatb
  have hg0v : ZMod.val (env.get i₀) = 0 ∨ ZMod.val (env.get i₀) = 1 := isBool_val_cases hcatb
  have hcat_le : E0.val + 2 * ZMod.val (env.get i₀) ≤ 7 := by
    rcases hE0v with h | h <;> rcases hg0v with h0 | h0 <;> omega
  have bna : valueBits input_newA < 2^32 := valueBits_lt_two_pow _ hna_norm
  have bnap : valueBits input_newAp < 2^32 := valueBits_lt_two_pow _ hnap_norm
  have bne : valueBits input_newE < 2^32 := valueBits_lt_two_pow _ hne_norm
  have bnep : valueBits input_newEp < 2^32 := valueBits_lt_two_pow _ hnep_norm
  have bs0t : valueBits input_sig0t < 2^32 := valueBits_lt_two_pow _ hs0t_norm
  have bs0tp : valueBits input_sig0tp < 2^32 := valueBits_lt_two_pow _ hs0tp_norm
  have bVA : valueBits VA < 2^32 := valueBits_lt_two_pow _ hVAnorm
  have bVB : valueBits VB < 2^32 := valueBits_lt_two_pow _ hVBnorm
  have bd : valueBits input_d < 2^32 := valueBits_lt_two_pow _ hd_norm
  have bc : valueBits input_c < 2^32 := valueBits_lt_two_pow _ hc_norm
  have h835 : (2:ℕ)^35 = 8 * 2^32 := by norm_num
  have hXeq : (2^32 : F p) * (E0 + 2 * env.get i₀)
      = (((valueBits input_newE : ℕ) : F p) + ((valueBits input_sig0t : ℕ) : F p)
          + ((2^32 - 1 - valueBits input_d : ℕ) : F p) + 1)
        + (((valueBits VA : ℕ) : F p) + (2^40 : F p) * ((valueBits VB : ℕ) : F p))
        + (2^40 : F p) * (((valueBits input_newEp : ℕ) : F p) + ((valueBits input_sig0tp : ℕ) : F p)
          + ((2^32 - 1 - valueBits input_c : ℕ) : F p) + 1)
        - ((valueBits input_newA : ℕ) : F p)
        - (2^40 : F p) * (((valueBits input_newAp : ℕ) : F p)
          + (2^32 : F p) * ((ZMod.val (env.get (i₀ + 1 + 0)) + 2 * ZMod.val (env.get (i₀ + 1 + 1)) : ℕ) : F p)) := by
    rw [hE0]
    have hX : ∀ x g0 : F p,
        (2^32 : F p) * ((2^32 : F p)⁻¹ * x - 2 * g0 + 2 * g0) = x := by
      intro x g0
      have hr : (2^32 : F p) * ((2^32 : F p)⁻¹ * x - 2 * g0 + 2 * g0)
          = (2^32 : F p) * ((2^32 : F p)⁻¹ * x) := by ring
      rw [hr, ← mul_assoc, w32_mul_inv, one_mul]
    exact hX _ _
  have hfa : ((valueBits input_newE + valueBits input_sig0t + valueBits VA
        + (2^32 - 1 - valueBits input_d) + 1 : ℕ) : F p)
      + 2^40 * ((valueBits input_newEp + valueBits input_sig0tp + valueBits VB
        + (2^32 - 1 - valueBits input_c) + 1 : ℕ) : F p)
      = ((valueBits input_newA + 2^32 * (E0.val + 2 * ZMod.val (env.get i₀)) : ℕ) : F p)
        + 2^40 * ((valueBits input_newAp + 2^32 * (ZMod.val (env.get (i₀ + 1 + 0))
          + 2 * ZMod.val (env.get (i₀ + 1 + 1))) : ℕ) : F p) := by
    rw [hE0cast, hg0cast] at hXeq
    push_cast
    push_cast at hXeq
    linear_combination -hXeq
  obtain ⟨hna_mod, hnap_mod⟩ := fused_extract (by omega) (by omega) bna bnap hcat_le (by omega) hfa
  refine ⟨?_, ?_⟩
  · rw [hna_mod, hVAval]
  · rw [hnap_mod, hVBval]

theorem completeness : FormalAssertion.Completeness (F p) main Assumptions Spec := by
  circuit_proof_start [main, lowCarry, Assumptions, Spec]
  obtain ⟨hna_norm, hnap_norm, hne_norm, hnep_norm, hs0t_norm, hs0tp_norm,
    ha_norm, hb_norm, hc_norm, hd_norm, hzeq⟩ := h_assumptions
  obtain ⟨h_na, h_nap, h_ne, h_nep, h_s0t, h_s0tp, h_z, h_a, h_b, h_c, h_d⟩ := h_input
  obtain ⟨hspec_a, hspec_ap⟩ := h_spec
  obtain ⟨h_ct, h_ctp⟩ := h_env
  set VA : fields 32 (F p) := Vector.ofFn fun j : Fin 32 => PackedMajRow.majBit input_a[j.val] input_b[j.val] input_c[j.val] with hVA
  set VB : fields 32 (F p) := Vector.ofFn fun j : Fin 32 => PackedMajRow.majBit input_newA[j.val] input_a[j.val] input_b[j.val] with hVB
  have hVAnorm : Normalized VA := by
    intro i; simp only [hVA, Fin.getElem_fin, Vector.getElem_ofFn]
    exact PackedMajRow.majBit_isBool (ha_norm i) (hb_norm i) (hc_norm i)
  have hVBnorm : Normalized VB := by
    intro i; simp only [hVB, Fin.getElem_fin, Vector.getElem_ofFn]
    exact PackedMajRow.majBit_isBool (hna_norm i) (ha_norm i) (hb_norm i)
  have hVAval : valueBits VA = Specs.SHA256.Maj (valueBits input_a) (valueBits input_b) (valueBits input_c) :=
    (Maj32.spec_of_constraint input_a input_b input_c VA ha_norm hb_norm hc_norm
      (fun i => by simp only [hVA, Fin.getElem_fin, Vector.getElem_ofFn, PackedMajRow.majBit])).1
  have hVBval : valueBits VB = Specs.SHA256.Maj (valueBits input_newA) (valueBits input_a) (valueBits input_b) :=
    (Maj32.spec_of_constraint input_newA input_a input_b VB hna_norm ha_norm hb_norm
      (fun i => by simp only [hVB, Fin.getElem_fin, Vector.getElem_ofFn, PackedMajRow.majBit])).1
  have evne := Add32.evalBitsNat_eq_valueBits env _ _ h_ne
  have evs0t := Add32.evalBitsNat_eq_valueBits env _ _ h_s0t
  have evna := Add32.evalBitsNat_eq_valueBits env _ _ h_na
  have eva := Add32.evalBitsNat_eq_valueBits env _ _ h_a
  have evb := Add32.evalBitsNat_eq_valueBits env _ _ h_b
  have evc := Add32.evalBitsNat_eq_valueBits env _ _ h_c
  have evd := Add32.evalBitsNat_eq_valueBits env _ _ h_d
  have evnep := Add32.evalBitsNat_eq_valueBits env _ _ h_nep
  have evs0tp := Add32.evalBitsNat_eq_valueBits env _ _ h_s0tp
  set Sa : ℕ := valueBits input_newE + valueBits input_sig0t + valueBits VA
    + (2^32 - 1 - valueBits input_d) + 1 with hSa
  set Sap : ℕ := valueBits input_newEp + valueBits input_sig0tp + valueBits VB
    + (2^32 - 1 - valueBits input_c) + 1 with hSap
  have hgenA : evalBitsNat env input_var_newE + evalBitsNat env input_var_sig0t
      + Specs.SHA256.Maj (evalBitsNat env input_var_a) (evalBitsNat env input_var_b) (evalBitsNat env input_var_c)
      + (2^32 - 1 - evalBitsNat env input_var_d) + 1 = Sa := by
    rw [evne, evs0t, eva, evb, evc, evd, hSa, hVAval]
  have hgenAp : evalBitsNat env input_var_newEp + evalBitsNat env input_var_sig0tp
      + Specs.SHA256.Maj (evalBitsNat env input_var_newA) (evalBitsNat env input_var_a) (evalBitsNat env input_var_b)
      + (2^32 - 1 - evalBitsNat env input_var_c) + 1 = Sap := by
    rw [evnep, evs0tp, evna, eva, evb, evc, hSap, hVBval]
  have bne : valueBits input_newE < 2^32 := valueBits_lt_two_pow _ hne_norm
  have bs0t : valueBits input_sig0t < 2^32 := valueBits_lt_two_pow _ hs0t_norm
  have bVA : valueBits VA < 2^32 := valueBits_lt_two_pow _ hVAnorm
  have bd : valueBits input_d < 2^32 := valueBits_lt_two_pow _ hd_norm
  have bnep : valueBits input_newEp < 2^32 := valueBits_lt_two_pow _ hnep_norm
  have bs0tp : valueBits input_sig0tp < 2^32 := valueBits_lt_two_pow _ hs0tp_norm
  have bVB : valueBits VB < 2^32 := valueBits_lt_two_pow _ hVBnorm
  have bc : valueBits input_c < 2^32 := valueBits_lt_two_pow _ hc_norm
  have e832 : (2:ℕ)^32 = 4294967296 := by norm_num
  have hSa8 : Sa / 2^32 < 4 := by rw [hSa] at *; rw [e832] at bne bs0t bVA bd ⊢; omega
  have hSap8 : Sap / 2^32 < 4 := by rw [hSap] at *; rw [e832] at bnep bs0tp bVB bc ⊢; omega
  have hg0 : env.get i₀ = ((Sa / 2^32 / 2 % 2 : ℕ) : F p) := by
    have h := h_ct 0; rw [hgenA, witCarryHigh1, Vector.getElem_ofFn] at h; simpa using h
  have hctp' : ∀ i : Fin 2, env.get (i₀ + 1 + i.val) = ((Sap / 2^32 / 2^i.val % 2 : ℕ) : F p) := by
    intro i; have h := h_ctp i; rw [hgenAp, witCarry2, Vector.getElem_ofFn] at h; exact h
  refine ⟨?_, fun i => ?_, ?_⟩
  · rw [hg0]
    rcases Nat.mod_two_eq_zero_or_one (Sa / 2^32 / 2) with h0 | h0 <;> rw [h0] <;> push_cast <;> ring
  · rw [hctp' i]
    rcases Nat.mod_two_eq_zero_or_one (Sap / 2^32 / 2^i.val) with h0 | h0 <;> rw [h0] <;> push_cast <;> ring
  · -- the fused low-carry row
    have fbv : ∀ (X : Var (fields 32) (F p)) (w : fields 32 (F p)),
        Vector.map (Expression.eval env.toEnvironment) X = w →
        Expression.eval env.toEnvironment (fromBitsExpr X) = ((valueBits w : ℕ) : F p) :=
      fun X w h => Add32.fromBitsExpr_eval_normalized env.toEnvironment X w h
    have hd_map_norm : Normalized (Vector.map (Expression.eval env.toEnvironment) input_var_d) := by
      rw [h_d]; exact hd_norm
    have hc_map_norm : Normalized (Vector.map (Expression.eval env.toEnvironment) input_var_c) := by
      rw [h_c]; exact hc_norm
    have hz' : ∀ j : Fin 32,
        (Vector.map (Expression.eval env.toEnvironment) input_var_z)[j.val]'j.isLt = VA[j.val]'j.isLt + (2^40 : F p) * VB[j.val]'j.isLt := by
      intro j
      have hzj : (Vector.map (Expression.eval env.toEnvironment) input_var_z)[j.val]'j.isLt = input_z[j.val]'j.isLt := by rw [h_z]
      rw [hzj, hzeq j]; simp only [hVA, hVB, Vector.getElem_ofFn, Fin.getElem_fin]
    rw [fbv _ _ h_ne, fbv _ _ h_s0t,
      fbv _ _ (SHA256Round.not32_eval env.toEnvironment input_var_d),
      packedZ_eval_var env.toEnvironment input_var_z VA VB hVAnorm hVBnorm hz',
      fbv _ _ h_nep, fbv _ _ h_s0tp,
      fbv _ _ (SHA256Round.not32_eval env.toEnvironment input_var_c),
      fbv _ _ h_na, fbv _ _ h_nap,
      carry_recompose2 env.toEnvironment (i₀ + 1) Sap hSap8 hctp',
      SHA256Round.valueBits_not _ hd_map_norm, SHA256Round.valueBits_not _ hc_map_norm, h_d, h_c, hg0]
    have hveq : valueBits input_newA = Sa % 2^32 := by rw [hSa, hVAval]; exact hspec_a
    have hvapq : valueBits input_newAp = Sap % 2^32 := by rw [hSap, hVBval]; exact hspec_ap
    have hSacast : ((Sa : ℕ) : F p) = ((valueBits input_newE : ℕ) : F p) + ((valueBits input_sig0t : ℕ) : F p)
        + ((valueBits VA : ℕ) : F p) + ((2^32 - 1 - valueBits input_d : ℕ) : F p) + 1 := by
      rw [hSa]; push_cast; ring
    have hSapcast : ((Sap : ℕ) : F p) = ((valueBits input_newEp : ℕ) : F p) + ((valueBits input_sig0tp : ℕ) : F p)
        + ((valueBits VB : ℕ) : F p) + ((2^32 - 1 - valueBits input_c : ℕ) : F p) + 1 := by
      rw [hSap]; push_cast; ring
    have h1 : ((valueBits input_newA : ℕ) : F p) + (2^32 : F p) * ((Sa / 2^32 : ℕ) : F p) = ((Sa : ℕ) : F p) := by
      have := congrArg (Nat.cast (R := F p)) (Nat.mod_add_div Sa (2^32))
      rw [← hveq] at this
      push_cast at this
      linear_combination this
    have h2 : ((valueBits input_newAp : ℕ) : F p) + (2^32 : F p) * ((Sap / 2^32 : ℕ) : F p) = ((Sap : ℕ) : F p) := by
      have := congrArg (Nat.cast (R := F p)) (Nat.mod_add_div Sap (2^32))
      rw [← hvapq] at this
      push_cast at this
      linear_combination this
    have hqsplit : ((Sa / 2^32 : ℕ) : F p) = ((Sa / 2^32 % 2 : ℕ) : F p)
        + 2 * ((Sa / 2^32 / 2 % 2 : ℕ) : F p) := by
      have hnat : Sa / 2^32 = Sa / 2^32 % 2 + 2 * (Sa / 2^32 / 2 % 2) := by
        omega
      have := congrArg (Nat.cast (R := F p)) hnat
      push_cast at this
      linear_combination this
    have hL : ((2 ^ 32 : F p)⁻¹ *
          (((valueBits input_newE : ℕ) : F p) + ((valueBits input_sig0t : ℕ) : F p)
              + ((2 ^ 32 - 1 - valueBits input_d : ℕ) : F p) + 1
            + (((valueBits VA : ℕ) : F p) + 2 ^ 40 * ((valueBits VB : ℕ) : F p))
            + 2 ^ 40 * (((valueBits input_newEp : ℕ) : F p) + ((valueBits input_sig0tp : ℕ) : F p)
              + ((2 ^ 32 - 1 - valueBits input_c : ℕ) : F p) + 1)
            + -((valueBits input_newA : ℕ) : F p)
            + -(2 ^ 40 * (((valueBits input_newAp : ℕ) : F p) + 2 ^ 32 * ((Sap / 2 ^ 32 : ℕ) : F p))))
          + -(2 * ((Sa / 2 ^ 32 / 2 % 2 : ℕ) : F p)))
        = ((Sa / 2 ^ 32 % 2 : ℕ) : F p) := by
      have hbr : (((valueBits input_newE : ℕ) : F p) + ((valueBits input_sig0t : ℕ) : F p)
              + ((2 ^ 32 - 1 - valueBits input_d : ℕ) : F p) + 1
            + (((valueBits VA : ℕ) : F p) + 2 ^ 40 * ((valueBits VB : ℕ) : F p))
            + 2 ^ 40 * (((valueBits input_newEp : ℕ) : F p) + ((valueBits input_sig0tp : ℕ) : F p)
              + ((2 ^ 32 - 1 - valueBits input_c : ℕ) : F p) + 1)
            + -((valueBits input_newA : ℕ) : F p)
            + -(2 ^ 40 * (((valueBits input_newAp : ℕ) : F p) + 2 ^ 32 * ((Sap / 2 ^ 32 : ℕ) : F p))))
          = (2 ^ 32 : F p) * ((Sa / 2 ^ 32 : ℕ) : F p) := by
        linear_combination (-1 : F p) * hSacast - h1 - (2 ^ 40 : F p) * hSapcast - (2 ^ 40 : F p) * h2
      rw [hbr, ← mul_assoc, inv_mul_cancel₀ (w32_ne_zero (p := p)), one_mul]
      linear_combination hqsplit
    rw [hL]
    rcases Nat.mod_two_eq_zero_or_one (Sa / 2 ^ 32) with h0 | h0 <;> rw [h0] <;> push_cast <;> ring

attribute [irreducible] main

def circuit : FormalAssertion (F p) Inputs where
  main; elaborated; Assumptions; Spec; soundness; completeness

end FusedAAdder

end Solution.SHA256
end
