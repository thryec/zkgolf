import Solution.SHA256.Add32Theorems
import Solution.SHA256.Theorems
import Challenge.Utils.CostR1CS

section
variable {p : ℕ} [Fact p.Prime] [h_large : Fact (p > 2^35)]

namespace Solution.SHA256

omit [Fact (Nat.Prime p)] [h_large : Fact (p > 2^35)] in
/-- Width-`m` bit recomposition: `Σⱼ (q / 2^j % 2) · 2^j = q % 2^m`. -/
lemma bit_decomp_mod (q m : ℕ) :
    ∑ j : Fin m, q / 2^j.val % 2 * 2^j.val = q % 2^m := by
  induction m with
  | zero => simp [Nat.mod_one]
  | succ m ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, Nat.mod_pow_succ]
    ring

omit [Fact (Nat.Prime p)] [h_large : Fact (p > 2^35)] in
/-- High-bit recomposition: `q % 2 + Σⱼ (q / 2^(j+1) % 2) · 2^(j+1) = q % 2^(m+1)`. -/
lemma bit_decomp_high (q m : ℕ) :
    q % 2 + ∑ j : Fin m, q / 2^(j.val+1) % 2 * 2^(j.val+1) = q % 2^(m+1) := by
  have hd := bit_decomp_mod q (m+1)
  rw [Fin.sum_univ_succ] at hd
  simpa using hd

namespace AddMany

open Challenge.CostR1CS

/-- Honest natural value of a vector of 32-bit words in a prover environment. -/
def evalManyNat {n : ℕ} (env : ProverEnvironment (F p))
    (xs : Vector (Var (fields 32) (F p)) n) : ℕ :=
  Finset.univ.sum fun k : Fin n => evalBitsNat env xs[k]

/-- Affine sum of all input words interpreted as little-endian 32-bit values. -/
def fromBitsExprSum {n : ℕ} (xs : Vector (Var (fields 32) (F p)) n) : Expression (F p) :=
  Fin.foldl n (fun acc k => acc + fromBitsExpr xs[k]) 0

/-- Fused n-operand 32-bit modular addition, for 2 ≤ n ≤ 8. -/
def addMany {n : ℕ} (_hn : 2 ≤ n ∧ n ≤ 8)
    (xs : Vector (Var (fields 32) (F p)) n) :
    Circuit (F p) (Var (fields 32) (F p)) := do
  let z ← witnessVector 32 fun env =>
    let s := evalManyNat env xs
    Vector.ofFn fun i : Fin 32 => ((s / 2^i.val % 2 : ℕ) : F p)
  let cv ← witnessVector 2 fun env =>
    let s := evalManyNat env xs
    Vector.ofFn fun j : Fin 2 => ((s / 2^(32 + j.val + 1) % 2 : ℕ) : F p)
  Circuit.forEach (Vector.finRange 32) fun i =>
    assertZero (z[i] * (z[i] - 1))
  Circuit.forEach (Vector.finRange 2) fun j =>
    assertZero (cv[j] * (cv[j] - 1))
  let lowCarry :=
    ((2^32 : F p)⁻¹ : F p) * (fromBitsExprSum xs - fromBitsExpr z) -
      (2 : F p) * cv[0] - (4 : F p) * cv[1]
  assertZero (lowCarry * (lowCarry - 1))
  return z

def Assumptions {n : ℕ} (xs : Vector (fields 32 (F p)) n) : Prop :=
  ∀ k : Fin n, Normalized xs[k]

def Spec {n : ℕ} (xs : Vector (fields 32 (F p)) n) (z : fields 32 (F p)) : Prop :=
  valueBits z = (Finset.univ.sum fun k : Fin n => valueBits xs[k]) % 2^32 ∧ Normalized z

abbrev Inputs (n : ℕ) := ProvableVector (fields 32) n

def main {n : ℕ} (hn : 2 ≤ n ∧ n ≤ 8)
    (input : Var (Inputs n) (F p)) : Circuit (F p) (Var (fields 32) (F p)) :=
  addMany hn input

instance elaborated {n : ℕ} (hn : 2 ≤ n ∧ n ≤ 8) :
    ElaboratedCircuit (F p) (Inputs n) (fields 32) (main (p := p) hn) := by
  elaborate_circuit

omit h_large in
/-- `Expression.eval` distributes over the additive `Fin.foldl` used by `fromBitsExprSum`. -/
lemma eval_finFoldl_add (env : Environment (F p)) (n : ℕ)
    (g : Fin n → Expression (F p)) :
    Expression.eval env (Fin.foldl n (fun acc i => acc + g i) (0 : Expression (F p))) =
      Finset.univ.sum fun i => Expression.eval env (g i) := by
  induction n with
  | zero =>
      simp [Fin.foldl_zero, Expression.eval]
  | succ m ih =>
      rw [Fin.foldl_succ_last, Fin.sum_univ_castSucc]
      simp only [Expression.eval]
      rw [show Fin.foldl m
            (fun (acc : Expression (F p)) (i : Fin m) => acc + g i.castSucc)
            (0 : Expression (F p)) =
          Fin.foldl m
            (fun (acc : Expression (F p)) (i : Fin m) => acc + (fun j => g j.castSucc) i)
            (0 : Expression (F p)) from rfl]
      rw [ih (fun j => g j.castSucc)]

omit h_large in
lemma eval_fromBitsExprSum {n : ℕ} (env : Environment (F p))
    (xsVar : Vector (Var (fields 32) (F p)) n)
    (xs : Vector (fields 32 (F p)) n)
    (hxs : ∀ k : Fin n, Vector.map (Expression.eval env) xsVar[k] = xs[k]) :
    Expression.eval env (fromBitsExprSum xsVar) =
      ((Finset.univ.sum fun k : Fin n => valueBits xs[k] : ℕ) : F p) := by
  unfold fromBitsExprSum
  rw [eval_finFoldl_add]
  rw [Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro k _
  exact Add32.fromBitsExpr_eval_normalized env xsVar[k] xs[k] (hxs k)

omit h_large in
lemma evalManyNat_eq_sum_valueBits {n : ℕ} (env : ProverEnvironment (F p))
    (xsVar : Vector (Var (fields 32) (F p)) n)
    (xs : Vector (fields 32 (F p)) n)
    (hxs : ∀ k : Fin n, Vector.map (Expression.eval env.toEnvironment) xsVar[k] = xs[k]) :
    evalManyNat env xsVar = Finset.univ.sum fun k : Fin n => valueBits xs[k] := by
  unfold evalManyNat
  apply Finset.sum_congr rfl
  intro k _
  exact Add32.evalBitsNat_eq_valueBits env xsVar[k] xs[k] (hxs k)

omit h_large in
lemma sum_valueBits_lt_pow35 {n : ℕ} (hn : n ≤ 8)
    (xs : Vector (fields 32 (F p)) n) (hxs : ∀ k : Fin n, Normalized xs[k]) :
    Finset.univ.sum (fun k : Fin n => valueBits xs[k]) < 2^35 := by
  have hsum_le :
      Finset.univ.sum (fun k : Fin n => valueBits xs[k]) ≤
        Finset.univ.sum (fun _k : Fin n => 2^32 - 1) := by
    apply Finset.sum_le_sum
    intro k _
    have hk := valueBits_lt_two_pow xs[k] (hxs k)
    omega
  rw [Finset.sum_const, Finset.card_fin] at hsum_le
  calc
    Finset.univ.sum (fun k : Fin n => valueBits xs[k])
        ≤ n * (2^32 - 1) := by simpa using hsum_le
    _ ≤ 8 * (2^32 - 1) := Nat.mul_le_mul_right _ hn
    _ < 2^35 := by norm_num

omit h_large in
lemma pow32_val (hp32 : (2:ℕ)^32 < p) : (2^32 : F p).val = 2^32 := by
  have hcast : ((2^32 : ℕ) : F p) = (2^32 : F p) := by push_cast; ring
  rw [← hcast, ZMod.val_natCast_of_lt hp32]

omit h_large in
lemma pow32_ne_zero (hp32 : (2:ℕ)^32 < p) : (2^32 : F p) ≠ 0 := by
  intro h
  have hv := congrArg ZMod.val h
  rw [pow32_val (p := p) hp32, ZMod.val_zero] at hv
  norm_num at hv

lemma carryBits_val {x y z : F p} (hx : IsBool x) (hy : IsBool y) (hz : IsBool z) :
    (x + (2 : F p) * y + (4 : F p) * z).val = x.val + 2 * y.val + 4 * z.val := by
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rcases hz with hz | hz <;>
    rw [hx, hy, hz] <;> norm_num [ZMod.val_zero, ZMod.val_one]
  all_goals
    apply ZMod.val_natCast_of_lt
    exact lt_trans (by norm_num) h_large.elim

set_option maxHeartbeats 1000000 in
theorem soundness {n : ℕ} (hn : 2 ≤ n ∧ n ≤ 8) :
    Soundness (F p) (main (p := p) hn) Assumptions Spec := by
  circuit_proof_start [main, addMany]
  obtain ⟨h_z_bool, h_cv_bool, h_low⟩ := h_holds
  have h_input_word (k : Fin n) :
      Vector.map (Expression.eval env) input_var[k] = input[k] := by
    have h := getElem_eval_vector env input_var k.val k.isLt
    rw [h_input] at h
    rw [← CircuitType.eval_var_fields env (input_var[k])]
    exact h
  have h_z_eval : Vector.map (Expression.eval env)
      (Vector.mapRange 32 fun i => (var {index := i₀ + i} : Expression (F p))) =
      Vector.ofFn fun i : Fin 32 => env.get (i₀ + i.val) := Add32.z_var_eval env i₀
  have h_z_norm : Normalized (Vector.ofFn fun i : Fin 32 => env.get (i₀ + i.val)) :=
    Add32.normalized_of_bool_holds env i₀ h_z_bool
  set sumV := Finset.univ.sum fun k : Fin n => valueBits input[k] with hsumV_def
  have hp32 : (2:ℕ)^32 < p := by
    have hp := h_large.elim
    norm_num at hp ⊢
    omega
  have h_sum_lt_p : sumV < p := by
    rw [hsumV_def]
    have hlt := sum_valueBits_lt_pow35 (p := p) hn.2 input h_assumptions
    exact lt_trans hlt h_large.elim
  set fsum := Expression.eval env (fromBitsExprSum input_var) with hfsum_def
  set fz := Expression.eval env (fromBitsExpr
    (Vector.mapRange 32 fun i => (var {index := i₀ + i} : Expression (F p)))) with hfz_def
  have h_fsum_val : fsum.val = sumV := by
    rw [hfsum_def, hsumV_def, eval_fromBitsExprSum env input_var input h_input_word]
    exact ZMod.val_natCast_of_lt h_sum_lt_p
  set zVec := Vector.ofFn fun i : Fin 32 => env.get (i₀ + i.val) with hzVec_def
  set vz := valueBits zVec with hvz_def
  have h_fz : fz.val = vz := by
    rw [hfz_def]
    exact Add32.fromBitsExpr_val_eq env _ zVec h_z_eval h_z_norm hp32
  set c0 := env.get (i₀ + 32) with hc0_def
  set c1 := env.get (i₀ + 32 + 1) with hc1_def
  have h_c0_bool : IsBool c0 := by
    apply Add32.isbool_of_bool_constraint
    simpa [c0] using h_cv_bool 0
  have h_c1_bool : IsBool c1 := by
    apply Add32.isbool_of_bool_constraint
    simpa [c1] using h_cv_bool 1
  set lowF := ((2^32 : F p)⁻¹ : F p) * (fsum - fz) - (2 : F p) * c0 -
    (4 : F p) * c1 with hlowF_def
  have h_low_bool : IsBool lowF := by
    apply Add32.isbool_of_bool_constraint
    simpa [lowF, fsum, fz, c0, c1, sub_eq_add_neg] using h_low
  set carryF := lowF + (2 : F p) * c0 + (4 : F p) * c1 with hcarryF_def
  have h_lin' : fsum = fz + (2^32 : F p) * carryF := by
    have hpow_ne := pow32_ne_zero (p := p) hp32
    rw [hcarryF_def, hlowF_def]
    have hmul : (2^32 : F p) * ((2^32 : F p)⁻¹ * (fsum - fz)) = fsum - fz := by
      rw [← mul_assoc, mul_inv_cancel₀ hpow_ne, one_mul]
    calc
      fsum = fz + (fsum - fz) := by ring
      _ = fz + (2^32 : F p) * ((2^32 : F p)⁻¹ * (fsum - fz)) := by rw [hmul]
      _ = fz + (2^32 : F p) *
          (((2^32 : F p)⁻¹ * (fsum - fz) - 2 * c0 - 4 * c1) + 2 * c0 + 4 * c1) := by
        ring
  set carryVal := lowF.val + 2 * c0.val + 4 * c1.val with hcarryVal_def
  have h_low_le : lowF.val ≤ 1 := by
    rcases IsBool.val_of_IsBool h_low_bool with h | h <;> omega
  have h_c0_le : c0.val ≤ 1 := by
    rcases IsBool.val_of_IsBool h_c0_bool with h | h <;> omega
  have h_c1_le : c1.val ≤ 1 := by
    rcases IsBool.val_of_IsBool h_c1_bool with h | h <;> omega
  have h_carry_le : carryVal ≤ 7 := by
    rw [hcarryVal_def]
    omega
  have h_carry_val : carryF.val = carryVal := by
    rw [hcarryF_def, hcarryVal_def]
    exact carryBits_val h_low_bool h_c0_bool h_c1_bool
  have hvz_lt : vz < 2^32 := by
    rw [hvz_def]
    exact valueBits_lt_two_pow zVec h_z_norm
  have h_total_lt : vz + 2^32 * carryVal < p := by
    have hvz_le : vz ≤ 2^32 - 1 := by omega
    have hle : vz + 2^32 * carryVal ≤ (2^32 - 1) + 2^32 * 7 := by
      exact Nat.add_le_add hvz_le (Nat.mul_le_mul_left _ h_carry_le)
    exact lt_trans (Nat.lt_of_le_of_lt hle (by norm_num)) h_large.elim
  have h_mul_lt : 2^32 * carryVal < p := by
    exact Nat.lt_of_le_of_lt (Nat.le_add_left _ _) h_total_lt
  have h_mul_val : ((2^32 : F p) * carryF).val = 2^32 * carryVal := by
    rw [ZMod.val_mul, pow32_val (p := p) hp32, h_carry_val]
    rw [Nat.mod_eq_of_lt h_mul_lt]
  have h_rhs_val : (fz + (2^32 : F p) * carryF).val = vz + 2^32 * carryVal := by
    rw [ZMod.val_add, h_fz, h_mul_val]
    rw [Nat.mod_eq_of_lt h_total_lt]
  have h_nat_eq := congrArg ZMod.val h_lin'
  rw [h_fsum_val, h_rhs_val] at h_nat_eq
  refine ⟨?_, ?_⟩
  · rw [h_z_eval, ← hvz_def]
    change vz = sumV % 2^32
    calc
      vz = (vz + 2^32 * carryVal) % 2^32 := by
        rw [show 2^32 * carryVal = carryVal * 2^32 by ring,
          Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hvz_lt]
      _ = sumV % 2^32 := congrArg (fun t : ℕ => t % 2^32) h_nat_eq.symm
  · rw [h_z_eval]
    exact h_z_norm

set_option maxHeartbeats 1000000 in
theorem completeness {n : ℕ} (hn : 2 ≤ n ∧ n ≤ 8) :
    Completeness (F p) (main (p := p) hn) Assumptions := by
  circuit_proof_start [main, addMany]
  obtain ⟨h_env_z, h_env_cv, _h_env_tail⟩ := h_env
  set S := evalManyNat env input_var with hS_def
  have h_input_word (k : Fin n) :
      Vector.map (Expression.eval env.toEnvironment) input_var[k] = input[k] := by
    have h := getElem_eval_vector env.toEnvironment input_var k.val k.isLt
    rw [h_input] at h
    rw [← CircuitType.eval_var_fields env.toEnvironment (input_var[k])]
    exact h
  have hS_eq : S = Finset.univ.sum fun k : Fin n => valueBits input[k] := by
    rw [hS_def]
    exact evalManyNat_eq_sum_valueBits env input_var input h_input_word
  have hS_lt35 : S < 2^35 := by
    rw [hS_eq]
    exact sum_valueBits_lt_pow35 (p := p) hn.2 input h_assumptions
  have hp32 : (2:ℕ)^32 < p := by
    exact lt_trans (by norm_num) h_large.elim
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have henv_i := h_env_z i
    simp only [Vector.getElem_ofFn] at henv_i
    rw [henv_i]
    rcases Nat.mod_two_eq_zero_or_one (S / 2^i.val) with h | h <;>
      rw [h] <;> push_cast <;> ring
  · intro j
    have henv_j := h_env_cv j
    simp only [Vector.getElem_ofFn] at henv_j
    rw [henv_j]
    rcases Nat.mod_two_eq_zero_or_one (S / 2^(32 + j.val + 1)) with h | h <;>
      rw [h] <;> push_cast <;> ring
  · set q := S / 2^32 with hq_def
    have hS_mod_lt : S % 2^32 < 2^32 := Nat.mod_lt _ (by norm_num)
    have h_z_eval := Add32.z_var_eval env.toEnvironment i₀
    have h_z_eval' : Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 32 fun i => (var {index := i₀ + i} : Expression (F p))) =
        Vector.ofFn fun i : Fin 32 => ((S % 2^32 / 2^i.val % 2 : ℕ) : F p) := by
      rw [h_z_eval]
      ext i hi
      simp only [Vector.getElem_ofFn]
      have this := h_env_z ⟨i, hi⟩
      simp only [Vector.getElem_ofFn] at this
      rw [this]
      congr 1
      rw [← Add32.testBit_ite_eq S i, ← Add32.testBit_ite_eq (S % 2^32) i]
      rw [Nat.testBit_mod_two_pow]
      simp [hi]
    have h_FZ : Expression.eval env.toEnvironment (fromBitsExpr
        (Vector.mapRange 32 fun i => (var {index := i₀ + i} : Expression (F p)))) =
        ((S % 2^32 : ℕ) : F p) := by
      show Expression.eval env.toEnvironment (Utils.Bits.fieldFromBitsExpr _) = _
      simp only [Utils.Bits.fieldFromBits_eval]
      rw [h_z_eval']
      exact Add32.fieldFromBits_bit_decomp (p := p) (S % 2^32) hS_mod_lt hp32
    have h_FS : Expression.eval env.toEnvironment (fromBitsExprSum input_var) =
        ((S : ℕ) : F p) := by
      rw [eval_fromBitsExprSum env.toEnvironment input_var input h_input_word, ← hS_eq]
    have hcv0 : env.get (i₀ + 32) = ((q / 2 % 2 : ℕ) : F p) := by
      have h := h_env_cv 0
      simp only [Vector.getElem_ofFn] at h
      norm_num at h
      rw [h]
      congr 1
      rw [hq_def]
      change S / (2^32 * 2) % 2 = S / 2^32 / 2 % 2
      rw [Nat.div_div_eq_div_mul]
    have hcv1 : env.get (i₀ + 32 + 1) = ((q / 4 % 2 : ℕ) : F p) := by
      have h := h_env_cv 1
      simp only [Vector.getElem_ofFn] at h
      norm_num at h
      rw [h]
      congr 1
      rw [hq_def]
      change S / (2^32 * 4) % 2 = S / 2^32 / 4 % 2
      rw [Nat.div_div_eq_div_mul]
    have hpow_ne := pow32_ne_zero (p := p) hp32
    have h_sub : ((S : ℕ) : F p) - ((S % 2^32 : ℕ) : F p) =
        (2^32 : F p) * ((q : ℕ) : F p) := by
      have hdec : S = S % 2^32 + 2^32 * q := by
        rw [hq_def]
        exact (Nat.mod_add_div S (2^32)).symm
      have hcast := congrArg (Nat.cast : ℕ → F p) hdec
      rw [Nat.cast_add, Nat.cast_mul] at hcast
      rw [hcast]
      ring
    have h_inv : ((2^32 : F p)⁻¹ : F p) *
        (((S : ℕ) : F p) - ((S % 2^32 : ℕ) : F p)) = ((q : ℕ) : F p) := by
      rw [h_sub]
      rw [← mul_assoc, inv_mul_cancel₀ hpow_ne, one_mul]
    have h_inv' : ((2^32 : F p)⁻¹ : F p) *
        (((S : ℕ) : F p) + -((S % 2^32 : ℕ) : F p)) = ((q : ℕ) : F p) := by
      simpa [sub_eq_add_neg] using h_inv
    have hq_lt8 : q < 8 := by
      rw [hq_def]
      have hmul : S < 8 * 2^32 := by
        have hpow : 8 * 2^32 = 2^35 := by norm_num
        rwa [hpow]
      have hdiv := (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2^32)).mpr hmul
      simpa [Nat.mul_comm] using hdiv
    have hq_decomp : q = q % 2 + 2 * (q / 2 % 2) + 4 * (q / 4 % 2) := by
      omega
    have hlow_nat : ((q : ℕ) : F p) - (2 : F p) * ((q / 2 % 2 : ℕ) : F p) -
        (4 : F p) * ((q / 4 % 2 : ℕ) : F p) = ((q % 2 : ℕ) : F p) := by
      have hcast := congrArg (Nat.cast : ℕ → F p) hq_decomp
      rw [Nat.cast_add, Nat.cast_add, Nat.cast_mul, Nat.cast_mul] at hcast
      rw [hcast]
      ring
    have hlow_nat' : ((q : ℕ) : F p) +
        -((2 : F p) * ((q / 2 % 2 : ℕ) : F p)) +
        -((4 : F p) * ((q / 4 % 2 : ℕ) : F p)) = ((q % 2 : ℕ) : F p) := by
      simpa [sub_eq_add_neg] using hlow_nat
    rw [h_FS, h_FZ, hcv0, hcv1]
    rw [h_inv', hlow_nat']
    rcases Nat.mod_two_eq_zero_or_one q with h | h <;>
      rw [h] <;> push_cast <;> ring

omit h_large in
theorem costIs_addMany {n : ℕ} (hn : 2 ≤ n ∧ n ≤ 8)
    (xs : Vector (Var (fields 32) (F p)) n) :
    CostIs (addMany hn xs) ⟨34, 35⟩ :=
  CostIs.bind (CostIs.witnessVector 32 _) fun z =>
    CostIs.bind (CostIs.witnessVector 2 _) fun _ =>
      CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ =>
        CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ =>
          CostIs.bind (CostIs.assertZero _) fun _ => CostIs.pure z

attribute [local irreducible] isR1CSRow r1csProducts operationsIsR1CS flatOperationsIsR1CS

omit h_large in
theorem affine_fieldFromBitsExpr {m : ℕ} (v : Var (fields m) (F p)) (h : AffineW v) :
    Affine (Utils.Bits.fieldFromBitsExpr v) := by
  unfold Utils.Bits.fieldFromBitsExpr
  apply affine_finFoldl'
  · exact Affine.zero
  · intro acc i hacc
    exact Affine.add hacc (Affine.mul_fconst _ (h i.val i.isLt))

omit h_large in
theorem affine_fromBitsExprSum {n : ℕ} (xs : Vector (Var (fields 32) (F p)) n)
    (hxs : ∀ k : Fin n, AffineW xs[k]) :
    Affine (fromBitsExprSum xs) := by
  unfold fromBitsExprSum
  apply affine_finFoldl'
  · exact Affine.zero
  · intro acc i hacc
    exact Affine.add hacc (affine_fieldFromBitsExpr xs[i] (hxs i))

omit h_large in
theorem r1cs_addMany {n : ℕ} (hn : 2 ≤ n ∧ n ≤ 8)
    (xs : Vector (Var (fields 32) (F p)) n)
    (hxs : ∀ k : Fin n, AffineW xs[k]) :
    IsR1CSCirc (addMany hn xs) :=
  IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector 32 _) fun zOff =>
  IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector 2 _) fun cvOff =>
  IsR1CSCirc.bind
    (IsR1CSCirc.forEach fun j m =>
      IsR1CSCirc.assertZero
        (isR1CSRow_mul (affineW_witnessVector_output 32 _ zOff j.val j.isLt)
          (Affine.sub (affineW_witnessVector_output 32 _ zOff j.val j.isLt)
            (Affine.const 1))) m)
    fun _ =>
  IsR1CSCirc.bind
    (IsR1CSCirc.forEach fun j m =>
      IsR1CSCirc.assertZero
        (isR1CSRow_mul (affineW_witnessVector_output 2 _ cvOff j.val j.isLt)
          (Affine.sub (affineW_witnessVector_output 2 _ cvOff j.val j.isLt)
            (Affine.const 1))) m)
    fun _ =>
  IsR1CSCirc.bind
    (IsR1CSCirc.assertZero
      (isR1CSRow_mul
        (Affine.sub
          (Affine.sub
            (Affine.fconst_mul _
              (Affine.sub (affine_fromBitsExprSum xs hxs)
                (affine_fieldFromBitsExpr _
                  (affineW_witnessVector_output 32 _ zOff))))
            (Affine.fconst_mul _ (affineW_witnessVector_output 2 _ cvOff 0 (by norm_num))))
          (Affine.fconst_mul _ (affineW_witnessVector_output 2 _ cvOff 1 (by norm_num))))
        (Affine.sub
          (Affine.sub
            (Affine.sub
              (Affine.fconst_mul _
                (Affine.sub (affine_fromBitsExprSum xs hxs)
                  (affine_fieldFromBitsExpr _
                    (affineW_witnessVector_output 32 _ zOff))))
              (Affine.fconst_mul _ (affineW_witnessVector_output 2 _ cvOff 0 (by norm_num))))
            (Affine.fconst_mul _ (affineW_witnessVector_output 2 _ cvOff 1 (by norm_num))))
          (Affine.const 1))))
    fun _ => IsR1CSCirc.pure _

def circuit {n : ℕ} (hn : 2 ≤ n ∧ n ≤ 8) :
    FormalCircuit (F p) (Inputs n) (fields 32) where
  main := main hn
  elaborated := elaborated hn
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness hn
  completeness := completeness hn

/-! ## `+1` variant: fused adder over `n ≤ 4` words **plus the constant 1**

Computes `new_a` from the already-decomposed `new_e` via the two's complement of
`d`: since `new_e ≡ d + t1 (mod 2^32)`, `new_a = t1 + t2 ≡ new_e + Σ₀ + Maj + ¬d + 1`
where `¬d = 2^32 − 1 − d` is the affine bit-complement. `n ≤ 4` keeps the carry to
2 bits, so a single witnessed high carry (weight 2) plus the fused low-carry row
suffice: cost `⟨33, 34⟩` vs the 7-word adder's `⟨34, 35⟩`. -/

/-- Fused (n ≤ 4)-operand 32-bit modular addition plus the constant 1. -/
def addMany2c {n : ℕ} (_hn : n ≤ 4)
    (xs : Vector (Var (fields 32) (F p)) n) :
    Circuit (F p) (Var (fields 32) (F p)) := do
  let z ← witnessVector 32 fun env =>
    let s := evalManyNat env xs + 1
    Vector.ofFn fun i : Fin 32 => ((s / 2^i.val % 2 : ℕ) : F p)
  let c1 ← witnessField fun env =>
    let s := evalManyNat env xs + 1
    ((s / 2^33 % 2 : ℕ) : F p)
  Circuit.forEach (Vector.finRange 32) fun i =>
    assertZero (z[i] * (z[i] - 1))
  assertZero (c1 * (c1 - 1))
  let lowCarry :=
    ((2^32 : F p)⁻¹ : F p) * (fromBitsExprSum xs + 1 - fromBitsExpr z) -
      (2 : F p) * c1
  assertZero (lowCarry * (lowCarry - 1))
  return z

def Spec2c {n : ℕ} (xs : Vector (fields 32 (F p)) n) (z : fields 32 (F p)) : Prop :=
  valueBits z = ((Finset.univ.sum fun k : Fin n => valueBits xs[k]) + 1) % 2^32 ∧ Normalized z

def main2c {n : ℕ} (hn : n ≤ 4)
    (input : Var (Inputs n) (F p)) : Circuit (F p) (Var (fields 32) (F p)) :=
  addMany2c hn input

instance elaborated2c {n : ℕ} (hn : n ≤ 4) :
    ElaboratedCircuit (F p) (Inputs n) (fields 32) (main2c (p := p) hn) := by
  elaborate_circuit

omit h_large in
lemma sum_valueBits_succ_lt_pow34 {n : ℕ} (hn : n ≤ 4)
    (xs : Vector (fields 32 (F p)) n) (hxs : ∀ k : Fin n, Normalized xs[k]) :
    (Finset.univ.sum (fun k : Fin n => valueBits xs[k])) + 1 < 2^34 := by
  have hsum_le :
      Finset.univ.sum (fun k : Fin n => valueBits xs[k]) ≤
        Finset.univ.sum (fun _k : Fin n => 2^32 - 1) := by
    apply Finset.sum_le_sum
    intro k _
    have hk := valueBits_lt_two_pow xs[k] (hxs k)
    omega
  rw [Finset.sum_const, Finset.card_fin] at hsum_le
  have hle : Finset.univ.sum (fun k : Fin n => valueBits xs[k]) ≤ n * (2^32 - 1) := by
    simpa using hsum_le
  have h2 : n * (2^32 - 1) ≤ 4 * (2^32 - 1) := Nat.mul_le_mul_right _ hn
  omega

/-- Booleans `x`, `y` recombine to the ℕ value `x + 2·y` in the field. -/
lemma carryBits2_val {x y : F p} (hx : IsBool x) (hy : IsBool y) :
    (x + (2 : F p) * y).val = x.val + 2 * y.val := by
  rcases hx with hx | hx <;> rcases hy with hy | hy <;>
    rw [hx, hy] <;> norm_num [ZMod.val_zero, ZMod.val_one]
  all_goals
    apply ZMod.val_natCast_of_lt
    exact lt_trans (by norm_num) h_large.elim

set_option maxHeartbeats 1000000 in
theorem soundness2c {n : ℕ} (hn : n ≤ 4) :
    Soundness (F p) (main2c (p := p) hn) Assumptions Spec2c := by
  circuit_proof_start [main2c, addMany2c]
  obtain ⟨h_z_bool, h_c1_bool, h_low⟩ := h_holds
  have h_input_word (k : Fin n) :
      Vector.map (Expression.eval env) input_var[k] = input[k] := by
    have h := getElem_eval_vector env input_var k.val k.isLt
    rw [h_input] at h
    rw [← CircuitType.eval_var_fields env (input_var[k])]
    exact h
  have h_z_eval : Vector.map (Expression.eval env)
      (Vector.mapRange 32 fun i => (var {index := i₀ + i} : Expression (F p))) =
      Vector.ofFn fun i : Fin 32 => env.get (i₀ + i.val) := Add32.z_var_eval env i₀
  have h_z_norm : Normalized (Vector.ofFn fun i : Fin 32 => env.get (i₀ + i.val)) :=
    Add32.normalized_of_bool_holds env i₀ h_z_bool
  set sumV := Finset.univ.sum fun k : Fin n => valueBits input[k] with hsumV_def
  have hp32 : (2:ℕ)^32 < p := by
    have hp := h_large.elim
    norm_num at hp ⊢
    omega
  have h_sum1_lt : sumV + 1 < 2^34 := by
    rw [hsumV_def]; exact sum_valueBits_succ_lt_pow34 hn input h_assumptions
  have h_sum1_lt_p : sumV + 1 < p :=
    lt_trans (lt_trans h_sum1_lt (by norm_num)) h_large.elim
  set fsum := Expression.eval env (fromBitsExprSum input_var) with hfsum_def
  set fz := Expression.eval env (fromBitsExpr
    (Vector.mapRange 32 fun i => (var {index := i₀ + i} : Expression (F p)))) with hfz_def
  have h_fsum_cast : fsum = ((sumV : ℕ) : F p) := by
    rw [hfsum_def, hsumV_def, eval_fromBitsExprSum env input_var input h_input_word]
  set zVec := Vector.ofFn fun i : Fin 32 => env.get (i₀ + i.val) with hzVec_def
  set vz := valueBits zVec with hvz_def
  have h_fz : fz.val = vz := by
    rw [hfz_def]
    exact Add32.fromBitsExpr_val_eq env _ zVec h_z_eval h_z_norm hp32
  set cc := env.get (i₀ + 32) with hcc_def
  have h_cc_bool : IsBool cc := by
    apply Add32.isbool_of_bool_constraint
    simpa [cc] using h_c1_bool
  set lowF := ((2^32 : F p)⁻¹ : F p) * (fsum + 1 - fz) - (2 : F p) * cc with hlowF_def
  have h_low_bool : IsBool lowF := by
    apply Add32.isbool_of_bool_constraint
    simpa [lowF, fsum, fz, cc, sub_eq_add_neg] using h_low
  set carryF := lowF + (2 : F p) * cc with hcarryF_def
  have h_lin' : fsum + 1 = fz + (2^32 : F p) * carryF := by
    have hpow_ne := pow32_ne_zero (p := p) hp32
    rw [hcarryF_def, hlowF_def]
    have hmul : (2^32 : F p) * ((2^32 : F p)⁻¹ * (fsum + 1 - fz)) = fsum + 1 - fz := by
      rw [← mul_assoc, mul_inv_cancel₀ hpow_ne, one_mul]
    calc
      fsum + 1 = fz + (fsum + 1 - fz) := by ring
      _ = fz + (2^32 : F p) * ((2^32 : F p)⁻¹ * (fsum + 1 - fz)) := by rw [hmul]
      _ = fz + (2^32 : F p) *
          (((2^32 : F p)⁻¹ * (fsum + 1 - fz) - 2 * cc) + 2 * cc) := by ring
  set carryVal := lowF.val + 2 * cc.val with hcarryVal_def
  have h_low_le : lowF.val ≤ 1 := by
    rcases IsBool.val_of_IsBool h_low_bool with h | h <;> omega
  have h_cc_le : cc.val ≤ 1 := by
    rcases IsBool.val_of_IsBool h_cc_bool with h | h <;> omega
  have h_carry_le : carryVal ≤ 3 := by rw [hcarryVal_def]; omega
  have h_carry_val : carryF.val = carryVal := by
    rw [hcarryF_def, hcarryVal_def]
    exact carryBits2_val h_low_bool h_cc_bool
  have hvz_lt : vz < 2^32 := by
    rw [hvz_def]
    exact valueBits_lt_two_pow zVec h_z_norm
  have h_total_lt : vz + 2^32 * carryVal < p := by
    have hvz_le : vz ≤ 2^32 - 1 := by omega
    have hle : vz + 2^32 * carryVal ≤ (2^32 - 1) + 2^32 * 3 :=
      Nat.add_le_add hvz_le (Nat.mul_le_mul_left _ h_carry_le)
    exact lt_trans (Nat.lt_of_le_of_lt hle (by norm_num)) h_large.elim
  have h_mul_lt : 2^32 * carryVal < p :=
    Nat.lt_of_le_of_lt (Nat.le_add_left _ _) h_total_lt
  have h_mul_val : ((2^32 : F p) * carryF).val = 2^32 * carryVal := by
    rw [ZMod.val_mul, pow32_val (p := p) hp32, h_carry_val]
    rw [Nat.mod_eq_of_lt h_mul_lt]
  have h_rhs_val : (fz + (2^32 : F p) * carryF).val = vz + 2^32 * carryVal := by
    rw [ZMod.val_add, h_fz, h_mul_val]
    rw [Nat.mod_eq_of_lt h_total_lt]
  have h_lhs_val : (fsum + 1).val = sumV + 1 := by
    rw [h_fsum_cast, show ((sumV : ℕ) : F p) + 1 = ((sumV + 1 : ℕ) : F p) from by push_cast; ring]
    exact ZMod.val_natCast_of_lt h_sum1_lt_p
  have h_nat_eq := congrArg ZMod.val h_lin'
  rw [h_lhs_val, h_rhs_val] at h_nat_eq
  refine ⟨?_, ?_⟩
  · rw [h_z_eval, ← hvz_def]
    change vz = (sumV + 1) % 2^32
    calc
      vz = (vz + 2^32 * carryVal) % 2^32 := by
        rw [show 2^32 * carryVal = carryVal * 2^32 by ring,
          Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hvz_lt]
      _ = (sumV + 1) % 2^32 := congrArg (fun t : ℕ => t % 2^32) h_nat_eq.symm
  · rw [h_z_eval]
    exact h_z_norm

set_option maxHeartbeats 1000000 in
theorem completeness2c {n : ℕ} (hn : n ≤ 4) :
    Completeness (F p) (main2c (p := p) hn) Assumptions := by
  circuit_proof_start [main2c, addMany2c]
  obtain ⟨h_env_z, h_env_c1⟩ := h_env
  set S := evalManyNat env input_var + 1 with hS_def
  have h_input_word (k : Fin n) :
      Vector.map (Expression.eval env.toEnvironment) input_var[k] = input[k] := by
    have h := getElem_eval_vector env.toEnvironment input_var k.val k.isLt
    rw [h_input] at h
    rw [← CircuitType.eval_var_fields env.toEnvironment (input_var[k])]
    exact h
  have hSm1_eq : evalManyNat env input_var
      = Finset.univ.sum fun k : Fin n => valueBits input[k] :=
    evalManyNat_eq_sum_valueBits env input_var input h_input_word
  have hS_eq : S = (Finset.univ.sum fun k : Fin n => valueBits input[k]) + 1 := by
    rw [hS_def, hSm1_eq]
  have hS_lt : S < 2^34 := by
    rw [hS_eq]; exact sum_valueBits_succ_lt_pow34 hn input h_assumptions
  have hp32 : (2:ℕ)^32 < p := lt_trans (by norm_num) h_large.elim
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have henv_i := h_env_z i
    simp only [Vector.getElem_ofFn] at henv_i
    rw [henv_i]
    rcases Nat.mod_two_eq_zero_or_one (S / 2^i.val) with h | h <;>
      rw [h] <;> push_cast <;> ring
  · rw [h_env_c1]
    rcases Nat.mod_two_eq_zero_or_one (S / 2^33) with h | h <;>
      rw [h] <;> push_cast <;> ring
  · set q := S / 2^32 with hq_def
    have hS_mod_lt : S % 2^32 < 2^32 := Nat.mod_lt _ (by norm_num)
    have h_z_eval := Add32.z_var_eval env.toEnvironment i₀
    have h_z_eval' : Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 32 fun i => (var {index := i₀ + i} : Expression (F p))) =
        Vector.ofFn fun i : Fin 32 => ((S % 2^32 / 2^i.val % 2 : ℕ) : F p) := by
      rw [h_z_eval]
      ext i hi
      simp only [Vector.getElem_ofFn]
      have this := h_env_z ⟨i, hi⟩
      simp only [Vector.getElem_ofFn] at this
      rw [this]
      congr 1
      rw [← Add32.testBit_ite_eq S i, ← Add32.testBit_ite_eq (S % 2^32) i]
      rw [Nat.testBit_mod_two_pow]
      simp [hi]
    have h_FZ : Expression.eval env.toEnvironment (fromBitsExpr
        (Vector.mapRange 32 fun i => (var {index := i₀ + i} : Expression (F p)))) =
        ((S % 2^32 : ℕ) : F p) := by
      show Expression.eval env.toEnvironment (Utils.Bits.fieldFromBitsExpr _) = _
      simp only [Utils.Bits.fieldFromBits_eval]
      rw [h_z_eval']
      exact Add32.fieldFromBits_bit_decomp (p := p) (S % 2^32) hS_mod_lt hp32
    have h_FS : Expression.eval env.toEnvironment (fromBitsExprSum input_var) + 1 =
        ((S : ℕ) : F p) := by
      rw [eval_fromBitsExprSum env.toEnvironment input_var input h_input_word, ← hSm1_eq, hS_def]
      push_cast; ring
    have hc1 : env.get (i₀ + 32) = ((q / 2 % 2 : ℕ) : F p) := by
      rw [h_env_c1]
      congr 1
      rw [hq_def, show (2:ℕ)^33 = 2^32 * 2 by norm_num, Nat.div_div_eq_div_mul]
    have hpow_ne := pow32_ne_zero (p := p) hp32
    have h_sub : ((S : ℕ) : F p) - ((S % 2^32 : ℕ) : F p) =
        (2^32 : F p) * ((q : ℕ) : F p) := by
      have hdec : S % 2^32 + 2^32 * q = S := by
        rw [hq_def]; exact Nat.mod_add_div S (2^32)
      have hcast := congrArg (Nat.cast : ℕ → F p) hdec
      push_cast at hcast
      rw [← hcast]; ring
    have h_inv : ((2^32 : F p)⁻¹ : F p) *
        (((S : ℕ) : F p) - ((S % 2^32 : ℕ) : F p)) = ((q : ℕ) : F p) := by
      rw [h_sub, ← mul_assoc, inv_mul_cancel₀ hpow_ne, one_mul]
    have h_inv' : ((2^32 : F p)⁻¹ : F p) *
        (((S : ℕ) : F p) + -((S % 2^32 : ℕ) : F p)) = ((q : ℕ) : F p) := by
      simpa [sub_eq_add_neg] using h_inv
    have hq_lt4 : q < 4 := by
      rw [hq_def]
      have hmul : S < 4 * 2^32 := by
        have hpow : 4 * 2^32 = 2^34 := by norm_num
        rwa [hpow]
      have hdiv := (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2^32)).mpr hmul
      simpa [Nat.mul_comm] using hdiv
    have hq_decomp : q = q % 2 + 2 * (q / 2 % 2) := by omega
    have hlow_nat : ((q : ℕ) : F p) - (2 : F p) * ((q / 2 % 2 : ℕ) : F p) =
        ((q % 2 : ℕ) : F p) := by
      have hcast := congrArg (Nat.cast : ℕ → F p) hq_decomp
      rw [Nat.cast_add, Nat.cast_mul] at hcast
      rw [hcast]
      ring
    have hlow_nat' : ((q : ℕ) : F p) +
        -((2 : F p) * ((q / 2 % 2 : ℕ) : F p)) = ((q % 2 : ℕ) : F p) := by
      simpa [sub_eq_add_neg] using hlow_nat
    rw [h_FS, h_FZ, hc1]
    rw [h_inv', hlow_nat']
    rcases Nat.mod_two_eq_zero_or_one q with h | h <;>
      rw [h] <;> push_cast <;> ring

omit h_large in
theorem costIs_addMany2c {n : ℕ} (hn : n ≤ 4)
    (xs : Vector (Var (fields 32) (F p)) n) :
    CostIs (addMany2c hn xs) ⟨33, 34⟩ :=
  CostIs.bind (CostIs.witnessVector 32 _) fun z =>
    CostIs.bind (CostIs.witnessField _) fun _ =>
      CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ =>
        CostIs.bind (CostIs.assertZero _) fun _ =>
          CostIs.bind (CostIs.assertZero _) fun _ => CostIs.pure z

omit h_large in
theorem r1cs_addMany2c {n : ℕ} (hn : n ≤ 4)
    (xs : Vector (Var (fields 32) (F p)) n)
    (hxs : ∀ k : Fin n, AffineW xs[k]) :
    IsR1CSCirc (addMany2c hn xs) :=
  IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector 32 _) fun zOff =>
  IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) fun cOff =>
  IsR1CSCirc.bind
    (IsR1CSCirc.forEach fun j m =>
      IsR1CSCirc.assertZero
        (isR1CSRow_mul (affineW_witnessVector_output 32 _ zOff j.val j.isLt)
          (Affine.sub (affineW_witnessVector_output 32 _ zOff j.val j.isLt)
            (Affine.const 1))) m)
    fun _ =>
  IsR1CSCirc.bind
    (IsR1CSCirc.assertZero
      (isR1CSRow_mul (affine_witnessField_output _ cOff)
        (Affine.sub (affine_witnessField_output _ cOff) (Affine.const 1))))
    fun _ =>
  IsR1CSCirc.bind
    (IsR1CSCirc.assertZero
      (isR1CSRow_mul
        (Affine.sub
          (Affine.fconst_mul _
            (Affine.sub
              (Affine.add (affine_fromBitsExprSum xs hxs) (Affine.const 1))
              (affine_fieldFromBitsExpr _ (affineW_witnessVector_output 32 _ zOff))))
          (Affine.fconst_mul _ (affine_witnessField_output _ cOff)))
        (Affine.sub
          (Affine.sub
            (Affine.fconst_mul _
              (Affine.sub
                (Affine.add (affine_fromBitsExprSum xs hxs) (Affine.const 1))
                (affine_fieldFromBitsExpr _ (affineW_witnessVector_output 32 _ zOff))))
            (Affine.fconst_mul _ (affine_witnessField_output _ cOff)))
          (Affine.const 1))))
    fun _ => IsR1CSCirc.pure _

def circuit2c {n : ℕ} (hn : n ≤ 4) :
    FormalCircuit (F p) (Inputs n) (fields 32) where
  main := main2c hn
  elaborated := elaborated2c hn
  Assumptions := Assumptions
  Spec := Spec2c
  soundness := soundness2c hn
  completeness := completeness2c hn

/-! ## Plain 4-word variant: modular addition over `n ≤ 4` words

Same `Spec` as the 7-word `circuit`, but `n ≤ 4` keeps the sum `< 2^34`, so a
single witnessed high carry (weight 2) plus the fused low-carry row suffice:
cost `⟨33, 34⟩` vs the 7-word adder's `⟨34, 35⟩`. -/

omit h_large in
lemma sum_valueBits_lt_pow34 {n : ℕ} (hn : n ≤ 4)
    (xs : Vector (fields 32 (F p)) n) (hxs : ∀ k : Fin n, Normalized xs[k]) :
    Finset.univ.sum (fun k : Fin n => valueBits xs[k]) < 2^34 := by
  have hsum_le :
      Finset.univ.sum (fun k : Fin n => valueBits xs[k]) ≤
        Finset.univ.sum (fun _k : Fin n => 2^32 - 1) := by
    apply Finset.sum_le_sum
    intro k _
    have hk := valueBits_lt_two_pow xs[k] (hxs k)
    omega
  rw [Finset.sum_const, Finset.card_fin] at hsum_le
  have hle : Finset.univ.sum (fun k : Fin n => valueBits xs[k]) ≤ n * (2^32 - 1) := by
    simpa using hsum_le
  have h2 : n * (2^32 - 1) ≤ 4 * (2^32 - 1) := Nat.mul_le_mul_right _ hn
  omega

/-- Plain fused (n ≤ 4)-operand 32-bit modular addition. -/
def addMany2 {n : ℕ} (_hn : n ≤ 4)
    (xs : Vector (Var (fields 32) (F p)) n) :
    Circuit (F p) (Var (fields 32) (F p)) := do
  let z ← witnessVector 32 fun env =>
    let s := evalManyNat env xs
    Vector.ofFn fun i : Fin 32 => ((s / 2^i.val % 2 : ℕ) : F p)
  let c1 ← witnessField fun env =>
    let s := evalManyNat env xs
    ((s / 2^33 % 2 : ℕ) : F p)
  Circuit.forEach (Vector.finRange 32) fun i =>
    assertZero (z[i] * (z[i] - 1))
  assertZero (c1 * (c1 - 1))
  let lowCarry :=
    ((2^32 : F p)⁻¹ : F p) * (fromBitsExprSum xs - fromBitsExpr z) -
      (2 : F p) * c1
  assertZero (lowCarry * (lowCarry - 1))
  return z

def main2 {n : ℕ} (hn : n ≤ 4)
    (input : Var (Inputs n) (F p)) : Circuit (F p) (Var (fields 32) (F p)) :=
  addMany2 hn input

instance elaborated2 {n : ℕ} (hn : n ≤ 4) :
    ElaboratedCircuit (F p) (Inputs n) (fields 32) (main2 (p := p) hn) := by
  elaborate_circuit

set_option maxHeartbeats 1000000 in
theorem soundness2 {n : ℕ} (hn : n ≤ 4) :
    Soundness (F p) (main2 (p := p) hn) Assumptions Spec := by
  circuit_proof_start [main2, addMany2]
  obtain ⟨h_z_bool, h_c1_bool, h_low⟩ := h_holds
  have h_input_word (k : Fin n) :
      Vector.map (Expression.eval env) input_var[k] = input[k] := by
    have h := getElem_eval_vector env input_var k.val k.isLt
    rw [h_input] at h
    rw [← CircuitType.eval_var_fields env (input_var[k])]
    exact h
  have h_z_eval : Vector.map (Expression.eval env)
      (Vector.mapRange 32 fun i => (var {index := i₀ + i} : Expression (F p))) =
      Vector.ofFn fun i : Fin 32 => env.get (i₀ + i.val) := Add32.z_var_eval env i₀
  have h_z_norm : Normalized (Vector.ofFn fun i : Fin 32 => env.get (i₀ + i.val)) :=
    Add32.normalized_of_bool_holds env i₀ h_z_bool
  set sumV := Finset.univ.sum fun k : Fin n => valueBits input[k] with hsumV_def
  have hp32 : (2:ℕ)^32 < p := by
    have hp := h_large.elim
    norm_num at hp ⊢
    omega
  have h_sum_lt : sumV < 2^34 := by
    rw [hsumV_def]; exact sum_valueBits_lt_pow34 hn input h_assumptions
  have h_sum_lt_p : sumV < p :=
    lt_trans (lt_trans h_sum_lt (by norm_num)) h_large.elim
  set fsum := Expression.eval env (fromBitsExprSum input_var) with hfsum_def
  set fz := Expression.eval env (fromBitsExpr
    (Vector.mapRange 32 fun i => (var {index := i₀ + i} : Expression (F p)))) with hfz_def
  have h_fsum_cast : fsum = ((sumV : ℕ) : F p) := by
    rw [hfsum_def, hsumV_def, eval_fromBitsExprSum env input_var input h_input_word]
  set zVec := Vector.ofFn fun i : Fin 32 => env.get (i₀ + i.val) with hzVec_def
  set vz := valueBits zVec with hvz_def
  have h_fz : fz.val = vz := by
    rw [hfz_def]
    exact Add32.fromBitsExpr_val_eq env _ zVec h_z_eval h_z_norm hp32
  set cc := env.get (i₀ + 32) with hcc_def
  have h_cc_bool : IsBool cc := by
    apply Add32.isbool_of_bool_constraint
    simpa [cc] using h_c1_bool
  set lowF := ((2^32 : F p)⁻¹ : F p) * (fsum - fz) - (2 : F p) * cc with hlowF_def
  have h_low_bool : IsBool lowF := by
    apply Add32.isbool_of_bool_constraint
    simpa [lowF, fsum, fz, cc, sub_eq_add_neg] using h_low
  set carryF := lowF + (2 : F p) * cc with hcarryF_def
  have h_lin' : fsum = fz + (2^32 : F p) * carryF := by
    have hpow_ne := pow32_ne_zero (p := p) hp32
    rw [hcarryF_def, hlowF_def]
    have hmul : (2^32 : F p) * ((2^32 : F p)⁻¹ * (fsum - fz)) = fsum - fz := by
      rw [← mul_assoc, mul_inv_cancel₀ hpow_ne, one_mul]
    calc
      fsum = fz + (fsum - fz) := by ring
      _ = fz + (2^32 : F p) * ((2^32 : F p)⁻¹ * (fsum - fz)) := by rw [hmul]
      _ = fz + (2^32 : F p) *
          (((2^32 : F p)⁻¹ * (fsum - fz) - 2 * cc) + 2 * cc) := by ring
  set carryVal := lowF.val + 2 * cc.val with hcarryVal_def
  have h_low_le : lowF.val ≤ 1 := by
    rcases IsBool.val_of_IsBool h_low_bool with h | h <;> omega
  have h_cc_le : cc.val ≤ 1 := by
    rcases IsBool.val_of_IsBool h_cc_bool with h | h <;> omega
  have h_carry_le : carryVal ≤ 3 := by rw [hcarryVal_def]; omega
  have h_carry_val : carryF.val = carryVal := by
    rw [hcarryF_def, hcarryVal_def]
    exact carryBits2_val h_low_bool h_cc_bool
  have hvz_lt : vz < 2^32 := by
    rw [hvz_def]
    exact valueBits_lt_two_pow zVec h_z_norm
  have h_total_lt : vz + 2^32 * carryVal < p := by
    have hvz_le : vz ≤ 2^32 - 1 := by omega
    have hle : vz + 2^32 * carryVal ≤ (2^32 - 1) + 2^32 * 3 :=
      Nat.add_le_add hvz_le (Nat.mul_le_mul_left _ h_carry_le)
    exact lt_trans (Nat.lt_of_le_of_lt hle (by norm_num)) h_large.elim
  have h_mul_lt : 2^32 * carryVal < p :=
    Nat.lt_of_le_of_lt (Nat.le_add_left _ _) h_total_lt
  have h_mul_val : ((2^32 : F p) * carryF).val = 2^32 * carryVal := by
    rw [ZMod.val_mul, pow32_val (p := p) hp32, h_carry_val]
    rw [Nat.mod_eq_of_lt h_mul_lt]
  have h_rhs_val : (fz + (2^32 : F p) * carryF).val = vz + 2^32 * carryVal := by
    rw [ZMod.val_add, h_fz, h_mul_val]
    rw [Nat.mod_eq_of_lt h_total_lt]
  have h_lhs_val : fsum.val = sumV := by
    rw [h_fsum_cast]
    exact ZMod.val_natCast_of_lt h_sum_lt_p
  have h_nat_eq := congrArg ZMod.val h_lin'
  rw [h_lhs_val, h_rhs_val] at h_nat_eq
  refine ⟨?_, ?_⟩
  · rw [h_z_eval, ← hvz_def]
    change vz = sumV % 2^32
    calc
      vz = (vz + 2^32 * carryVal) % 2^32 := by
        rw [show 2^32 * carryVal = carryVal * 2^32 by ring,
          Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hvz_lt]
      _ = sumV % 2^32 := congrArg (fun t : ℕ => t % 2^32) h_nat_eq.symm
  · rw [h_z_eval]
    exact h_z_norm

set_option maxHeartbeats 1000000 in
theorem completeness2 {n : ℕ} (hn : n ≤ 4) :
    Completeness (F p) (main2 (p := p) hn) Assumptions := by
  circuit_proof_start [main2, addMany2]
  obtain ⟨h_env_z, h_env_c1⟩ := h_env
  set S := evalManyNat env input_var with hS_def
  have h_input_word (k : Fin n) :
      Vector.map (Expression.eval env.toEnvironment) input_var[k] = input[k] := by
    have h := getElem_eval_vector env.toEnvironment input_var k.val k.isLt
    rw [h_input] at h
    rw [← CircuitType.eval_var_fields env.toEnvironment (input_var[k])]
    exact h
  have hS_eq : S = Finset.univ.sum fun k : Fin n => valueBits input[k] :=
    evalManyNat_eq_sum_valueBits env input_var input h_input_word
  have hS_lt : S < 2^34 := by
    rw [hS_eq]; exact sum_valueBits_lt_pow34 hn input h_assumptions
  have hp32 : (2:ℕ)^32 < p := lt_trans (by norm_num) h_large.elim
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have henv_i := h_env_z i
    simp only [Vector.getElem_ofFn] at henv_i
    rw [henv_i]
    rcases Nat.mod_two_eq_zero_or_one (S / 2^i.val) with h | h <;>
      rw [h] <;> push_cast <;> ring
  · rw [h_env_c1]
    rcases Nat.mod_two_eq_zero_or_one (S / 2^33) with h | h <;>
      rw [h] <;> push_cast <;> ring
  · set q := S / 2^32 with hq_def
    have hS_mod_lt : S % 2^32 < 2^32 := Nat.mod_lt _ (by norm_num)
    have h_z_eval := Add32.z_var_eval env.toEnvironment i₀
    have h_z_eval' : Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 32 fun i => (var {index := i₀ + i} : Expression (F p))) =
        Vector.ofFn fun i : Fin 32 => ((S % 2^32 / 2^i.val % 2 : ℕ) : F p) := by
      rw [h_z_eval]
      ext i hi
      simp only [Vector.getElem_ofFn]
      have this := h_env_z ⟨i, hi⟩
      simp only [Vector.getElem_ofFn] at this
      rw [this]
      congr 1
      rw [← Add32.testBit_ite_eq S i, ← Add32.testBit_ite_eq (S % 2^32) i]
      rw [Nat.testBit_mod_two_pow]
      simp [hi]
    have h_FZ : Expression.eval env.toEnvironment (fromBitsExpr
        (Vector.mapRange 32 fun i => (var {index := i₀ + i} : Expression (F p)))) =
        ((S % 2^32 : ℕ) : F p) := by
      show Expression.eval env.toEnvironment (Utils.Bits.fieldFromBitsExpr _) = _
      simp only [Utils.Bits.fieldFromBits_eval]
      rw [h_z_eval']
      exact Add32.fieldFromBits_bit_decomp (p := p) (S % 2^32) hS_mod_lt hp32
    have h_FS : Expression.eval env.toEnvironment (fromBitsExprSum input_var) =
        ((S : ℕ) : F p) := by
      rw [eval_fromBitsExprSum env.toEnvironment input_var input h_input_word, ← hS_eq]
    have hc1 : env.get (i₀ + 32) = ((q / 2 % 2 : ℕ) : F p) := by
      rw [h_env_c1]
      congr 1
      rw [hq_def, show (2:ℕ)^33 = 2^32 * 2 by norm_num, Nat.div_div_eq_div_mul]
    have hpow_ne := pow32_ne_zero (p := p) hp32
    have h_sub : ((S : ℕ) : F p) - ((S % 2^32 : ℕ) : F p) =
        (2^32 : F p) * ((q : ℕ) : F p) := by
      have hdec : S % 2^32 + 2^32 * q = S := by
        rw [hq_def]; exact Nat.mod_add_div S (2^32)
      have hcast := congrArg (Nat.cast : ℕ → F p) hdec
      push_cast at hcast
      rw [← hcast]; ring
    have h_inv : ((2^32 : F p)⁻¹ : F p) *
        (((S : ℕ) : F p) - ((S % 2^32 : ℕ) : F p)) = ((q : ℕ) : F p) := by
      rw [h_sub, ← mul_assoc, inv_mul_cancel₀ hpow_ne, one_mul]
    have h_inv' : ((2^32 : F p)⁻¹ : F p) *
        (((S : ℕ) : F p) + -((S % 2^32 : ℕ) : F p)) = ((q : ℕ) : F p) := by
      simpa [sub_eq_add_neg] using h_inv
    have hq_lt4 : q < 4 := by
      rw [hq_def]
      have hmul : S < 4 * 2^32 := by
        have hpow : 4 * 2^32 = 2^34 := by norm_num
        rwa [hpow]
      have hdiv := (Nat.div_lt_iff_lt_mul (by norm_num : 0 < 2^32)).mpr hmul
      simpa [Nat.mul_comm] using hdiv
    have hq_decomp : q = q % 2 + 2 * (q / 2 % 2) := by omega
    have hlow_nat : ((q : ℕ) : F p) - (2 : F p) * ((q / 2 % 2 : ℕ) : F p) =
        ((q % 2 : ℕ) : F p) := by
      have hcast := congrArg (Nat.cast : ℕ → F p) hq_decomp
      rw [Nat.cast_add, Nat.cast_mul] at hcast
      rw [hcast]
      ring
    have hlow_nat' : ((q : ℕ) : F p) +
        -((2 : F p) * ((q / 2 % 2 : ℕ) : F p)) = ((q % 2 : ℕ) : F p) := by
      simpa [sub_eq_add_neg] using hlow_nat
    rw [h_FS, h_FZ, hc1]
    rw [h_inv', hlow_nat']
    rcases Nat.mod_two_eq_zero_or_one q with h | h <;>
      rw [h] <;> push_cast <;> ring

omit h_large in
theorem costIs_addMany2 {n : ℕ} (hn : n ≤ 4)
    (xs : Vector (Var (fields 32) (F p)) n) :
    CostIs (addMany2 hn xs) ⟨33, 34⟩ :=
  CostIs.bind (CostIs.witnessVector 32 _) fun z =>
    CostIs.bind (CostIs.witnessField _) fun _ =>
      CostIs.bind (CostIs.forEach fun _ => CostIs.assertZero _) fun _ =>
        CostIs.bind (CostIs.assertZero _) fun _ =>
          CostIs.bind (CostIs.assertZero _) fun _ => CostIs.pure z

omit h_large in
theorem r1cs_addMany2 {n : ℕ} (hn : n ≤ 4)
    (xs : Vector (Var (fields 32) (F p)) n)
    (hxs : ∀ k : Fin n, AffineW xs[k]) :
    IsR1CSCirc (addMany2 hn xs) :=
  IsR1CSCirc.bind_out (IsR1CSCirc.witnessVector 32 _) fun zOff =>
  IsR1CSCirc.bind_out (IsR1CSCirc.witnessField _) fun cOff =>
  IsR1CSCirc.bind
    (IsR1CSCirc.forEach fun j m =>
      IsR1CSCirc.assertZero
        (isR1CSRow_mul (affineW_witnessVector_output 32 _ zOff j.val j.isLt)
          (Affine.sub (affineW_witnessVector_output 32 _ zOff j.val j.isLt)
            (Affine.const 1))) m)
    fun _ =>
  IsR1CSCirc.bind
    (IsR1CSCirc.assertZero
      (isR1CSRow_mul (affine_witnessField_output _ cOff)
        (Affine.sub (affine_witnessField_output _ cOff) (Affine.const 1))))
    fun _ =>
  IsR1CSCirc.bind
    (IsR1CSCirc.assertZero
      (isR1CSRow_mul
        (Affine.sub
          (Affine.fconst_mul _
            (Affine.sub
              (affine_fromBitsExprSum xs hxs)
              (affine_fieldFromBitsExpr _ (affineW_witnessVector_output 32 _ zOff))))
          (Affine.fconst_mul _ (affine_witnessField_output _ cOff)))
        (Affine.sub
          (Affine.sub
            (Affine.fconst_mul _
              (Affine.sub
                (affine_fromBitsExprSum xs hxs)
                (affine_fieldFromBitsExpr _ (affineW_witnessVector_output 32 _ zOff))))
            (Affine.fconst_mul _ (affine_witnessField_output _ cOff)))
          (Affine.const 1))))
    fun _ => IsR1CSCirc.pure _

def circuit2 {n : ℕ} (hn : n ≤ 4) :
    FormalCircuit (F p) (Inputs n) (fields 32) where
  main := main2 hn
  elaborated := elaborated2 hn
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness2 hn
  completeness := completeness2 hn

/-! ## Wide-adder support helpers (used by `AddManyWide`).

`sumEvalNat` / `sumExpr` mirror `evalManyNat` / `fromBitsExprSum` but in the
foldl/name shape the wide adder's proofs are written against; `highExpr` is the
generic weighted high-carry expression (the base `addMany` inlines 2 carry bits,
the wide adder needs 3). -/

/-- The natural-number value of all addends under a prover environment. -/
def sumEvalNat {n : ℕ} (env : ProverEnvironment (F p))
    (words : Var (ProvableVector (fields 32) n) (F p)) : ℕ :=
  ∑ i : Fin n, evalBitsNat env (words[i.val]'i.isLt)

/-- The linear-combination expression `Σⱼ fromBits(word j)`. -/
def sumExpr {n : ℕ} (words : Var (ProvableVector (fields 32) n) (F p)) : Expression (F p) :=
  Fin.foldl n (fun acc (i : Fin n) => acc + fromBitsExpr (words[i.val]'i.isLt)) 0

/-- The affine high-carry contribution `Σⱼ 2^(j+1) · cv[j]`. -/
def highExpr {m : ℕ} (cv : Var (fields m) (F p)) : Expression (F p) :=
  Fin.foldl m (fun acc (j : Fin m) =>
    acc + cv[j.val]'j.isLt * (((2^(j.val+1) : ℕ) : F p) : Expression (F p))) 0

omit h_large in
/-- `Expression.eval` distributes over a `Fin.foldl` of added terms. -/
lemma eval_foldl_add (env : Environment (F p)) :
    ∀ (m : ℕ) (g : Fin m → Expression (F p)),
      Expression.eval env (Fin.foldl m (fun acc (i : Fin m) => acc + g i) 0)
        = ∑ i : Fin m, Expression.eval env (g i) := by
  intro m
  induction m with
  | zero => intro g; simp [Fin.foldl_zero, Expression.eval]
  | succ k ih =>
    intro g
    rw [Fin.foldl_succ_last, Fin.sum_univ_castSucc]
    rw [show Fin.foldl k
          (fun acc (i : Fin k) => (fun acc (i : Fin (k+1)) => acc + g i) acc i.castSucc) 0 =
        Fin.foldl k (fun acc (i : Fin k) => acc + (fun i : Fin k => g i.castSucc) i) 0 from rfl]
    show Expression.eval env (Expression.add
      (Fin.foldl k (fun acc (i : Fin k) => acc + g i.castSucc) 0) (g (Fin.last k))) = _
    rw [eval_add, ih (fun i : Fin k => g i.castSucc)]

omit h_large in
/-- `Expression.eval` distributes over the `sumExpr` fold. -/
lemma eval_sum_fromBits (env : Environment (F p)) :
    ∀ (m : ℕ) (g : Fin m → Var (fields 32) (F p)),
      Expression.eval env (Fin.foldl m (fun acc (i : Fin m) => acc + fromBitsExpr (g i)) 0)
        = ∑ i : Fin m, Expression.eval env (fromBitsExpr (g i)) := by
  intro m g
  exact eval_foldl_add env m (fun i => fromBitsExpr (g i))

omit h_large in
/-- `highExpr` evaluates to the weighted sum of its entries. -/
lemma eval_highExpr {m : ℕ} (env : Environment (F p)) (cv : Var (fields m) (F p)) :
    Expression.eval env (highExpr cv) =
      ∑ j : Fin m, Expression.eval env (cv[j.val]'j.isLt) * ((2^(j.val+1) : ℕ) : F p) := by
  rw [highExpr, eval_foldl_add env m
    (fun j : Fin m => cv[j.val]'j.isLt * (((2^(j.val+1) : ℕ) : F p) : Expression (F p)))]
  apply Finset.sum_congr rfl
  intro j _
  show Expression.eval env (Expression.mul (cv[j.val]'j.isLt)
    (Expression.const ((2^(j.val+1) : ℕ) : F p))) = _
  rw [eval_mul]
  rfl

omit h_large in
/-- `sumExpr` evaluates to the field-cast of the ℕ sum of `valueBits`. -/
lemma sumExpr_eval {n : ℕ} (env : Environment (F p))
    (words_var : Var (ProvableVector (fields 32) n) (F p))
    (words : ProvableVector (fields 32) n (F p))
    (h_eval : eval env words_var = words) :
    Expression.eval env (sumExpr words_var) =
      ((∑ i : Fin n, valueBits words[i] : ℕ) : F p) := by
  rw [sumExpr, eval_sum_fromBits env]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  have hi : Vector.map (Expression.eval env) (words_var[i.val]'i.isLt) = words[i.val]'i.isLt := by
    rw [← CircuitType.eval_var_fields env (words_var[i.val]'i.isLt)]
    rw [getElem_eval_vector env words_var i.val i.isLt, h_eval]
  exact Add32.fromBitsExpr_eval_normalized env _ _ hi

end AddMany
end Solution.SHA256
end
