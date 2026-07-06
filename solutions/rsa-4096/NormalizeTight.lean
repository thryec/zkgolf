import Solution.RSASSAPKCS1v15_SHA256_4096_65537.Normalize

/-!
# RSA big-integer *tight* range-check gadget — `NormalizeTight`

Like `Normalize` (gadget G1), but the **top** limb is range-checked to only `tb`
bits instead of the full `B`. This certifies not just `Normalized` (every limb
`< 2^B`) but also the sharper value bound `value < 2^((m-1)·B + tb)`.

Used by the lazy-reduction `MulMod`: keeping each modular-multiplication output
below `2^((m-1)·B + tb) = 2^4096` (rather than `2^(m·B) = 2^4114`) is what keeps the
next step's quotient inside `m` limbs, so we can drop the per-modmul `LessThan`
(canonical `< n`) check and rely on congruence mod `n` propagating, with the
final octet-string comparison pinning the result canonical.

All range checks use the implicit-top-bit `RangeCheck` gadget (`n-1` witnessed
bits + a derived affine top digit), saving one allocation and one row per limb;
the `htb` hypothesis therefore carries `1 ≤ tb` alongside `2^tb < p`.
-/

namespace Solution.RSASSAPKCS1v15_SHA256_4096_65537
open Specs.RSA

section
variable {p : ℕ} [Fact p.Prime]
variable {m : ℕ} [NeZero m]

/-- Tight sum bound: if the first `n` weighted base-`2^B` limbs are `< 2^B` and the
top one is `< 2^tb`, the whole sum is `< 2^(B·n + tb)`. (Max is `2^(B·n+tb) − 1`.) -/
theorem sum_lt_pow_tight {B tb n : ℕ} (f : Fin (n + 1) → ℕ)
    (hf : ∀ i : Fin n, f i.castSucc < 2 ^ B) (hlast : f (Fin.last n) < 2 ^ tb) :
    (∑ i : Fin (n + 1), f i * 2 ^ (B * i.val)) < 2 ^ (B * n + tb) := by
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.val_last, Fin.val_castSucc]
  have hhead : (∑ i : Fin n, f i.castSucc * 2 ^ (B * i.val)) < 2 ^ (B * n) :=
    sum_lt_pow (fun i => f i.castSucc) hf
  have htail : f (Fin.last n) * 2 ^ (B * n) ≤ (2 ^ tb - 1) * 2 ^ (B * n) :=
    Nat.mul_le_mul_right _ (by omega)
  have hpow : (2:ℕ) ^ (B * n + tb) = 2 ^ tb * 2 ^ (B * n) := by rw [pow_add]; ring
  have hexp : (2 ^ tb - 1) * 2 ^ (B * n) = 2 ^ (B * n + tb) - 2 ^ (B * n) := by
    rw [hpow, Nat.sub_mul, Nat.one_mul]
  have hTS : (2:ℕ) ^ (B * n) ≤ 2 ^ (B * n + tb) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [hexp] at htail
  omega

/-- `NormalizedTight B tb x`: every limb `< 2^B` and the top limb `< 2^tb`. -/
def BigInt.NormalizedTight (B tb : ℕ) (x : BigInt m (F p)) : Prop :=
  BigInt.Normalized B x ∧ (x[m - 1]'(by have := Nat.pos_of_neZero m; omega)).val < 2 ^ tb

omit [Fact (Nat.Prime p)] in
/-- A tight-normalized big integer is bounded by `2^((m-1)·B + tb)`. -/
theorem BigInt.value_lt_tight {B tb : ℕ} {x : BigInt m (F p)} (htb : tb ≤ B)
    (h : BigInt.NormalizedTight B tb x) :
    BigInt.value B x < 2 ^ ((m - 1) * B + tb) := by
  obtain ⟨hnorm, htop⟩ := h
  rw [BigInt.value_eq_sum, show (m - 1) * B + tb = B * (m - 1) + tb by ring]
  have hm : m = (m - 1) + 1 := by have := Nat.pos_of_neZero m; omega
  -- reindex the `Fin m` sum as a `Fin ((m-1)+1)` sum
  rw [Fintype.sum_equiv (finCongr hm) (fun k : Fin m => (x[k]).val * 2 ^ (B * k.val))
      (fun i : Fin ((m - 1) + 1) => (x[i.val]'(by omega)).val * 2 ^ (B * i.val))
      (fun k => by simp only [finCongr_apply, Fin.coe_cast, Fin.getElem_fin])]
  exact sum_lt_pow_tight _
    (fun i => by
      have := hnorm ⟨i.castSucc.val, by have := i.isLt; omega⟩
      simpa [Fin.getElem_fin] using this)
    (by simpa [Fin.val_last] using htop)

/-! ## `NormalizeTight` -/

namespace NormalizeTight

/-- Range-check the first `m-1` limbs to `B` bits and the top limb to `tb` bits,
each with an implicit top-bit range check. -/
def main (P : BigIntParams p m) (tb : ℕ) (htb : 1 ≤ tb ∧ 2 ^ tb < p) [Fact (p > 2)]
    (x : Var (BigInt m) (F p)) : Circuit (F p) Unit := do
  Circuit.forEach x.pop (fun xi => RangeCheck.circuit P.B P.hB P.hB1 xi)
  RangeCheck.circuit tb htb.2 htb.1 (x[m - 1]'(by have := Nat.pos_of_neZero m; omega))

instance elaborated (P : BigIntParams p m) (tb : ℕ) (htb : 1 ≤ tb ∧ 2 ^ tb < p) [Fact (p > 2)] :
    ElaboratedCircuit (F p) (BigInt m) unit (main P tb htb) where
  localLength _ := (m - 1) * (P.B - 1) + (tb - 1)
  localLength_eq := by
    intro input offset
    simp only [main, circuit_norm, RangeCheck.circuit]
  subcircuitsConsistent := by
    intro input offset
    simp +arith only [main, circuit_norm, RangeCheck.circuit]
  channelsLawful := by
    simp only [main, circuit_norm, RangeCheck.circuit]

def Assumptions (_ : BigInt m (F p)) : Prop := True

def Spec (B tb : ℕ) (x : BigInt m (F p)) : Prop :=
  BigInt.NormalizedTight B tb x

/-- The `NormalizeTight` formal assertion: every limb is `< 2^B` and the top limb
is `< 2^tb`, so `value < 2^((m-1)·B + tb)`. -/
def circuit (P : BigIntParams p m) (tb : ℕ) (htb : 1 ≤ tb ∧ 2 ^ tb < p) (htbB : tb ≤ P.B) [Fact (p > 2)] :
    FormalAssertion (F p) (BigInt m) where
  main := main P tb htb
  Assumptions := Assumptions
  Spec := Spec P.B tb
  soundness := by
    circuit_proof_start
    simp only [circuit_norm, RangeCheck.circuit] at h_holds
    obtain ⟨h_pop, h_top⟩ := h_holds
    have h_top' : (input[m - 1]'(by have := Nat.pos_of_neZero m; omega)).val < 2 ^ tb := by
      rw [← h_input, Vector.getElem_map]; exact h_top trivial
    have h_pop' : ∀ j (hj : j < m - 1), (input[j]'(by omega)).val < 2 ^ P.B := by
      intro j hj
      have hp := h_pop ⟨j, hj⟩ trivial
      simpa [Vector.getElem_pop', ← h_input, Vector.getElem_map] using hp
    refine ⟨⟨?_, h_top'⟩, fun i => Or.inl rfl, Or.inl rfl⟩
    intro i
    rw [Fin.getElem_fin]
    rcases Nat.lt_or_ge i.val (m - 1) with hlt | hge
    · exact h_pop' i.val hlt
    · have hi : i.val = m - 1 := by have := i.isLt; omega
      simp only [hi]
      exact lt_of_lt_of_le h_top' (Nat.pow_le_pow_right (by norm_num) htbB)
  completeness := by
    circuit_proof_start
    simp only [Spec, BigInt.NormalizedTight, BigInt.Normalized] at h_spec
    obtain ⟨hnorm, htop⟩ := h_spec
    simp only [circuit_norm, RangeCheck.circuit]
    refine ⟨fun i => ⟨trivial, ?_⟩, trivial, ?_⟩
    · have := hnorm ⟨i.val, by have := i.isLt; omega⟩
      simpa [Vector.getElem_pop', Fin.getElem_fin, ← h_input, Vector.getElem_map] using this
    · simpa [Fin.getElem_fin, ← h_input, Vector.getElem_map] using htop

end NormalizeTight

end
end Solution.RSASSAPKCS1v15_SHA256_4096_65537
