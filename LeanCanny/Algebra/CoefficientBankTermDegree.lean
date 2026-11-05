/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.CoefficientBankTermQuery
/-! # Finite spatial degree boxes for actual common-bank term queries -/
@[expose] public section
namespace LeanCanny.Algebra.CoefficientBankTermDegree
open scoped Classical BigOperators
variable {R σ : Type*} [CommRing R]
theorem cleared_degree (A M W E : ℕ) (a : ℕ → R) (e : ℕ → ℕ → ℕ)
    (n d : ℕ → MvPolynomial σ R)
    (he : ∀ r,r<M → ∀ i,i<A → e r i≤W)
    (hn : ∀ i,i<A → (n i).totalDegree≤E) (hd : ∀ i,i<A → (d i).totalDegree≤E) :
    (CoefficientIndexedRationalClearing.cleared A M W a e n d).totalDegree≤A*W*E := by
  unfold CoefficientIndexedRationalClearing.cleared
  apply MvPolynomial.totalDegree_finsetSum_le
  intro r hr
  apply (MvPolynomial.totalDegree_mul _ _).trans
  rw [MvPolynomial.totalDegree_C,Nat.zero_add]
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ _i ∈ Finset.range A,W*E := by
      apply Finset.sum_le_sum
      intro i hi
      have HE := he r (Finset.mem_range.mp hr) i (Finset.mem_range.mp hi)
      calc
        _ ≤ (n i^e r i).totalDegree+(d i^(W-e r i)).totalDegree := MvPolynomial.totalDegree_mul _ _
        _ ≤ e r i*(n i).totalDegree+(W-e r i)*(d i).totalDegree :=
          Nat.add_le_add (MvPolynomial.totalDegree_pow _ _) (MvPolynomial.totalDegree_pow _ _)
        _ ≤ e r i*E+(W-e r i)*E := Nat.add_le_add
          (Nat.mul_le_mul_left _ (hn i (Finset.mem_range.mp hi)))
          (Nat.mul_le_mul_left _ (hd i (Finset.mem_range.mp hi)))
        _ = W*E := by rw [← Nat.add_mul,Nat.add_sub_of_le HE]
    _ = A*W*E := by simp only [Finset.sum_const,Finset.card_range,smul_eq_mul,Nat.mul_assoc]

noncomputable def degreeBound (A : CoefficientBankTermQuery.Arguments R) (p : LeanCanny.ETR.Term) : ℕ :=
  p.toData.size * (2 * p.toData.size) *
    UniformIntegralPowerSchedule.birth A.horizon (2 ^ A.width) A.horizon

private theorem numerator_degree [Nontrivial R] (A : CoefficientBankTermQuery.Arguments R)
    (hb : A.birth ≤ A.horizon) (i : ℕ) :
    (CoefficientBankTermQuery.numerator A i).totalDegree ≤
      UniformIntegralPowerSchedule.birth A.horizon (2 ^ A.width) A.horizon := by
  unfold CoefficientBankTermQuery.numerator
  split_ifs with hi
  · apply (MvPolynomial.totalDegree_mul _ _).trans
    rw [MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X_pow, Nat.zero_add]
    exact UniformIntegralPowerSchedule.birth_le _ _ _ (hi.le.trans hb)
  · simp

/-- Fixed indexed clearing bounds spatial support independently of coefficients. -/
theorem degree [Nontrivial R] (A : CoefficientBankTermQuery.Arguments R) (p : LeanCanny.ETR.Term)
    (hb : A.birth ≤ A.horizon) :
    (CoefficientBankTermQuery.polynomial A p).totalDegree ≤ degreeBound A p := by
  unfold CoefficientBankTermQuery.polynomial CoefficientIndexedRationalClearing.term degreeBound
  apply cleared_degree
  · intro r _ i _
    have HE := p.monomialExponent_le r i
    have HD := p.degreeBound_le_dataSize
    omega
  · intro i _
    exact numerator_degree A hb i
  · intro i _
    simp only [CoefficientBankTermQuery.denominator, MvPolynomial.totalDegree_C, Nat.zero_le]

end LeanCanny.Algebra.CoefficientBankTermDegree
