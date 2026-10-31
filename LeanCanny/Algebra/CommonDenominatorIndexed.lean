/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CommonDenominatorSpecialization
public import LeanCanny.Algebra.IndexedRationalSubstitution

/-! # Common-denominator clearing from native indexed substitution

Per-coordinate clearing uses a larger common integer power. Extra powers
only multiply the exact total-degree clearing by a constant. The indexed
native reader therefore needs no division modulo its requested modulus.
-/

@[expose] public section
namespace LeanCanny.Algebra.CommonDenominatorSpecialization
open MvPolynomial
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {σ τ R : Type*} [Fintype σ] [CommRing R]

theorem degree_mul (D : ℕ) (q : R) (v : σ → MvPolynomial τ R) (E : ℕ)
    (hv : ∀ i, (v i).totalDegree ≤ E) (p : MvPolynomial σ R) :
    (clear D q v p).totalDegree ≤ p.totalDegree * E := by
  change (∑ e ∈ p.support, C (p.coeff e) * factor D q v e).totalDegree ≤ _
  apply totalDegree_finsetSum_le
  intro e he
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, Nat.zero_add, factor]
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, Nat.zero_add]
  apply (totalDegree_finsetProd _ _).trans
  calc
    _ ≤ ∑ i, e i * E := Finset.sum_le_sum (fun i _ =>
      (totalDegree_pow _ _).trans (Nat.mul_le_mul_left (e i) (hv i)))
    _ = e.degree * E := by rw [← Finset.sum_mul, Finsupp.degree_eq_sum]
    _ ≤ p.totalDegree * E := Nat.mul_le_mul_right E (MvPolynomial.le_totalDegree he)

theorem pad (D extra : ℕ) (q : R) (v : σ → MvPolynomial τ R) (p : MvPolynomial σ R)
    (hp : p.totalDegree ≤ D) :
    clear (D + extra) q v p = C (q ^ extra) * clear D q v p := by
  change (∑ e ∈ p.support, C (p.coeff e) * factor (D + extra) q v e) =
    C (q ^ extra) * ∑ e ∈ p.support, C (p.coeff e) * factor D q v e
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  have HD : e.degree ≤ D := (MvPolynomial.le_totalDegree he).trans hp
  have HE : D + extra - e.degree = extra + (D - e.degree) := by omega
  simp only [factor, HE, pow_add, map_mul]
  ring

theorem indexed (A M W : ℕ) (q : R) (a : ℕ → R) (e : ℕ → ℕ → ℕ)
    (v : Fin A → MvPolynomial τ R) (ψ : MvPolynomial τ R →+* Polynomial R)
    (hψ : ∀ c, ψ (C c) = Polynomial.C c) (num : ℕ → Polynomial R)
    (hnum : ∀ i : Fin A, ψ (v i) = num i.val)
    (he : ∀ r, r < M → ∀ i, i < A → e r i ≤ W) :
    ψ (clear (A * W) q v (RationalSubstitution.Indexed.source A M a e)) =
      RationalSubstitution.Indexed.cleared A M W a e num (fun _ => Polynomial.C q) := by
  rw [RationalSubstitution.Indexed.source, map_sum, map_sum]
  unfold RationalSubstitution.Indexed.cleared
  apply Finset.sum_congr rfl
  intro r hr
  rw [CommonDenominatorSpecialization.monomial]
  simp only [factor, map_mul, map_prod, map_pow, hψ, hnum]
  have HE : (∑ i : Fin A, (W - e r i.val)) + (RationalSubstitution.Indexed.exponentVector A (e r)).degree = A * W := by
    rw [Finsupp.degree_eq_sum, ← Finset.sum_add_distrib]
    calc
      _ = ∑ _i : Fin A, W := by
        apply Finset.sum_congr rfl
        intro i _
        exact Nat.sub_add_cancel (he r (Finset.mem_range.mp hr) i.val i.isLt)
      _ = A * W := by simp
  have HE' : (∑ i : Fin A, (W - e r i.val)) = A * W - (RationalSubstitution.Indexed.exponentVector A (e r)).degree := by omega
  rw [← Fin.prod_univ_eq_prod_range (fun i => num i ^ e r i * Polynomial.C q ^ (W - e r i)) A,
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, HE', ← map_pow]
  simp only [RationalSubstitution.Indexed.exponentVector, Finsupp.coe_equivFunOnFinite_symm]
  ring

end LeanCanny.Algebra.CommonDenominatorSpecialization
