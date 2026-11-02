/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.FermatLevelLift
public import LeanCanny.Algebra.FixedWidthPolynomial
/-! # Exact fixed-width coefficients after appending a free level coordinate -/
@[expose] public section
namespace LeanCanny.Algebra.FermatLevelCoefficient
open LeanCanny.Encoding FixedWidthPolynomial RationalSubstitution.Indexed MvPolynomial
open scoped Classical

theorem last_not_range (n : ℕ) : (Fin.last n) ∉ Set.range (Fin.castSucc : Fin n → Fin (n+1)) := by
  rintro ⟨i, hi⟩
  exact Fin.castSucc_ne_last i hi

theorem extend_exponent (n W k : ℕ) (hz : entry W k n = 0) :
    (exponentVector n (entry W k)).mapDomain Fin.castSucc = exponentVector (n+1) (entry W k) := by
  ext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · rw [Finsupp.mapDomain_of_notMem_range _ _ (last_not_range n)]
    exact hz.symm
  · rw [Finsupp.mapDomain_apply_of_injective (Fin.castSucc_injective n)]
    rfl

theorem rename_coefficient (n W k : ℕ) (p : MvPolynomial (Fin n) ℤ) :
    (rename Fin.castSucc p).coeff (exponentVector (n+1) (entry W k)) =
      if entry W k n = 0 then p.coeff (exponentVector n (entry W k)) else 0 := by
  by_cases hz : entry W k n = 0
  · rw [ite_eq_left hz, ← extend_exponent n W k hz, coeff_rename_mapDomain _ (Fin.castSucc_injective n)]
  · rw [ite_eq_right hz]
    apply coeff_rename_eq_zero
    intro e he
    have H := congrArg (fun d : Fin (n+1) →₀ ℕ => d (Fin.last n)) he
    rw [Finsupp.mapDomain_of_notMem_range _ _ (last_not_range n)] at H
    exact False.elim (hz H.symm)

def IsLast (n W k : ℕ) : Prop := entry W k n = 1 ∧ ∀ i < n, entry W k i = 0

theorem exponent_single_iff (n W k : ℕ) :
    exponentVector (n+1) (entry W k) = Finsupp.single (Fin.last n) 1 ↔ IsLast n W k := by
  constructor
  · intro he
    constructor
    · have H := congrArg (fun e : Fin (n+1) →₀ ℕ => e (Fin.last n)) he
      simpa [exponentVector] using H
    · intro i hi
      have H := congrArg (fun e : Fin (n+1) →₀ ℕ => e (Fin.castSucc ⟨i, hi⟩)) he
      rw [Finsupp.single_eq_of_ne (Fin.castSucc_ne_last ⟨i, hi⟩)] at H
      simpa [exponentVector] using H
  · rintro ⟨hl, ho⟩
    ext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa [exponentVector] using hl
    · simpa [exponentVector] using ho i.val i.isLt

theorem coefficient (n W k : ℕ) (p : MvPolynomial (Fin n) ℤ) (a : ℤ) :
    (rename Fin.castSucc p - C a * X (Fin.last n)).coeff (exponentVector (n+1) (entry W k)) =
      (if entry W k n = 0 then p.coeff (exponentVector n (entry W k)) else 0) -
      (if IsLast n W k then a else 0) := by
  rw [coeff_sub, rename_coefficient, C_mul_X_eq_monomial, coeff_monomial]
  by_cases h : IsLast n W k
  · have H : Finsupp.single (Fin.last n) 1 = exponentVector (n+1) (entry W k) :=
      ((exponent_single_iff n W k).mpr h).symm
    rw [ite_eq_left H, ite_eq_left h]
  · have H : Finsupp.single (Fin.last n) 1 ≠ exponentVector (n+1) (entry W k) := by
      intro he
      exact h ((exponent_single_iff n W k).mp he.symm)
    rw [ite_eq_right H, ite_eq_right h]

theorem source_coefficient {n : ℕ} (P : IntegralMixedHistory.SpatialSource n) (a : ℤ) (W k : ℕ) :
    (FermatLevelLift.source P a).low.coeff (exponentVector (n+2) (entry W k)) =
      (if entry W k (n+1) = 0 then P.low.coeff (exponentVector (n+1) (entry W k)) else 0) -
      (if IsLast (n+1) W k then a else 0) := coefficient (n+1) W k P.low a

end LeanCanny.Algebra.FermatLevelCoefficient
