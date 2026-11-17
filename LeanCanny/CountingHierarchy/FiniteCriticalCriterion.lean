/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.FiniteCriticalData

/-! # The complete finite determinant criterion for nonnegative real feasibility

Every polynomial, bound, label length and shift range is constructed from the
source integer polynomial's arity, degree and coefficient-mass bound.
Counting-hierarchy evaluator certificates for this criterion are separate.
-/

public section

namespace LeanCanny.CountingHierarchy

open Polynomial MvPolynomial PurePowerResidue LeanCanny.Algebra

@[expose] noncomputable def finiteCriticalDeterminant {n : ℕ} (d b : ℕ)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1)
    (L : List (Fin ((d + 1) ^ n) × SignType)) (e : ℕ) : ℤ :=
  (multiplicationMatrix (by omega : 1 ≤ d + 1) (finiteCriticalRelations d b F)
    (fun i => (finiteCriticalRelations_degree d b F hF i).trans_lt (Nat.lt_succ_self d))
    (Polynomial.aeval (finiteCriticalObjective d b F)
      (shiftedIntegerLabel ((d + 1) ^ n) e
        (sparseIntegerRootLabel (finiteCriticalPolynomial d b F hF)
          (Polynomial.C (criticalIntegerCutoff n d b) - Polynomial.X)
          (criticalRootLabelLength n d) (criticalLabelInputMassExponent n d b) L)))).det

/-- A zero of the nonnegative source polynomial exists exactly when one
 short label and one bounded integer shift give a negative integer determinant. -/
theorem real_zero_iff_negative_finiteCriticalDeterminant {n : ℕ}
    (d : ℕ) (hd : 1 ≤ d) (he : Even (d + 2)) (b : ℕ)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1)
    (hM : MvMass.mass F ≤ 2 ^ b)
    (hFn : ∀ x : Fin n → ℝ, 0 ≤ MvPolynomial.eval x (F.map (Int.castRingHom ℝ))) :
    (∃ x : Fin n → ℝ, MvPolynomial.eval x (F.map (Int.castRingHom ℝ)) = 0) ↔
      ∃ L : List (Fin ((d + 1) ^ n) × SignType), L.length ≤ criticalRootLabelLength n d ∧
        ∃ e : ℕ, e ≤ (d + 1) ^ n ∧ finiteCriticalDeterminant d b F hF L e < 0 := by
  have hgeom := real_zero_iff_source_bounded_critical_root d hd he b F hF hM hFn
  have hgeom' : (∃ x : Fin n → ℝ, MvPolynomial.eval x (F.map (Int.castRingHom ℝ)) = 0) ↔
      ∃ x : ℝ, (finiteCriticalPolynomial d b F hF).eval₂ (Int.castRingHom ℝ) x = 0 ∧
        x < (criticalIntegerCutoff n d b : ℝ) := by
    simpa only [finiteCriticalPolynomial, criticalSpecializationExponent, criticalIntegerCutoff,
      Polynomial.IsRoot, Polynomial.eval_map, Int.cast_pow, Int.cast_ofNat, and_comm] using hgeom
  have hnorm := root_below_iff_negative_quotient_label d hd (finiteCriticalRelations d b F)
    (finiteCriticalRelations_degree d b F hF) (finiteCriticalObjective d b F)
    (finiteCriticalPolynomial d b F hF) (finiteCriticalPolynomial_eq_charpoly d hd b F hF)
    (source_bounded_criticalValue_separable_complex d hd b F hF hM)
    (criticalRootLabelLength n d) (criticalLabelInputMassExponent n d b)
    (criticalRootLabelLength_suffices n d) (criticalIntegerCutoff n d b)
    (finiteCriticalPolynomial_mass_le d hd b F hF hM) (criticalCutoff_test_mass_le n d b)
  exact hgeom'.trans hnorm

end LeanCanny.CountingHierarchy
