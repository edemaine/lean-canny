/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineHeightValues
public import LeanCanny.Connectivity.IntegerGridArcs

/-! # Actual affine-height arcs using the computed native value polynomials

The original power-tower source supplies its coordinate grid and equation
value certificates. Their trailing factors and the squarefree coordinate
factors construct the exceptional polynomial used by the complete arcs.
Thus the value polynomials read natively and the geometric arc certificates
agree. Singular original roots and exceptional endpoint fibers are retained.
-/

@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineHeightArcs
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

noncomputable def rows (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (u : List Bool) :=
  AffineConstantParameterShift.system (FlatAffinePowerPositive.system F u)
    (fun i => if i = height u then Polynomial.X else 0)

noncomputable def certificate (F : Inputs) (height : (u : List Bool) → Fin (count F u))
    (u : List Bool) (i : Fin (count F u)) : Polynomial (Polynomial ℤ) :=
  (FlatAffineHeightValues.family F height (fun v => FlatAffineHeightGram.rawRow F v i.val)).affine.homogeneous.annihilator u

lemma test_eq (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (u : List Bool) (i : Fin (count F u)) :
    (FlatAffineHeightValues.family F height (fun v => FlatAffineHeightGram.rawRow F v i.val)).test u = rows F height u i := by
  change rows F height u (FlatAffineHeightGram.rawRow F u i.val) = _
  rw [FlatAffineHeightGram.rawRow_val]

lemma certificate_ne_zero (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (u : List Bool) (i : Fin (count F u)) : certificate F height u i ≠ 0 :=
  FlatAffineHeightValues.ne_zero F hcone height _ u

lemma value_relation (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (u : List Bool)
    {K : Type*} [Field K] (rho : Polynomial ℤ →+* K) (x : Fin (count F u) → K)
    (hx : ∀ j, (FlatAffineHeightGrid.coordinate F height u j).eval₂ rho (x j) = 0) (i : Fin (count F u)) :
    (certificate F height u i).eval₂ rho ((rows F height u i).eval₂ rho x) = 0 := by
  have h := FlatAffineHeightValues.eval_eq_zero F height (fun v => FlatAffineHeightGram.rawRow F v i.val) u rho x hx
  rwa [test_eq] at h

noncomputable def exceptional (F : Inputs) (height : (u : List Bool) → Fin (count F u))
    (u : List Bool) : Polynomial ℤ :=
  (∏ i, SymbolicScaledSquarefree.exceptional (FlatAffineHeightGrid.coordinate F height u i)) *
    ∏ i, (certificate F height u i).trailingCoeff

lemma exceptional_ne_zero (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (u : List Bool) : exceptional F height u ≠ 0 := by
  apply mul_ne_zero
  · apply Finset.prod_ne_zero_iff.mpr
    intro i _
    apply SymbolicScaledSquarefree.exceptional_ne_zero
    exact Geometry.AffineShiftCoordinates.coordinate_ne_zero _ _ _ (FlatAffinePowerPositive.degree_pos F u)
      (FlatAffinePowerPositive.noInfinity F hcone u) i
  · apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact Polynomial.trailingCoeff_ne_zero.mpr (certificate_ne_zero F hcone height u i)

lemma finite_exceptional (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (u : List Bool) :
    {t : ℝ | SymbolicScaledSquarefree.scalarEvaluation t (exceptional F height u) = 0}.Finite := by
  have hn : (exceptional F height u).map (Int.castRingHom ℝ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (Int.cast_injective (α := ℝ))).mpr (exceptional_ne_zero F hcone height u)
  simpa only [Polynomial.IsRoot, Polynomial.eval_map, SymbolicScaledSquarefree.scalarEvaluation,
    Polynomial.coe_eval₂RingHom] using Polynomial.finite_setOfPred_isRoot hn

/-- These arcs use the very value polynomials computed by the actual-source
native readers. Their exceptional polynomial is constructed, not supplied. -/
theorem anchored_arcs (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (u : List Bool)
    (a b : ℝ) (t₀ : Ioo a b)
    (havoid : ∀ t ∈ Ioo a b, SymbolicScaledSquarefree.scalarEvaluation t (exceptional F height u) ≠ 0) :
    Finite (PolynomialGridArcs.Fiber (IntegerGridArcs.realRows (rows F height u)) t₀.val) ∧
    ∃ curve : PolynomialGridArcs.Fiber (IntegerGridArcs.realRows (rows F height u)) t₀.val → ℝ → Fin (count F u) → ℝ,
      (∀ j, curve j t₀.val = j.val) ∧
      (∀ j, ContinuousOn (curve j) (Icc a b)) ∧
      (∀ j t, t ∈ Icc a b → PolynomialGridValues.value (IntegerGridArcs.realRows (rows F height u)) (t, curve j t) = 0) ∧
      (∀ t : Ioo a b, ∀ x, PolynomialGridValues.value (IntegerGridArcs.realRows (rows F height u)) (t.val, x) = 0 ↔
        ∃! j, curve j t.val = x) ∧
      ∀ j, FrontierCover.Accessible ((fun t => (t, curve j t)) '' Ioo a b) := by
  have hsplit (t : ℝ) (ht : t ∈ Ioo a b) :
      (∀ i, SymbolicScaledSquarefree.scalarEvaluation t
        (SymbolicScaledSquarefree.exceptional (FlatAffineHeightGrid.coordinate F height u i)) ≠ 0) ∧
      ∀ i, SymbolicScaledSquarefree.scalarEvaluation t (certificate F height u i).trailingCoeff ≠ 0 := by
    have H := havoid t ht
    simpa only [exceptional, map_mul, map_prod, mul_ne_zero_iff, Finset.prod_ne_zero_iff,
      Finset.mem_univ, forall_const] using H
  apply PolynomialGridArcs.anchored_arcs_of_annihilators (FlatAffineHeightGrid.coordinate F height u)
    (fun i => Geometry.AffineShiftCoordinates.coordinate_ne_zero _ _ _ (FlatAffinePowerPositive.degree_pos F u)
      (FlatAffinePowerPositive.noInfinity F hcone u) i) (IntegerGridArcs.realRows (rows F height u))
    (fun i => SquarefreeRootFamily.realPolynomial (certificate F height u i)) ?_ ?_ ?_ a b t₀
    (fun t ht => (hsplit t ht).1) ?_
  · intro t x hx i
    rw [SquarefreeRootFamily.eval_realPolynomial, IntegerGridArcs.real_value]
    exact value_relation F height u _ x hx i
  · exact Geometry.AffineShiftCoordinates.proper _ _ _ (FlatAffinePowerPositive.degree_pos F u)
      (FlatAffinePowerPositive.noInfinity F hcone u)
  · exact Geometry.AffineShiftCoordinates.capture _ _ _ (FlatAffinePowerPositive.polynomial_degree F u)
  · intro i t ht
    rw [IntegerGridArcs.trailing_realPolynomial, Polynomial.eval_map]
    exact (hsplit t ht).2 i

end LeanCanny.Connectivity.FlatAffineHeightArcs
