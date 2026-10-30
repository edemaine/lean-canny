/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.RootCurveOrder
public import LeanCanny.Geometry.SymbolicUnivariateRootFamily
public import LeanCanny.Geometry.PolynomialCoordinateProper
public import LeanCanny.Geometry.RootSlabEquivalence
public import LeanCanny.Geometry.LocalProperRootBranches

/-! # Coordinate root order from the explicit squarefree exceptional factor

Away from the constructed exceptional polynomial, original scalar roots form
a proper covering after squarefree preprocessing. Thus any continuous grid
curves retain their coordinate equality and order. Properness of the scalar
projection is proved from the original leading coefficient on the interval;
no global properness or endpoint regularity hypothesis is needed.
-/

@[expose] public section
namespace LeanCanny.Geometry.SymbolicRootCurveOrder
open Set LeanCanny.Algebra
open SymbolicScaledSquarefree (Coefficient scalarEvaluation exceptional)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem covering (p : Polynomial Coefficient) (a b : ℝ)
    (havoid : ∀ t ∈ Ioo a b, scalarEvaluation t (exceptional p) ≠ 0) :
    IsCoveringMap (RootBranches.projection
      (SymbolicUnivariateRootFamily.value (SymbolicScaledSquarefree.polynomial p)) a b) := by
  have hrows : UnivariateRootFamily.rows (SymbolicUnivariateRootFamily.realPolynomial p) =
      UnivariateRootFamily.diagonal (fun _ : Fin 1 => SymbolicUnivariateRootFamily.realPolynomial p) := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  have hp : IsProperMap (RootBranches.projection (SymbolicUnivariateRootFamily.value p) a b) := by
    change IsProperMap ((Ioo a b).restrictPreimage (RootProjection.projection
      (PolynomialRootFamily.value (UnivariateRootFamily.rows (SymbolicUnivariateRootFamily.realPolynomial p)))))
    rw [hrows]
    apply PolynomialCoordinateProper.proper_restriction
    intro _ t ht
    rw [SymbolicUnivariateRootFamily.realPolynomial, Polynomial.leadingCoeff_map_of_injective
      (Polynomial.map_injective _ (Int.cast_injective (α := ℝ)))]
    change (p.leadingCoeff.map (Int.castRingHom ℝ)).eval t ≠ 0
    rw [Polynomial.eval_map]
    exact (SymbolicScaledSquarefree.exceptional_conditions (scalarEvaluation t) p (havoid t ht)).1
  have haux := RootSlabEquivalence.proper_restriction (SymbolicUnivariateRootFamily.value p)
    (SymbolicUnivariateRootFamily.value (SymbolicScaledSquarefree.polynomial p)) (Ioo a b)
    (fun t ht x => SymbolicUnivariateRootFamily.roots_away p t x (havoid t ht)) hp
  apply LocalProperRootBranches.covering _ a b haux
  · intro z _
    exact (SymbolicUnivariateRootFamily.contDiff_value _ 1).contDiffAt
  · intro z hz
    exact SymbolicUnivariateRootFamily.regular_away p z.val.1 z.val.2 (havoid _ hz) z.property

theorem coordinate_comparison_iff {ι : Type*} (p : Polynomial Coefficient) {a b : ℝ}
    (havoid : ∀ t ∈ Ioo a b, scalarEvaluation t (exceptional p) ≠ 0)
    (f g : C(Ioo a b, ι → ℝ)) (i : ι)
    (hf : ∀ t, p.eval₂ (scalarEvaluation t.val) (f t i) = 0)
    (hg : ∀ t, p.eval₂ (scalarEvaluation t.val) (g t i) = 0) (s t : Ioo a b) :
    (f s i = g s i ↔ f t i = g t i) ∧ (f s i < g s i ↔ f t i < g t i) := by
  apply RootBranches.coordinate_comparison_iff
    (SymbolicUnivariateRootFamily.value (SymbolicScaledSquarefree.polynomial p))
    (covering p a b havoid) f g i _ _ s t
  · intro u
    apply (SymbolicUnivariateRootFamily.roots_away p u.val _ (havoid _ u.property)).mp
    exact (SymbolicUnivariateRootFamily.value_zero_iff p u.val _).mpr (hf u)
  · intro u
    apply (SymbolicUnivariateRootFamily.roots_away p u.val _ (havoid _ u.property)).mp
    exact (SymbolicUnivariateRootFamily.value_zero_iff p u.val _).mpr (hg u)

end LeanCanny.Geometry.SymbolicRootCurveOrder
