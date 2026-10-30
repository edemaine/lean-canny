/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineHeightCoordinateTrailing
public import LeanCanny.Encoding.FlatAffineHeightOrdinals
public import LeanCanny.Geometry.AlgebraicBranchSign

/-! # Source-derived zero and sign tests on actual affine-height curves

Avoiding the native coordinate trailing product makes every coordinate's
zero test and both strict signs constant. Singular coordinate roots and
identically zero multiplier coordinates are retained.
-/

@[expose] public section
namespace LeanCanny.Geometry.FlatAffineHeightCoordinateSigns
open Set LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Connectivity
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

theorem tests_iff (F : Inputs) (height : (u : List Bool) → Fin (count F u)) (u : List Bool)
    {a b : ℝ} (curve : ℝ → Fin (count F u) → ℝ) (hc : ContinuousOn curve (Ioo a b))
    (hroot : ∀ t ∈ Ioo a b, PolynomialGridValues.value (IntegerGridArcs.realRows (FlatAffineHeightArcs.rows F height u)) (t, curve t) = 0)
    (havoid : ∀ t ∈ Ioo a b, SymbolicScaledSquarefree.scalarEvaluation t (FlatAffineHeightCoordinateTrailing.polynomial F height u) ≠ 0)
    (i : Fin (count F u)) (s t : Ioo a b) :
    (curve s.val i = 0 ↔ curve t.val i = 0) ∧
      (curve s.val i < 0 ↔ curve t.val i < 0) ∧ (0 < curve s.val i ↔ 0 < curve t.val i) := by
  let : PreconnectedSpace (Ioo a b) := Subtype.preconnectedSpace isPreconnected_Ioo
  let p := SquarefreeRootFamily.realPolynomial (FlatAffineHeightGrid.coordinate F height u i)
  let f : Ioo a b → ℝ := fun x => curve x.val i
  have HF : Continuous f := (continuous_apply i).comp (continuousOn_iff_continuous_domRestrict.mp hc)
  have HR (x : Ioo a b) : p.eval₂ (Polynomial.evalRingHom x.val) (f x) = 0 := by
    rw [SquarefreeRootFamily.eval_realPolynomial]
    exact FlatAffineHeightOrdinals.coordinate_root F height u x.val (curve x.val) (hroot x.val x.property) i
  have HT (x : Ioo a b) : p.trailingCoeff.eval x.val ≠ 0 := by
    rw [IntegerGridArcs.trailing_realPolynomial, Polynomial.eval_map]
    exact FlatAffineHeightCoordinateTrailing.avoids (SymbolicScaledSquarefree.scalarEvaluation x.val) F height u
      (havoid x.val x.property) i
  exact ⟨AlgebraicBranchZero.zero_iff p Subtype.val f continuous_subtype_val HF HR HT s t,
    AlgebraicBranchSign.sign_iff p Subtype.val f continuous_subtype_val HF HR HT s t⟩

end LeanCanny.Geometry.FlatAffineHeightCoordinateSigns
