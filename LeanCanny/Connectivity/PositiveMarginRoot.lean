/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.PositiveMarginValues
public import LeanCanny.Connectivity.PositiveMarginSourceSplitting
/-! # Literal root reads in the unique margin graph -/
@[expose] public section
namespace LeanCanny.Connectivity.PositiveMarginValues
open ETR LeanCanny.Encoding LeanCanny.Geometry MonotoneGateSource

theorem root_full (F : Family) (c : List Bool) (x : Fin (F.dimension c) → ℝ) (hc : 0<F.count c) :
    (PositiveMarginSource.root F c).eval (Formula.extend (full F c x))=
      value F c x ⟨F.count c-1,by omega⟩ := by
  have H0 : F.count c≠0 := Nat.ne_zero_of_lt hc
  have HI : F.dimension c+(F.count c-1)<F.dimension c+F.count c := by omega
  simp only [PositiveMarginSource.root,ite_eq_right H0,Term.eval,Formula.extend,dite_eq_left HI,value]

theorem rootOn_continuous (F : Family) (c : List Bool) : Continuous (PositiveMarginGraph.rootOn F c) :=
  (FormulaStrictWitness.continuous_eval _ _).comp continuous_subtype_val

end LeanCanny.Connectivity.PositiveMarginValues
