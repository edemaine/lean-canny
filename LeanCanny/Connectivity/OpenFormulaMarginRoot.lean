/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.OpenFormulaMarginTruth
public import LeanCanny.Connectivity.PositiveMarginRoot
/-! # The actual native reciprocal root reads the original formula's nonnegative margin -/
@[expose] public section
namespace LeanCanny.Connectivity.OpenFormulaMarginValues
open ETR Set LeanCanny.Encoding LeanCanny.Geometry
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] pair Input.field FormulaView.normalize
  ClosedFormulaGateMetadata.dimension ClosedFormulaGateMetadata.count ClosedFormulaGateMetadata.query
  OpenFormulaGateMetadata.atom OpenFormulaGateMetadata.kind PositiveMarginValues.value PositiveMarginValues.full

 theorem root_formula {p : Formula} (hp : OpenFormulaMargin.Open p) (c : List Bool)
    (hc : FormulaView.normalize (Input.field 2 c)=p.encode) (hs : p.arity≤ClosedFormulaGateMetadata.dimension c)
    (x : Fin (ClosedFormulaGateMetadata.dimension c) → ℝ) :
    (PositiveMarginSource.root F c).eval (Formula.extend (PositiveMarginValues.full F c x))=
      OpenFormulaMargin.margin (Formula.extend x) p := by
  have HM : 0<ClosedFormulaGateMetadata.count c := by
    unfold ClosedFormulaGateMetadata.count
    rw [hc]
    simp [Formula.encode]
  have HMF : 0<F.count c := HM
  have HI : ClosedFormulaGateMetadata.count c-1<ClosedFormulaGateMetadata.count c := by omega
  rw [PositiveMarginValues.root_full F c x HM]
  have HE : PositiveMarginValues.value F c x ⟨F.count c-1,by omega⟩=entry c x (ClosedFormulaGateMetadata.count c-1) := by
    exact (entry_valid c x _ HI).symm
  rw [HE]
  have HV:=wire_formula hp c [] [] x (by simpa only [List.nil_append,List.append_nil] using hc) hs
  simpa only [FormulaBooleanCircuitSource.wire,ClosedFormulaGateMetadata.count,List.length_nil,Nat.sub_zero] using HV

theorem root_on_formula {p : Formula} (hp : OpenFormulaMargin.Open p) (c : List Bool)
    (hc : FormulaView.normalize (Input.field 2 c)=p.encode) (hs : p.arity≤ClosedFormulaGateMetadata.dimension c)
    (y : PositiveMarginGraph.Sol F c) :
    PositiveMarginGraph.rootOn F c y=OpenFormulaMargin.margin
      (Formula.extend (TriangularContinuousGraph.projection (F.dimension c) (F.count c) y.val)) p := by
  let x:=TriangularContinuousGraph.projection (F.dimension c) (F.count c) y.val
  have HU:=TriangularContinuousGraph.unique (F.dimension c) (PositiveMarginGraph.gate F c) (F.count c) y
  have HE : y.val=PositiveMarginValues.full F c x := by
    simpa only [PositiveMarginValues.full,x] using HU.symm
  calc
    PositiveMarginGraph.rootOn F c y=(PositiveMarginSource.root F c).eval (Formula.extend (PositiveMarginValues.full F c x)) :=
      congrArg (fun v => (PositiveMarginSource.root F c).eval (Formula.extend v)) HE
    _=OpenFormulaMargin.margin (Formula.extend x) p := root_formula hp c hc hs x

theorem root_nonneg {p : Formula} (hp : OpenFormulaMargin.Open p) (c : List Bool)
    (hc : FormulaView.normalize (Input.field 2 c)=p.encode) (hs : p.arity≤ClosedFormulaGateMetadata.dimension c)
    (y : PositiveMarginGraph.Sol F c) : 0≤PositiveMarginGraph.rootOn F c y := by
  rw [root_on_formula hp c hc hs]
  exact OpenFormulaMargin.nonneg hp _

end LeanCanny.Connectivity.OpenFormulaMarginValues
