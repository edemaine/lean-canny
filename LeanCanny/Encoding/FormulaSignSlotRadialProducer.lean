/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialEquation
public import LeanCanny.Encoding.BoundedFullCriticalSamples
public import LeanCanny.Encoding.BoundedFullCoefficient
/-! # The actual regularized producer for one original radial graph

The packet contains the original selected-sign input and a binary radius.
All source metadata and scope are proved here. The pure-power degree is
chosen once from the original equation syntax and retained by later frames.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProducer
open ETR LeanCanny.Computation LeanCanny.Connectivity LeanCanny.Geometry LeanCanny.Algebra
open LeanCanny.ETR.ComplexCircuit
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] pair Input.field ClosedFormulaGateMetadata.dimension ClosedFormulaGateMetadata.count
  ClosedFormulaGateMetadata.atom ClosedFormulaGateMetadata.kind FormulaSignSlotMargin.prepared
  FormulaSignSlotMargin.initialDimension FormulaSignSlotMargin.initialPolynomial FormulaSignSlotSource.dimension

def root (q : List Bool) := pairFst q
def radius (q : List Bool) := Nat.fromBitsLE (pairSnd q)
noncomputable def readers : BoundedFullWriter.Readers where
  source q := (FormulaSignSlotRadialEquation.equation (root q)).toData.toBits
  dim q := FormulaSignSlotRadialEquation.dimension (root q)
  radius := radius

theorem access : readers.PolyTime where
  source := mem_FP_comp (f:=root) (g:=fun c => (FormulaSignSlotRadialEquation.equation c).toData.toBits)
    pairFst_mem_FP FormulaSignSlotRadialEquation.equation_FP
  dim := FormulaSignSlotRadialEquation.dimension_unary.comp pairFst_mem_FP
  radius := BinaryFn.fromBits pairSnd_mem_FP

theorem source_scope (q : List Bool) : (TermView.term (readers.source q)).arity≤readers.dim q := by
  change (TermView.term (FormulaSignSlotRadialEquation.equation (root q)).toData.toBits).arity≤_
  rw [TermView.term_toBits]
  exact FormulaSignSlotRadialEquation.scope (root q)

theorem original_eq (q : List Bool) : BoundedFullWriter.original readers q=
    FormulaSignSlotRadialEquation.polynomial (root q) := by
  change (TermView.term (FormulaSignSlotRadialEquation.equation (root q)).toData.toBits).finitePolynomial _=_
  rw [TermView.term_toBits]
  rfl

theorem size_eq (q : List Bool) : BoundedFullWriter.size readers q=FormulaSignSlotRadialEquation.budget (root q) := by
  change (TermView.term (FormulaSignSlotRadialEquation.equation (root q)).toData.toBits).toData.size=_
  rw [TermView.term_toBits]
  rfl

theorem degree_binary : BinaryFn (BoundedFullWriter.degree readers) := BoundedFullWriter.degree_binary access

theorem source_identity (q : List Bool) :
    Differential.symbolicRun (fun i => (MvPolynomial.X i : MvPolynomial ℕ ℤ))
      (BoundedFullWriter.start readers q) (BoundedFullWriter.program readers q) (BoundedFullWriter.output readers q)=
      MvPolynomial.rename Fin.val (BoundedFullCriticalSamples.polynomial readers q) :=
  BoundedFullGeometry.source_identity readers q (source_scope q)

theorem source_regular (q : List Bool) (x : Fin (readers.dim q+4) → ℝ)
    (hx : (BoundedFullCriticalSamples.realPolynomial readers q).eval x=0) :
    Function.Surjective (fderiv ℝ (fun y => (BoundedFullCriticalSamples.realPolynomial readers q).eval y) x) :=
  BoundedFullCriticalSamples.source_regular readers q x hx

theorem source_proper (q : List Bool) :
    IsProperMap (fun x => (BoundedFullCriticalSamples.realPolynomial readers q).eval x) :=
  BoundedFullCriticalSamples.source_proper readers q

theorem finite_components (q : List Bool) :
    Finite (ConnectedComponents (BoundedFullCriticalSamples.Source readers q)) ∧
      Nat.card (ConnectedComponents (BoundedFullCriticalSamples.Source readers q))≤
        2^BoundedFullCriticalSamples.labelWidth readers q :=
  BoundedFullCriticalSamples.finite_components readers q

theorem exists_joined_sample (q : List Bool) (x : Fin (readers.dim q+4) → ℝ)
    (hx : (BoundedFullCriticalSamples.realPolynomial readers q).eval x=0) :
    ∃ y : BoundedFullCriticalSamples.Samples readers q,
      JoinedIn {z | (BoundedFullCriticalSamples.realPolynomial readers q).eval z=0} x y.val :=
  BoundedFullCriticalSamples.exists_joined_sample readers q x hx

theorem coefficient_evaluator {W : List Bool → ℕ} {target modulus : List Bool → List Bool}
    (hW : UnaryFn W) (ht : target∈FP) (hm : modulus∈FP) :
    SpaceFunction (BoundedFullCoefficient.value readers W target modulus) :=
  BoundedFullCoefficient.evaluator access hW ht hm source_scope

end LeanCanny.Encoding.FormulaSignSlotRadialProducer
