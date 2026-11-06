/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicMarkedLanguage
/-! # Fresh own words retain native marked guards through initial-field equality -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomic
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Geometry
open FormulaSignSlotRadialExternalPrelude (number radius)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] LeanCanny.Connectivity.CanonicalAuxiliaryCandidateCover.equation
  LeanCanny.ETR.Term.finitePolynomial

private def InitialEquations (c : List Bool) (v : ℕ→ℝ) : Prop :=
  (∀i<number c+8,(FormulaSignSlotRadialProviderIntegerPlan.source.polynomial (pair c (BinaryNatCode.encode i))).eval₂
    (Int.castRingHom ℝ) (v i)=0) ∧
  (BoundedRegularSource.polynomial (LeanCanny.Connectivity.FormulaSignSlotRadialProviderMarkedGeometry.equation c)
    (LeanCanny.Connectivity.FormulaSignSlotRadialProviderMarkedGeometry.allowance c)
    (LeanCanny.Connectivity.FormulaSignSlotRadialProviderMarkedGeometry.allowance c) (radius c)).eval₂
      (Int.castRingHom ℝ) (fun i=>v i.val)=0 ∧
  (BoundedRegularSource.markPolynomial (LeanCanny.Connectivity.FormulaSignSlotRadialProviderMarkedGeometry.equation c)
    (radius c)).eval₂ (Int.castRingHom ℝ) (fun i=>v i.val)=0

private theorem initial_equations_congr (c : List Bool) (u v : ℕ→ℝ)
    (he : ∀i<number c+8,v i=u i) (h : InitialEquations c u) : InitialEquations c v := by
  have HE : (fun i : Fin (number c+4)=>v i.val)=(fun i : Fin (number c+4)=>u i.val) := by
    funext i
    exact he i.val (by have HI := i.isLt;omega)
  refine ⟨?_,?_,?_⟩
  · intro i hi
    rw [he i hi]
    exact h.1 i hi
  · exact (congrArg (fun x : Fin (number c+4)→ℝ=>
      (BoundedRegularSource.polynomial (LeanCanny.Connectivity.FormulaSignSlotRadialProviderMarkedGeometry.equation c)
        (LeanCanny.Connectivity.FormulaSignSlotRadialProviderMarkedGeometry.allowance c)
        (LeanCanny.Connectivity.FormulaSignSlotRadialProviderMarkedGeometry.allowance c) (radius c)).eval₂
        (Int.castRingHom ℝ) x) HE).trans h.2.1
  · exact (congrArg (fun x : Fin (number c+4)→ℝ=>
      (BoundedRegularSource.markPolynomial (LeanCanny.Connectivity.FormulaSignSlotRadialProviderMarkedGeometry.equation c)
        (radius c)).eval₂ (Int.castRingHom ℝ) x) HE).trans h.2.2

theorem marked_of_initial_fields (old : List Bool) (hv : Valid old) (q : List Bool) (hw : FullValid q)
    (hp : provider q=provider old)
    (hf : ∀i<number (provider old)+8,bankField (context q) (word q) hw i=field old hv i) : Marked.Holds q := by
  have HO : InitialEquations (provider old) (field old hv) :=
    ⟨MarkedPrelude.source_roots old hv,(MarkedPrelude.equations old hv).1,(MarkedPrelude.equations old hv).2⟩
  have H := initial_equations_congr (provider old) (field old hv) (MarkedLanguage.values q hw) hf HO
  have HN : InitialEquations (provider q) (MarkedLanguage.values q hw) := by
    rw [hp]
    exact H
  exact MarkedLanguage.holds_of_equations q hw HN.1 HN.2.1 HN.2.2

end LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomic
