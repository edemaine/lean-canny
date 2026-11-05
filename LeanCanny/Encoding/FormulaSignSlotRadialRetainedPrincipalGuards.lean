/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialRetainedPrincipalTest
public import LeanCanny.Encoding.FormulaSignSlotRadialRetainedCenterGuards
/-! # Native finite principal guards retaining one full word and one center -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialRetainedPrincipalGuards
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Connectivity LeanCanny.ETR
open LeanCanny.Encoding.Brackets
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotRadialRetainedPrincipalTest.value

def slot := FormulaSignSlotRadialRetainedPrincipalTest.slot
theorem slot_FP (i : ℕ) : slot i ∈ FP := FormulaSignSlotRadialRetainedPrincipalTest.slot_FP i
def context (q : List Bool) := pairFst (pairFst q)
def degree (q : List Bool) := Nat.fromBitsLE (slot 1 q)
def order (q : List Bool) := Nat.fromBitsLE (slot 2 q)
theorem context_FP : context ∈ FP := by polytime [context]
theorem degree_binary : BinaryFn degree := BinaryFn.fromBits (slot_FP 1)
theorem order_binary : BinaryFn order := BinaryFn.fromBits (slot_FP 2)
def familyContext (radial : List Bool → List Bool) (q : List Bool) :=
  pair (radial (context q)) (pair (slot 0 q) (slot 1 q))
theorem familyContext_FP (radial : List Bool → List Bool) (hr : radial ∈ FP) : familyContext radial ∈ FP :=
  mem_FP_pair (mem_FP_comp context_FP hr) (mem_FP_pair (slot_FP 0) (slot_FP 1))
noncomputable def bound (radial : List Bool → List Bool) (q : List Bool) :=
  FormulaSignSlotRadialCenterPrincipalFamily.degreeBound (familyContext radial q)
theorem bound_binary (radial : List Bool → List Bool) (hr : radial ∈ FP) : BinaryFn (bound radial) :=
  FormulaSignSlotRadialCenterPrincipalFamily.degreeBound_binary.comp (familyContext_FP radial hr)
def centerQuery (q : List Bool) := pair (pairFst q) (pair (slot 0 q) (slot 1 q))
theorem centerQuery_FP : centerQuery ∈ FP := mem_FP_pair pairFst_mem_FP (mem_FP_pair (slot_FP 0) (slot_FP 1))
def base (z : List Bool) := pairFst (pairFst z)
theorem base_FP : base ∈ FP := by polytime [base]
def radiusQuery (z : List Bool) := pair (pairFst (base z))
  (WordList.encode [BinaryNat.normalize (slot 0 (base z)), BinaryNat.normalize (slot 1 (base z)),
    BinaryNat.normalize (pairSnd (pairFst z)), BinaryNat.normalize (pairSnd z)])
theorem radiusQuery_FP : radiusQuery ∈ FP := by
  unfold radiusQuery WordList.encode
  exact mem_FP_pair (mem_FP_comp base_FP pairFst_mem_FP)
    (mem_FP_pair (mem_FP_comp (mem_FP_comp base_FP (slot_FP 0)) BinaryNat.normalize_mem_FP)
      (mem_FP_pair (mem_FP_comp (mem_FP_comp base_FP (slot_FP 1)) BinaryNat.normalize_mem_FP)
        (mem_FP_pair (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) BinaryNat.normalize_mem_FP)
          (mem_FP_pair (mem_FP_comp pairSnd_mem_FP BinaryNat.normalize_mem_FP) (constFn_mem_FP [])))))
def chosen (q : List Bool) := pair q (BinaryNatCode.encode (order q))
theorem chosen_FP : chosen ∈ FP := mem_FP_pair id_mem_FP order_binary.bits_mem_FP

variable {n : List Bool → ℕ} {t : List Bool → Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R : List Bool → ℕ} (hR : BinaryFn R) (outer : Bool) (radial refs : List Bool → List Bool)

noncomputable def RadiusZero (q : List Bool) : Prop := ∀ r < bound radial (pairFst q) + 1,
  FormulaSignSlotRadialRetainedPrincipalTest.value hn ht ha hR outer radial refs
    (radiusQuery (pair q (BinaryNatCode.encode r))) = InfinitesimalSign.encode 0
noncomputable def marker (q : List Bool) := [decide (RadiusZero hn ht ha hR outer radial refs q)]

theorem marker_evaluator (hr : radial ∈ FP) (hf : refs ∈ FP) : SpaceFunction (marker hn ht ha hR outer radial refs) := by
  have ES := (FormulaSignSlotRadialRetainedPrincipalTest.evaluator hn ht ha hR outer radial refs hr hf).precompose
    radiusQuery radiusQuery_FP
  have EZ := ES.postcompose _ (stringEq_fppred id_mem_FP (constFn_mem_FP (InfinitesimalSign.encode 0))).flag_mem_FP
  have H : BinaryFn (fun q => bound radial (pairFst q)) := (bound_binary radial hr).comp pairFst_mem_FP
  exact (EZ.forall_binary (H.add (BinaryFn.const 1))).congr (funext fun q => by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [RadiusZero, Function.comp_apply, id_eq, List.cons.injEq, and_true, decide_eq_true_eq])

noncomputable def Lower (q : List Bool) : Prop := ∀ j < order q,
  RadiusZero hn ht ha hR outer radial refs (pair q (BinaryNatCode.encode j))
noncomputable def Guards (q : List Bool) : Prop :=
  FormulaSignSlotRadialRetainedCenterGuards.Guards hn ht ha hR outer radial refs (centerQuery q) ∧
    if degree q = 0 then order q = 0 else order q < degree q ∧
      Lower hn ht ha hR outer radial refs q ∧ ¬RadiusZero hn ht ha hR outer radial refs (chosen q)

theorem evaluator (hr : radial ∈ FP) (hf : refs ∈ FP) :
    SpaceFunction (fun q => [decide (Guards hn ht ha hR outer radial refs q)]) := by
  have EM := marker_evaluator hn ht ha hR outer radial refs hr hf
  have EL : SpaceFunction (fun q => [decide (Lower hn ht ha hR outer radial refs q)]) :=
    (EM.forall_binary order_binary).congr (funext fun q => by
      apply congrArg List.singleton
      apply Bool.eq_iff_iff.mpr
      simp only [Lower, marker, List.cons.injEq, and_true, decide_eq_true_eq])
  have EC := (EM.precompose chosen chosen_FP).postcompose _
    (stringEq_fppred id_mem_FP (constFn_mem_FP [true])).not.flag_mem_FP
  have EC' : SpaceFunction (fun q => [decide (¬RadiusZero hn ht ha hR outer radial refs (chosen q))]) :=
    EC.congr (funext fun q => by
      apply congrArg List.singleton
      apply Bool.eq_iff_iff.mpr
      simp only [marker, Function.comp_apply, id_eq, List.cons.injEq, and_true, decide_eq_true_eq])
  have EK := SpaceFunction.ofFP _ ((order_binary.lt degree_binary).flag_mem_FP)
  have EB : SpaceFunction (fun q => [decide (order q < degree q ∧ Lower hn ht ha hR outer radial refs q ∧
      ¬RadiusZero hn ht ha hR outer radial refs (chosen q))]) :=
    (EK.andFlags (EL.andFlags EC')).congr (funext fun q => by
      apply congrArg List.singleton
      apply Bool.eq_iff_iff.mpr
      simp only [List.cons.injEq, and_true, decide_eq_true_eq])
  have E0 := SpaceFunction.ofFP _ ((order_binary.eq (BinaryFn.const 0)).flag_mem_FP)
  have EP := SpaceFunction.branch (fun q => decide (degree q = 0))
    (degree_binary.eq (BinaryFn.const 0)).flag_mem_FP E0 EB
  have EO := (FormulaSignSlotRadialRetainedCenterGuards.evaluator hn ht ha hR outer radial refs hr hf).precompose
    centerQuery centerQuery_FP
  exact (EO.andFlags EP).congr (funext fun q => by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [Guards, Function.comp_apply, List.cons.injEq, and_true, decide_eq_true_eq]
    split_ifs <;> simp only [List.cons.injEq, and_true, decide_eq_true_eq])

end LeanCanny.Encoding.FormulaSignSlotRadialRetainedPrincipalGuards
