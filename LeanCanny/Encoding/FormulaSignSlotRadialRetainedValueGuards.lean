/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialRetainedValueCoordinateGuards
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterValueTrailingSelection
public import LeanCanny.Encoding.FormulaSignSlotRadialRetainedValueTest
/-! # Native same-bank guards select the actual value-certificate cut -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialRetainedValueGuards
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Connectivity LeanCanny.ETR
open LeanCanny.Encoding.Brackets
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotRadialRetainedValueTest.value

def context (q : List Bool) := pairFst (pairFst q)
def selected (q : List Bool) := Nat.fromBitsLE (pairSnd q)
noncomputable def bound (radial : List Bool → List Bool) (q : List Bool) :=
  FormulaSignSlotRadialCenterValueTrailingSelection.bound (radial (context q))
noncomputable def radiusBound (radial : List Bool → List Bool) (q : List Bool) :=
  FormulaSignSlotRadialCenterValuePacking.degree (radial (context q))
def radiusQuery (q : List Bool) := pair (pairFst (pairFst q))
  (WordList.encode [pairSnd (pairFst q), pairSnd q])
def lowerQuery (q : List Bool) := pair (pairFst (pairFst q)) (pairSnd q)
def query (c w : List Bool) (ell : ℕ) := pair (pair c w) (BinaryNatCode.encode ell)
theorem context_FP : context ∈ FP := by polytime [context]
theorem selected_binary : BinaryFn selected := BinaryFn.fromBits pairSnd_mem_FP
theorem bound_binary (radial : List Bool → List Bool) (hr : radial ∈ FP) : BinaryFn (bound radial) :=
  FormulaSignSlotRadialCenterValueTrailingSelection.bound_binary.comp (mem_FP_comp context_FP hr)
theorem radiusBound_binary (radial : List Bool → List Bool) (hr : radial ∈ FP) : BinaryFn (radiusBound radial) :=
  FormulaSignSlotRadialCenterValuePacking.degree_binary.comp (mem_FP_comp context_FP hr)
theorem radiusQuery_FP : radiusQuery ∈ FP := by
  unfold radiusQuery WordList.encode
  exact mem_FP_pair (by polytime) (mem_FP_pair (by polytime) (mem_FP_pair pairSnd_mem_FP (constFn_mem_FP [])))
theorem lowerQuery_FP : lowerQuery ∈ FP := by polytime [lowerQuery]

variable {n : List Bool → ℕ} {t : List Bool → Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R : List Bool → ℕ} (hR : BinaryFn R) (outer : Bool) (radial refs : List Bool → List Bool)
noncomputable def RadiusZero (q : List Bool) : Prop := ∀ r < radiusBound radial q + 1,
  FormulaSignSlotRadialRetainedValueTest.value hn ht ha hR outer radial refs
    (radiusQuery (pair q (BinaryNatCode.encode r))) = InfinitesimalSign.encode 0
noncomputable def LowerZero (q : List Bool) : Prop := ∀ j < selected q,
  RadiusZero hn ht ha hR outer radial refs (lowerQuery (pair q (BinaryNatCode.encode j)))
noncomputable def Guards (q : List Bool) : Prop :=
  FormulaSignSlotRadialRetainedValueCoordinateGuards.Guards hn ht ha hR outer radial refs (pairFst q) ∧
  selected q ≤ bound radial q ∧ LowerZero hn ht ha hR outer radial refs q ∧
    ¬RadiusZero hn ht ha hR outer radial refs q
attribute [local irreducible] RadiusZero LowerZero Guards

theorem radius_evaluator (hr : radial ∈ FP) (hf : refs ∈ FP) :
    SpaceFunction (fun q => [decide (RadiusZero hn ht ha hR outer radial refs q)]) := by
  have ES := (FormulaSignSlotRadialRetainedValueTest.evaluator hn ht ha hR outer radial refs hr hf).precompose
    radiusQuery radiusQuery_FP
  have EZ := ES.postcompose (fun z => [decide (z = InfinitesimalSign.encode 0)])
    (stringEq_fppred id_mem_FP (constFn_mem_FP _)).flag_mem_FP
  have EA := EZ.forall_binary ((radiusBound_binary radial hr).add (BinaryFn.const 1))
  exact EA.congr (funext fun q => by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [RadiusZero, Function.comp_apply, List.cons.injEq, and_true, decide_eq_true_eq])

theorem evaluator (hr : radial ∈ FP) (hf : refs ∈ FP) :
    SpaceFunction (fun q => [decide (Guards hn ht ha hR outer radial refs q)]) := by
  have ER := radius_evaluator hn ht ha hR outer radial refs hr hf
  have EL := (ER.precompose lowerQuery lowerQuery_FP).forall_binary selected_binary
  have EC := ER.postcompose (fun z => [decide (z ≠ [true])])
    (stringEq_fppred id_mem_FP (constFn_mem_FP [true])).not.flag_mem_FP
  have EG := (FormulaSignSlotRadialRetainedValueCoordinateGuards.evaluator hn ht ha hR outer radial refs hr hf).precompose
    pairFst pairFst_mem_FP
  have EB := SpaceFunction.ofFP _ (selected_binary.le (bound_binary radial hr)).flag_mem_FP
  refine (EG.andFlags (EB.andFlags (EL.andFlags EC))).congr (funext fun q => ?_)
  apply congrArg List.singleton
  apply Bool.eq_iff_iff.mpr
  simp only [Guards, LowerZero, Function.comp_apply, List.cons.injEq, and_true, decide_eq_true_eq]
  exact and_congr_right' (and_congr_right' (and_congr_right' (not_congr
    (by simp only [List.cons.injEq, and_true, decide_eq_true_eq]))))

private theorem radius_query_packet (c w : List Bool) (j r : ℕ) :
    radiusQuery (pair (query c w j) (BinaryNatCode.encode r)) =
      pair (pair c w) (FormulaSignSlotRadialRetainedValueTest.indices j r) := by
  simp only [radiusQuery, query, pairFst_pair, pairSnd_pair, FormulaSignSlotRadialRetainedValueTest.indices]
private theorem zero_packet (c w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR outer) c w)
    (j r : ℕ) : FormulaSignSlotRadialRetainedValueTest.value hn ht ha hR outer radial refs
      (pair (pair c w) (FormulaSignSlotRadialRetainedValueTest.indices j r)) = InfinitesimalSign.encode 0 ↔
        FormulaSignSlotRadialCenterValueTrailingSelection.Zero (radial c)
          (fun i => FormulaSignSlotRadialRetainedValueTest.center hn ht ha hR outer refs c w hv i.val) j r := by
  rw [FormulaSignSlotRadialRetainedValueTest.packet hn ht ha hR outer radial refs c w _ hv]
  simp only [FormulaSignSlotRadialRetainedValueTest.indices, WordList.get_encode,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, MacaulayBits.fromBits_encode]
  exact (SquareSampleTestSign.encode_eq_iff _ _).trans sign_eq_zero_iff
private theorem radius_packet (c w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR outer) c w)
    (j : ℕ) : RadiusZero hn ht ha hR outer radial refs (query c w j) ↔
      ∀ r < FormulaSignSlotRadialCenterValuePacking.degree (radial c) + 1,
        FormulaSignSlotRadialCenterValueTrailingSelection.Zero (radial c)
          (fun i => FormulaSignSlotRadialRetainedValueTest.center hn ht ha hR outer refs c w hv i.val) j r := by
  rw [RadiusZero]
  simp_rw [radius_query_packet, zero_packet hn ht ha hR outer radial refs c w hv]
  simp only [radiusBound, context, query, pairFst_pair]

private theorem radius_at (c w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR outer) c w)
    (j : ℕ) : RadiusZero hn ht ha hR outer radial refs (pair (pair c w) (BinaryNatCode.encode j)) ↔
      ∀ r < FormulaSignSlotRadialCenterValuePacking.degree (radial c) + 1,
        FormulaSignSlotRadialCenterValueTrailingSelection.Zero (radial c)
          (fun i => FormulaSignSlotRadialRetainedValueTest.center hn ht ha hR outer refs c w hv i.val) j r :=
  radius_packet hn ht ha hR outer radial refs c w hv j

theorem guards_packet (c w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR outer) c w)
    (ell : ℕ) : Guards hn ht ha hR outer radial refs (query c w ell) ↔
      FormulaSignSlotRadialCenterValueFamily.Guards (FormulaSignSlotRadialCenterValueLayout.original (radial c))
        (fun i => FormulaSignSlotRadialRetainedValueTest.center hn ht ha hR outer refs c w hv i.val)
        (fun i => FormulaSignSlotRadialCenterValueLayout.tau (radial c) i.val)
        (fun i => FormulaSignSlotRadialCenterValueLayout.degree (radial c) i.val) ∧
      FormulaSignSlotRadialCenterValueTrailingSelection.Guards (radial c)
        (fun i => FormulaSignSlotRadialRetainedValueTest.center hn ht ha hR outer refs c w hv i.val) ell := by
  rw [Guards]
  have HC := FormulaSignSlotRadialRetainedValueCoordinateGuards.guards_packet hn ht ha hR outer radial refs c w hv
  change _ ↔ _ at HC
  simp only [query, pairFst_pair] at HC ⊢
  rw [HC]
  simp only [LowerZero, lowerQuery, pairFst_pair, pairSnd_pair, selected, MacaulayBits.fromBits_encode]
  simp_rw [radius_at hn ht ha hR outer radial refs c w hv]
  simp only [bound, context, pairFst_pair, FormulaSignSlotRadialCenterValueTrailingSelection.Guards,
    FormulaSignSlotRadialRetainedValueCoordinateGuards.original,
    FormulaSignSlotRadialRetainedCoordinateTest.center, FormulaSignSlotRadialRetainedValueTest.center]

theorem guards_actual (c w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR outer) c w)
    (ell : ℕ) : Guards hn ht ha hR outer radial refs (query c w ell) ↔
      FormulaSignSlotRadialCenterValueFamily.Guards (FormulaSignSlotRadialCenterValueLayout.original (radial c))
        (fun i => FormulaSignSlotRadialRetainedValueTest.center hn ht ha hR outer refs c w hv i.val)
        (fun i => FormulaSignSlotRadialCenterValueLayout.tau (radial c) i.val)
        (fun i => FormulaSignSlotRadialCenterValueLayout.degree (radial c) i.val) ∧
      FormulaSignSlotRadialValueCertificate.polynomial (FormulaSignSlotRadialCenterValueLayout.original (radial c))
        (fun i => FormulaSignSlotRadialRetainedValueTest.center hn ht ha hR outer refs c w hv i.val) ≠ 0 ∧
      ell = (FormulaSignSlotRadialValueCertificate.polynomial (FormulaSignSlotRadialCenterValueLayout.original (radial c))
        (fun i => FormulaSignSlotRadialRetainedValueTest.center hn ht ha hR outer refs c w hv i.val)).natTrailingDegree := by
  rw [guards_packet hn ht ha hR outer radial refs c w hv ell]
  constructor
  · rintro ⟨HC, HT⟩
    exact ⟨HC, (FormulaSignSlotRadialCenterValueTrailingSelection.guards_actual (radial c) _ ell HC).mp HT⟩
  · rintro ⟨HC, HT⟩
    exact ⟨HC, (FormulaSignSlotRadialCenterValueTrailingSelection.guards_actual (radial c) _ ell HC).mpr HT⟩

theorem exists_guards (c w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR outer) c w)
    (h : FormulaSignSlotRadialCenterValueFamily.Guards (FormulaSignSlotRadialCenterValueLayout.original (radial c))
      (fun i => FormulaSignSlotRadialRetainedValueTest.center hn ht ha hR outer refs c w hv i.val)
      (fun i => FormulaSignSlotRadialCenterValueLayout.tau (radial c) i.val)
      (fun i => FormulaSignSlotRadialCenterValueLayout.degree (radial c) i.val))
    (r : ℝ) (hr : r ∉ FormulaSignSlotRadialParameterEliminant.bad
      (FormulaSignSlotRadialCenterValueLayout.original (radial c))
      (fun i => FormulaSignSlotRadialRetainedValueTest.center hn ht ha hR outer refs c w hv i.val))
    (x : Fin (FormulaSignSlotCenteredRadialGraph.N (FormulaSignSlotRadialCenterValueLayout.original (radial c)) +
      FormulaSignSlotCenteredRadialGraph.d (FormulaSignSlotRadialCenterValueLayout.original (radial c)) + 1) → ℝ)
    (hx : x ∈ FormulaSignSlotRadialParameterGrid.grid (FormulaSignSlotRadialCenterValueLayout.original (radial c))
      (fun i => FormulaSignSlotRadialRetainedValueTest.center hn ht ha hR outer refs c w hv i.val) r) :
    ∃ ell ≤ FormulaSignSlotRadialCenterValueTrailingSelection.bound (radial c),
      Guards hn ht ha hR outer radial refs (query c w ell) := by
  obtain ⟨ell, hL, HG⟩ := FormulaSignSlotRadialCenterValueTrailingSelection.exists_guards (radial c) _ h r hr x hx
  exact ⟨ell, hL, (guards_packet hn ht ha hR outer radial refs c w hv ell).mpr ⟨h, HG⟩⟩

theorem trailing_packet (c w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR outer) c w)
    (ell r : ℕ) (h : Guards hn ht ha hR outer radial refs (query c w ell)) :
    FormulaSignSlotRadialRetainedValueTest.value hn ht ha hR outer radial refs
      (pair (pair c w) (FormulaSignSlotRadialRetainedValueTest.indices ell r)) = InfinitesimalSign.encode
        (SignType.sign (((FormulaSignSlotRadialValueCertificate.polynomial
          (FormulaSignSlotRadialCenterValueLayout.original (radial c))
          (fun i => FormulaSignSlotRadialRetainedValueTest.center hn ht ha hR outer refs c w hv i.val)).trailingCoeff).coeff r)) := by
  have HG := (guards_packet hn ht ha hR outer radial refs c w hv ell).mp h
  rw [FormulaSignSlotRadialRetainedValueTest.packet hn ht ha hR outer radial refs c w _ hv]
  simp only [FormulaSignSlotRadialRetainedValueTest.indices, WordList.get_encode,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some, MacaulayBits.fromBits_encode]
  apply congrArg (fun a : ℝ => InfinitesimalSign.encode (SignType.sign a))
  exact FormulaSignSlotRadialCenterValueTrailingSelection.trailing_coefficient (radial c) _ ell r HG.1 HG.2

end LeanCanny.Encoding.FormulaSignSlotRadialRetainedValueGuards
