/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialRetainedCoordinateTest
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterValuePacking
public import LeanCanny.Computation.FiniteCoefficientSignScan
/-! # All selected coordinate equations use one unchanged retained bank center -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialRetainedValueCoordinateGuards
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Connectivity LeanCanny.ETR
open LeanCanny.Encoding.Brackets
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotRadialRetainedCoordinateTest.value

def context (q : List Bool) := pairFst (pairFst q)
def root (q : List Bool) := pairFst (pairFst (pairFst q))
def original (radial : List Bool → List Bool) (c : List Bool) :=
  FormulaSignSlotRadialCenterValueLayout.original (radial c)
def selectionQuery (radial : List Bool → List Bool) (q : List Bool) := pair (radial (context q)) (pairSnd q)
def tau (radial : List Bool → List Bool) (q : List Bool) :=
  FormulaSignSlotRadialCenterValueLayout.tau (radial (context q)) (Nat.fromBitsLE (pairSnd q))
def degree (radial : List Bool → List Bool) (q : List Bool) :=
  FormulaSignSlotRadialCenterValueLayout.degree (radial (context q)) (Nat.fromBitsLE (pairSnd q))
noncomputable def bound (radial : List Bool → List Bool) (q : List Bool) :=
  FormulaSignSlotRadialCenterValuePacking.inputBound (radial (context q))
noncomputable def arity (radial : List Bool → List Bool) (q : List Bool) :=
  FormulaSignSlotRadialCenterValueLayout.arity (radial (pairFst q))
def leafQuery (q : List Bool) := pair (pairFst (root q)) (WordList.encode
  [pairSnd (root q), pairSnd (pairFst (pairFst q)), pairSnd (pairFst q), pairSnd q])
def chosenQuery (radial : List Bool → List Bool) (q : List Bool) :=
  pair (pair q (BinaryNatCode.encode (tau radial q))) (BinaryNatCode.encode (degree radial q))
def higherQuery (radial : List Bool → List Bool) (q : List Bool) :=
  pair (pair (pairFst q) (BinaryNatCode.encode (tau radial (pairFst q)))) (pairSnd q)

theorem context_FP : context ∈ FP := by polytime [context]
theorem root_FP : root ∈ FP := by polytime [root]
theorem original_FP (radial : List Bool → List Bool) (hr : radial ∈ FP) : original radial ∈ FP :=
  mem_FP_comp hr FormulaSignSlotRadialCenterValueLayout.original_FP
theorem selectionQuery_FP (radial : List Bool → List Bool) (hr : radial ∈ FP) : selectionQuery radial ∈ FP :=
  mem_FP_pair (mem_FP_comp context_FP hr) pairSnd_mem_FP
theorem tau_binary (radial : List Bool → List Bool) (hr : radial ∈ FP) : BinaryFn (tau radial) := by
  have H : BinaryFn (fun q => FormulaSignSlotRadialCenterValueLayout.tau
      (pairFst (selectionQuery radial q)) (Nat.fromBitsLE (pairSnd (selectionQuery radial q)))) :=
    FormulaSignSlotRadialCenterValueLayout.tau_binary.comp (selectionQuery_FP radial hr)
  exact H.of_eq (fun q => by simp only [selectionQuery, pairFst_pair, pairSnd_pair]; rfl)
theorem degree_binary (radial : List Bool → List Bool) (hr : radial ∈ FP) : BinaryFn (degree radial) := by
  have H : BinaryFn (fun q => FormulaSignSlotRadialCenterValueLayout.degree
      (pairFst (selectionQuery radial q)) (Nat.fromBitsLE (pairSnd (selectionQuery radial q)))) :=
    FormulaSignSlotRadialCenterValueLayout.degree_binary.comp (selectionQuery_FP radial hr)
  exact H.of_eq (fun q => by simp only [selectionQuery, pairFst_pair, pairSnd_pair]; rfl)

theorem bound_binary (radial : List Bool → List Bool) (hr : radial ∈ FP) : BinaryFn (bound radial) :=
  FormulaSignSlotRadialCenterValuePacking.inputBound_binary.comp (mem_FP_comp context_FP hr)
theorem arity_unary (radial : List Bool → List Bool) (hr : radial ∈ FP) : UnaryFn (arity radial) :=
  FormulaSignSlotRadialCenterValueLayout.arity_unary.comp (mem_FP_comp pairFst_mem_FP hr)
theorem leafQuery_FP : leafQuery ∈ FP := by
  unfold leafQuery WordList.encode
  exact mem_FP_pair (by polytime [root]) (mem_FP_pair (by polytime [root])
    (mem_FP_pair (by polytime) (mem_FP_pair (by polytime) (mem_FP_pair pairSnd_mem_FP (constFn_mem_FP [])))))
theorem chosenQuery_FP (radial : List Bool → List Bool) (hr : radial ∈ FP) : chosenQuery radial ∈ FP :=
  mem_FP_pair (mem_FP_pair id_mem_FP (tau_binary radial hr).bits_mem_FP) (degree_binary radial hr).bits_mem_FP
theorem higherQuery_FP (radial : List Bool → List Bool) (hr : radial ∈ FP) : higherQuery radial ∈ FP := by
  have HT : BinaryFn (fun q => tau radial (pairFst q)) := (tau_binary radial hr).comp pairFst_mem_FP
  exact mem_FP_pair (mem_FP_pair pairFst_mem_FP HT.bits_mem_FP) pairSnd_mem_FP

private theorem all_flag (P : List Bool → Prop) (B : List Bool → ℕ)
    (E : SpaceFunction (fun q => [decide (P q)])) (hB : BinaryFn B) :
    SpaceFunction (fun q => [decide (∀ i < B q, P (pair q (BinaryNatCode.encode i)))]) :=
  (E.forall_binary hB).congr (funext fun q => by
    simp only [List.cons.injEq, and_true, decide_eq_true_eq])
private theorem not_flag (P : List Bool → Prop) (E : SpaceFunction (fun q => [decide (P q)])) :
    SpaceFunction (fun q => [decide (¬P q)]) := by
  have EN := E.postcompose (fun z => [decide (z ≠ [true])])
    (stringEq_fppred id_mem_FP (constFn_mem_FP [true])).not.flag_mem_FP
  exact EN.congr (funext fun q => by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact not_congr (by simp only [List.cons.injEq, and_true, decide_eq_true_eq]))

private theorem implies_flag (P Q : List Bool → Prop) (hP : FPPred P)
    (E : SpaceFunction (fun q => [decide (Q q)])) :
    SpaceFunction (fun q => [decide (P q → Q q)]) := by
  have H := SpaceFunction.branch (fun q => decide (P q)) hP.flag_mem_FP E
    (SpaceFunction.ofFP _ (constFn_mem_FP [true]))
  exact H.congr (funext fun q => by
    simp only [decide_eq_true_eq]
    by_cases HP : P q <;> simp only [HP, ite_true, ite_false, true_implies, false_implies, decide_true])

variable {n : List Bool → ℕ} {t : List Bool → Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R : List Bool → ℕ} (hR : BinaryFn R) (outer : Bool) (radial refs : List Bool → List Bool)

noncomputable def LeafZero (q : List Bool) : Prop :=
  FormulaSignSlotRadialRetainedCoordinateTest.value hn ht ha hR outer (original radial) refs (leafQuery q) =
    InfinitesimalSign.encode 0
noncomputable def RadiusZero (q : List Bool) : Prop := ∀ r < bound radial (pairFst (pairFst q)) + 1,
  LeafZero hn ht ha hR outer radial refs (pair q (BinaryNatCode.encode r))
noncomputable def TargetZero (q : List Bool) : Prop := ∀ j < bound radial (pairFst q) + 1,
  RadiusZero hn ht ha hR outer radial refs (pair q (BinaryNatCode.encode j))
noncomputable def LowerZero (q : List Bool) : Prop := ∀ s < tau radial q,
  TargetZero hn ht ha hR outer radial refs (pair q (BinaryNatCode.encode s))
noncomputable def HigherZero (q : List Bool) : Prop := ∀ j < bound radial q + 1,
  degree radial q < j → RadiusZero hn ht ha hR outer radial refs
    (higherQuery radial (pair q (BinaryNatCode.encode j)))
noncomputable def GuardAt (q : List Bool) : Prop :=
  (tau radial q ≤ bound radial q ∧ degree radial q ≤ bound radial q) ∧
  LowerZero hn ht ha hR outer radial refs q ∧
  ¬RadiusZero hn ht ha hR outer radial refs (chosenQuery radial q) ∧
  HigherZero hn ht ha hR outer radial refs q
noncomputable def Guards (q : List Bool) : Prop := ∀ i < arity radial q,
  GuardAt hn ht ha hR outer radial refs (pair q (BinaryNatCode.encode i))

attribute [local irreducible] LeafZero RadiusZero TargetZero LowerZero HigherZero GuardAt Guards

theorem radius_evaluator (hr : radial ∈ FP) (hf : refs ∈ FP) :
    SpaceFunction (fun q => [decide (RadiusZero hn ht ha hR outer radial refs q)]) := by
  have ES := (FormulaSignSlotRadialRetainedCoordinateTest.evaluator hn ht ha hR outer
    (original radial) refs (original_FP radial hr) hf).precompose leafQuery leafQuery_FP
  have EZ := ES.postcompose (fun z => [decide (z = InfinitesimalSign.encode 0)])
    (stringEq_fppred id_mem_FP (constFn_mem_FP _)).flag_mem_FP
  have HB : BinaryFn (fun q => bound radial (pairFst (pairFst q))) :=
    (bound_binary radial hr).comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  have EZ0 : SpaceFunction (fun q => [decide (LeafZero hn ht ha hR outer radial refs q)]) :=
    EZ.congr (funext fun q => by
      apply congrArg List.singleton
      apply Bool.eq_iff_iff.mpr
      simp only [Function.comp_apply, LeafZero, decide_eq_true_eq])
  have EA := all_flag (LeafZero hn ht ha hR outer radial refs)
    (fun q => bound radial (pairFst (pairFst q)) + 1) EZ0 (HB.add (BinaryFn.const 1))
  exact EA.congr (funext fun q => by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [RadiusZero, decide_eq_true_eq])

theorem guardAt_evaluator (hr : radial ∈ FP) (hf : refs ∈ FP) :
    SpaceFunction (fun q => [decide (GuardAt hn ht ha hR outer radial refs q)]) := by
  have ER := radius_evaluator hn ht ha hR outer radial refs hr hf
  have HB : BinaryFn (fun q => bound radial (pairFst q)) := (bound_binary radial hr).comp pairFst_mem_FP
  have ET := all_flag (RadiusZero hn ht ha hR outer radial refs)
    (fun q => bound radial (pairFst q) + 1) ER (HB.add (BinaryFn.const 1))
  have ET0 : SpaceFunction (fun q => [decide (TargetZero hn ht ha hR outer radial refs q)]) :=
    ET.congr (funext fun q => by
      apply congrArg List.singleton
      apply Bool.eq_iff_iff.mpr
      simp only [TargetZero, decide_eq_true_eq])
  have EL := all_flag (TargetZero hn ht ha hR outer radial refs) (tau radial) ET0 (tau_binary radial hr)
  have EC := not_flag (fun q => RadiusZero hn ht ha hR outer radial refs (chosenQuery radial q)) (ER.precompose (chosenQuery radial) (chosenQuery_FP radial hr))
  have HD : BinaryFn (fun q => degree radial (pairFst q)) := (degree_binary radial hr).comp pairFst_mem_FP
  have EH := implies_flag _ _ (HD.lt (BinaryFn.fromBits pairSnd_mem_FP))
    (ER.precompose (higherQuery radial) (higherQuery_FP radial hr))
  have EHA := EH.forall_binary ((bound_binary radial hr).add (BinaryFn.const 1))
  have EB := SpaceFunction.ofFP _ (((tau_binary radial hr).le (bound_binary radial hr)).and
    ((degree_binary radial hr).le (bound_binary radial hr))).flag_mem_FP
  refine (EB.andFlags (EL.andFlags (EC.andFlags EHA))).congr (funext fun q => ?_)
  simp only [GuardAt, LowerZero, TargetZero, RadiusZero, HigherZero,
    pairFst_pair, pairSnd_pair, MacaulayBits.fromBits_encode, List.cons.injEq, and_true, decide_eq_true_eq]

theorem evaluator (hr : radial ∈ FP) (hf : refs ∈ FP) :
    SpaceFunction (fun q => [decide (Guards hn ht ha hR outer radial refs q)]) :=
  all_flag (GuardAt hn ht ha hR outer radial refs) (arity radial) (guardAt_evaluator hn ht ha hR outer radial refs hr hf)
    (BinaryFn.ofUnary (arity_unary radial hr)) |>.congr (funext fun q => by
      apply congrArg List.singleton
      apply Bool.eq_iff_iff.mpr
      simp only [Guards, decide_eq_true_eq])

private theorem leaf_zero_packet (c w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR outer) c w)
    (i s j r : ℕ) : LeafZero hn ht ha hR outer radial refs
      (pair (pair (pair (pair (pair c w) (BinaryNatCode.encode i))
        (BinaryNatCode.encode s)) (BinaryNatCode.encode j)) (BinaryNatCode.encode r)) ↔
    FormulaSignSlotRadialCenterSelection.Zero
      (FormulaSignSlotRadialCoordinatePacket.packet (original radial c) i)
        (fun k => FormulaSignSlotRadialRetainedCoordinateTest.center hn ht ha hR outer
          refs c w hv k.val) s j r := by
  unfold LeafZero
  have HQ : leafQuery (pair (pair (pair (pair (pair c w) (BinaryNatCode.encode i))
      (BinaryNatCode.encode s)) (BinaryNatCode.encode j)) (BinaryNatCode.encode r)) =
        pair (pair c w) (FormulaSignSlotRadialRetainedCoordinateTest.indices i s j r) := by
    simp only [leafQuery, root, pairFst_pair, pairSnd_pair, FormulaSignSlotRadialRetainedCoordinateTest.indices]
  rw [HQ, FormulaSignSlotRadialRetainedCoordinateTest.coordinate_packet hn ht ha hR outer
    (original radial) refs c w hv i s j r]
  exact (SquareSampleTestSign.encode_eq_iff _ _).trans sign_eq_zero_iff

private theorem bound_packet (c w : List Bool) (i : ℕ) :
    bound radial (pair (pair c w) (BinaryNatCode.encode i)) =
      FormulaSignSlotRadialCenterSelection.bound (FormulaSignSlotRadialCoordinatePacket.packet (original radial c) i) := by
  simp only [bound, context, pairFst_pair, FormulaSignSlotRadialCenterValuePacking.inputBound, original]
  exact (FormulaSignSlotRadialCenterValueSelection.bound_eq _ i).symm

private theorem guardAt_packet (c w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR outer) c w)
    (i : ℕ) : GuardAt hn ht ha hR outer radial refs (pair (pair c w) (BinaryNatCode.encode i)) ↔
      FormulaSignSlotRadialCenterSelection.Guards
        (FormulaSignSlotRadialCoordinatePacket.packet (original radial c) i)
          (fun k => FormulaSignSlotRadialRetainedCoordinateTest.center hn ht ha hR outer
            refs c w hv k.val)
          (FormulaSignSlotRadialCenterValueLayout.tau (radial c) i)
          (FormulaSignSlotRadialCenterValueLayout.degree (radial c) i) := by
  rw [GuardAt]
  simp only [LowerZero, TargetZero, RadiusZero, HigherZero, chosenQuery, higherQuery,
    pairFst_pair, pairSnd_pair]
  simp_rw [leaf_zero_packet hn ht ha hR outer radial refs c w hv]
  rw [bound_packet radial c w i]
  simp only [tau, degree, context, pairFst_pair, pairSnd_pair, MacaulayBits.fromBits_encode,
    FormulaSignSlotRadialCenterSelection.Guards, not_forall, exists_prop, and_assoc]

private theorem arity_packet (radial : List Bool → List Bool) (c w : List Bool) :
    arity radial (pair c w) = FormulaSignSlotCenteredRadialGraph.N (original radial c) +
      FormulaSignSlotCenteredRadialGraph.d (original radial c) + 1 := by
  simp only [arity, pairFst_pair, FormulaSignSlotRadialCenterValueLayout.arity,
    FormulaSignSlotRadialFormalInput.spatial, original]
private theorem all_index {A : ℕ} (P : ℕ → Prop) :
    (∀ i < A, P i) ↔ ∀ i : Fin A, P i.val := by
  constructor
  · intro H i; exact H i.val i.isLt
  · intro H i hi; exact H ⟨i, hi⟩

theorem guards_packet (c w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR outer) c w) :
    Guards hn ht ha hR outer radial refs (pair c w) ↔
      FormulaSignSlotRadialCenterValueFamily.Guards (original radial c)
        (fun i => FormulaSignSlotRadialRetainedCoordinateTest.center hn ht ha hR outer
          refs c w hv i.val)
        (fun i => FormulaSignSlotRadialCenterValueLayout.tau (radial c) i.val)
        (fun i => FormulaSignSlotRadialCenterValueLayout.degree (radial c) i.val) := by
  rw [← FormulaSignSlotRadialCenterValueSelection.all_guards (original radial c)
    (FormulaSignSlotRadialRetainedCoordinateTest.center hn ht ha hR outer refs c w hv)]
  rw [Guards, arity_packet]
  exact (all_index _).trans (forall_congr' fun i =>
    guardAt_packet hn ht ha hR outer radial refs c w hv i.val)

end LeanCanny.Encoding.FormulaSignSlotRadialRetainedValueCoordinateGuards
