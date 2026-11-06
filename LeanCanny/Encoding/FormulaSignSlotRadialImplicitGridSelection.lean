/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialImplicitCenterSelection
public import LeanCanny.Encoding.FormulaSignSlotRadialImplicitGridScan
public import LeanCanny.Computation.SpaceFunctionBinaryExistence
/-! # Native parameter-grid checking with internally verified selections -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialImplicitGridSelection
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Connectivity LeanCanny.ETR
open LeanCanny.Encoding.Brackets
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "F" => FormulaSignSlotRadialJointStratumSampler.input
attribute [local irreducible] FormulaSignSlotRadialImplicitCenterSelection.Guards
  FormulaSignSlotRadialImplicitGridTest.value FormulaSignSlotRadialImplicitGridTest.language
  FormulaSignSlotRadialJointGridSource.source FormulaSignSlotRadialParameterEliminant.coordinate
  FormulaSignSlotSource.dimension FormulaSignSlotMargin.initialDimension FormulaSignSlotMargin.initialPolynomial

def context (p : List Bool) := pairFst (pairFst p)
def own (p : List Bool) := pairSnd (pairFst p)
def coordinate (p : List Bool) := Nat.fromBitsLE (pairSnd p)
noncomputable def limit (p : List Bool) := FormulaSignSlotRadialJointCoefficientCatalogue.limit
  (FormulaSignSlotRadialImplicitGridTest.header (context p))
theorem context_FP : context ∈ FP := by polytime [context]
theorem limit_binary : BinaryFn limit := FormulaSignSlotRadialJointCoefficientCatalogue.limit_binary.comp
  (mem_FP_comp (f:=context) (g:=FormulaSignSlotRadialImplicitGridTest.header)
    context_FP FormulaSignSlotRadialImplicitGridTest.header_FP)

def selectedQuery (z : List Bool) := pair (pairFst (pairFst z)) (pair (pairSnd (pairFst z)) (pairSnd z))
def zeroQuery (z : List Bool) := pair (pairFst (pairFst (pairFst z)))
  (pair (pairSnd (pairFst (pairFst z))) (pairSnd (pairFst z)))
theorem selectedQuery_FP : selectedQuery ∈ FP := by polytime [selectedQuery]
theorem zeroQuery_FP : zeroQuery ∈ FP := by polytime [zeroQuery]
noncomputable def Candidate (z : List Bool) : Prop :=
  FormulaSignSlotRadialImplicitCenterSelection.Guards (selectedQuery z) ∧
    zeroQuery z ∈ FormulaSignSlotRadialImplicitGridTest.language

theorem candidate_evaluator : SpaceFunction (fun z => [decide (Candidate z)]) := by
  have EC := FormulaSignSlotRadialImplicitCenterSelection.evaluator.precompose selectedQuery selectedQuery_FP
  have EZ := (FormulaSignSlotRadialImplicitGridTest.decider.precompose zeroQuery zeroQuery_FP).flagEvaluator
  exact (EC.andFlags EZ).congr (funext fun z => by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [Candidate,Set.mem_preimage,Function.comp_apply,List.cons.injEq,and_true,decide_eq_true_eq])

noncomputable def At (p : List Bool) : Prop := ∃ tau < limit p,∃ D < limit p,
  Candidate (pair (pair p (BinaryNatCode.encode tau)) (BinaryNatCode.encode D))
theorem at_evaluator : SpaceFunction (fun p => [decide (At p)]) := by
  have HD : BinaryFn (fun z => limit (pairFst z)) := limit_binary.comp pairFst_mem_FP
  have ED := candidate_evaluator.exists_binary HD
  have ET := ED.exists_binary limit_binary
  exact ET.congr (funext fun p => by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [At,List.cons.injEq,and_true,decide_eq_true_eq,pairFst_pair])

noncomputable def count (p : List Bool) := FormulaSignSlotRadialJointLayout.spatialCount
  (FormulaSignSlotRadialImplicitGridTest.header (pairFst p))
theorem count_unary : UnaryFn count := FormulaSignSlotRadialJointLayout.spatialCount_unary.comp
  (mem_FP_comp (f:=pairFst) (g:=FormulaSignSlotRadialImplicitGridTest.header)
    pairFst_mem_FP FormulaSignSlotRadialImplicitGridTest.header_FP)
noncomputable def Holds (p : List Bool) : Prop := ∀ j < count p,At (pair p (BinaryNatCode.encode j))
theorem holds_evaluator : SpaceFunction (fun p => [decide (Holds p)]) :=
  (at_evaluator.forall_binary (BinaryFn.ofUnary count_unary)).congr (funext fun p => by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [Holds,List.cons.injEq,and_true,decide_eq_true_eq])


private theorem natural_point_heq {a b : ℕ} (h : a = b) (v : ℕ → ℝ) :
    HEq (fun i : Fin a => v (4*i.val)) (fun i : Fin b => v (4*i.val)) := by cases h; rfl
private theorem guards_congr (c d : List Bool) (h : c = d)
    (a : Fin (FormulaSignSlotCenteredRadialGraph.d (pairFst c)) → ℝ)
    (b : Fin (FormulaSignSlotCenteredRadialGraph.d (pairFst d)) → ℝ) (hab : HEq a b) (t D : ℕ) :
    FormulaSignSlotRadialCenterSelection.Guards c a t D ↔
      FormulaSignSlotRadialCenterSelection.Guards d b t D := by
  cases h
  have H : a = b := eq_of_heq hab
  subst b
  rfl
private theorem radial_packet (H : List Bool) (j t : ℕ) :
    FormulaSignSlotRadialJointGridLayout.radial (pair H (pair (BinaryNatCode.encode j) (BinaryNatCode.encode t))) =
      FormulaSignSlotRadialCoordinatePacket.packet (FormulaSignSlotRadialJointLayout.source true H) j := by
  unfold FormulaSignSlotRadialJointGridLayout.radial FormulaSignSlotRadialJointGridLayout.sliceContext
  simp only [FormulaSignSlotRadialJointGridLayout.header,FormulaSignSlotRadialJointGridLayout.coordinateWord,
    FormulaSignSlotRadialJointGridLayout.tauInput,pairFst_pair,pairSnd_pair,
    FormulaSignSlotRadialCoordinatePacket.writer_packet]

private theorem selected_guards_iff (H : List Bool) (j t D : ℕ) (v : ℕ → ℝ) :
    let z := pair H (pair (BinaryNatCode.encode j) (BinaryNatCode.encode t))
    FormulaSignSlotRadialCenterSelection.Guards (FormulaSignSlotRadialJointGridLayout.radial z)
      (FormulaSignSlotRadialJointGridSource.center z v)
      (Nat.fromBitsLE (FormulaSignSlotRadialJointGridLayout.tauWord z)) D ↔
    FormulaSignSlotRadialCenterSelection.Guards
      (FormulaSignSlotRadialCoordinatePacket.packet (FormulaSignSlotRadialJointLayout.source true H) j)
      (fun i => v (4*i.val)) t D := by
  let z := pair H (pair (BinaryNatCode.encode j) (BinaryNatCode.encode t))
  have HP := radial_packet H j t
  have HA : HEq (FormulaSignSlotRadialJointGridSource.center z v)
      (fun i : Fin (FormulaSignSlotCenteredRadialGraph.d (pairFst
        (FormulaSignSlotRadialCoordinatePacket.packet (FormulaSignSlotRadialJointLayout.source true H) j))) => v (4*i.val)) :=
    natural_point_heq (congrArg (fun u => FormulaSignSlotCenteredRadialGraph.d (pairFst u)) HP) v
  have HT : Nat.fromBitsLE (FormulaSignSlotRadialJointGridLayout.tauWord z) = t := by
    simp only [z,FormulaSignSlotRadialJointGridLayout.tauWord,FormulaSignSlotRadialJointGridLayout.sliceContext,
      FormulaSignSlotRadialJointGridLayout.tauInput,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
  change FormulaSignSlotRadialCenterSelection.Guards (FormulaSignSlotRadialJointGridLayout.radial z)
    (FormulaSignSlotRadialJointGridSource.center z v) (Nat.fromBitsLE (FormulaSignSlotRadialJointGridLayout.tauWord z)) D ↔ _
  rw [HT]
  exact guards_congr _ _ HP _ _ HA t D

noncomputable def GridAt (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w)
    (j : Fin (FormulaSignSlotRadialJointLayout.spatialCount (FormulaSignSlotRadialImplicitGridTest.header c))) : Prop :=
  let H := FormulaSignSlotRadialImplicitGridTest.header c
  let v := FormulaSignSlotRadialImplicitGridTest.env c w hw
  (FormulaSignSlotRadialParameterEliminant.coordinate (FormulaSignSlotRadialJointLayout.source true H)
    (FormulaSignSlotRadialJointGeometry.center H v) j).eval₂
      (Polynomial.evalRingHom (FormulaSignSlotRadialJointGeometry.parameter H v))
      (FormulaSignSlotRadialJointGeometry.spatialPoint H v j) = 0

private noncomputable def gridValue (z : List Bool) (v : ℕ → ℝ) : ℝ :=
  (FormulaSignSlotRadialJointGridSource.source.polynomial z).eval₂ (Int.castRingHom ℝ) (fun i => v i.val)

private theorem candidate_packet_iff (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w)
    (j : Fin (FormulaSignSlotRadialJointLayout.spatialCount (FormulaSignSlotRadialImplicitGridTest.header c))) (t D : ℕ) :
    Candidate (pair (pair (pair (pair c w) (BinaryNatCode.encode j.val)) (BinaryNatCode.encode t)) (BinaryNatCode.encode D)) ↔
    FormulaSignSlotRadialImplicitCenterSelection.Guards
      (FormulaSignSlotRadialImplicitCenterSelection.packet c w j.val t D) ∧ GridAt c w hw j := by
  have HS : selectedQuery (pair (pair (pair (pair c w) (BinaryNatCode.encode j.val))
      (BinaryNatCode.encode t)) (BinaryNatCode.encode D)) =
      FormulaSignSlotRadialImplicitCenterSelection.packet c w j.val t D := by
    simp only [selectedQuery,FormulaSignSlotRadialImplicitCenterSelection.packet,pairFst_pair,pairSnd_pair]
  have HZ : zeroQuery (pair (pair (pair (pair c w) (BinaryNatCode.encode j.val))
      (BinaryNatCode.encode t)) (BinaryNatCode.encode D)) =
      pair (pair c w) (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode t)) := by
    simp only [zeroQuery,pairFst_pair,pairSnd_pair]
  rw [Candidate,HS,HZ]
  apply and_congr_right
  intro HG
  have HA := (FormulaSignSlotRadialImplicitCenterSelection.guards_packet c w hw j.val t D).mp HG
  have HN := (selected_guards_iff (FormulaSignSlotRadialImplicitGridTest.header c) j.val t D
    (FormulaSignSlotRadialImplicitGridTest.env c w hw)).mpr HA
  rw [FormulaSignSlotRadialImplicitGridTest.language_packet_iff _ _ _ hw]
  change (gridValue (FormulaSignSlotRadialImplicitGridTest.read
    (pair c (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode t))))
    (FormulaSignSlotRadialImplicitGridTest.env c w hw) = 0) ↔ _
  have HR : FormulaSignSlotRadialImplicitGridTest.read
      (pair c (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode t))) =
      pair (FormulaSignSlotRadialImplicitGridTest.header c) (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode t)) := by
    simp only [FormulaSignSlotRadialImplicitGridTest.read,pairFst_pair,pairSnd_pair]
  rw [HR]
  change ((FormulaSignSlotRadialJointGridSource.source.polynomial
    (pair (FormulaSignSlotRadialImplicitGridTest.header c) (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode t)))).eval₂
    (Int.castRingHom ℝ) (fun i => FormulaSignSlotRadialImplicitGridTest.env c w hw i.val) = 0) ↔ _
  rw [FormulaSignSlotRadialImplicitGridScan.selected_evaluation _ j _ _ D HN]
  rfl


private theorem limit_packet (c w : List Bool) (j : ℕ) :
    limit (pair (pair c w) (BinaryNatCode.encode j)) =
    FormulaSignSlotRadialCenterSelection.bound (FormulaSignSlotRadialCoordinatePacket.packet
      (FormulaSignSlotRadialJointLayout.source true (FormulaSignSlotRadialImplicitGridTest.header c)) j)+1 := by
  simp only [limit,context,pairFst_pair]
  unfold FormulaSignSlotRadialJointCoefficientCatalogue.limit
  apply congrArg (fun n => n+1)
  apply FormulaSignSlotRadialEliminantRootProfiles.degree_eq
  simp only [FormulaSignSlotRadialJointCoefficientCatalogue.base,FormulaSignSlotRadialCoordinatePacket.root,pairFst_pair]

/-- The perturbation and degree receipts are chosen and checked internally. -/
theorem at_packet_iff (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w)
    (j : Fin (FormulaSignSlotRadialJointLayout.spatialCount (FormulaSignSlotRadialImplicitGridTest.header c))) :
    At (pair (pair c w) (BinaryNatCode.encode j.val)) ↔ GridAt c w hw j := by
  constructor
  · rintro ⟨t,_,D,_,HG⟩
    exact ((candidate_packet_iff c w hw j t D).mp HG).2
  · intro HG
    obtain ⟨t,ht,D,hD,HA⟩ := FormulaSignSlotRadialCenterSelection.exists_guards
      (FormulaSignSlotRadialCoordinatePacket.packet
        (FormulaSignSlotRadialJointLayout.source true (FormulaSignSlotRadialImplicitGridTest.header c)) j.val)
      (fun i => FormulaSignSlotRadialImplicitCoefficientTest.env c w hw (4*i.val))
    have HT : t < limit (pair (pair c w) (BinaryNatCode.encode j.val)) := by rw [limit_packet]; omega
    have HD : D < limit (pair (pair c w) (BinaryNatCode.encode j.val)) := by rw [limit_packet]; omega
    exact ⟨t,HT,D,HD,(candidate_packet_iff c w hw j t D).mpr
      ⟨(FormulaSignSlotRadialImplicitCenterSelection.guards_packet c w hw j.val t D).mpr HA,HG⟩⟩

theorem holds_packet_iff (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid F c w) :
    Holds (pair c w) ↔
    FormulaSignSlotRadialJointGeometry.spatialPoint (FormulaSignSlotRadialImplicitGridTest.header c)
      (FormulaSignSlotRadialImplicitGridTest.env c w hw) ∈
    FormulaSignSlotRadialParameterGrid.grid
      (FormulaSignSlotRadialJointLayout.source true (FormulaSignSlotRadialImplicitGridTest.header c))
      (FormulaSignSlotRadialJointGeometry.center (FormulaSignSlotRadialImplicitGridTest.header c)
        (FormulaSignSlotRadialImplicitGridTest.env c w hw))
      (FormulaSignSlotRadialJointGeometry.parameter (FormulaSignSlotRadialImplicitGridTest.header c)
        (FormulaSignSlotRadialImplicitGridTest.env c w hw)) := by
  change (∀ j < count (pair c w),At (pair (pair c w) (BinaryNatCode.encode j))) ↔ ∀ j,GridAt c w hw j
  simp only [count,pairFst_pair]
  constructor
  · intro H j
    exact (at_packet_iff c w hw j).mp (H j.val j.isLt)
  · intro H j hj
    exact (at_packet_iff c w hw ⟨j,hj⟩).mpr (H ⟨j,hj⟩)

noncomputable def language : Language := {p | SquareSampleCompleteVertices.Valid F (pairFst p) (pairSnd p) ∧ Holds p}
theorem decider : SpaceDecider language := by
  have EV := SquareSampleCompleteVertices.decider (ImplicitSourceGramGrid.access FormulaSignSlotRadialJointStratum.source
    FormulaSignSlotRadialJointStratumNative.access FormulaSignSlotRadialJointStratumSampler.positive)
  apply (EV.flagEvaluator.andFlags holds_evaluator).decider (fun v => decide (v=[true]))
    (stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro p
  simp only [language,SquareSampleCompleteVertices.language,Set.mem_ofPred_eq,
    List.cons.injEq,and_true,decide_eq_true_eq]
theorem mem_PSPACE : language ∈ PSPACE := decider.mem_PSPACE

end LeanCanny.Encoding.FormulaSignSlotRadialImplicitGridSelection
