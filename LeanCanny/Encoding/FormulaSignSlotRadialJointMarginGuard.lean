/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialJointPrincipalGuard
public import LeanCanny.Encoding.FormulaSignSlotRadialRetainedTrailingGuards
/-! # The actual margin trailing choice uses the same joint node and center -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialJointSample
open LeanCanny.Computation LeanCanny.Connectivity LeanCanny.Geometry LeanCanny.Algebra LeanCanny.ETR
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "HN" => FormulaSignSlotRadialJointLayout.dimension_unary
local notation "HT" => FormulaSignSlotRadialJointCore.equation_FP
local notation "HA" => FormulaSignSlotRadialJointCore.scope
local notation "HR" => IntegralMixedOriginalRegularSource.radius_binary radius_binary
attribute [local irreducible] radius FormulaSignSlotRadialJointCore.equation
  FormulaSignSlotRadialJointLayout.dimension IntegralMixedPhysicalMarkedPlan.bank slot context word

noncomputable def marginCoordinate (p : List Bool) := FormulaSignSlotMargin.objective
  (FormulaSignSlotRadialJointLayout.source true (header p))
noncomputable def marginIndexPacket (p : List Bool) := pair p (List.replicate (marginCoordinate p) true)
noncomputable def marginChild (p : List Bool) := indexed p (marginCoordinate p)
noncomputable def marginIndex (p : List Bool) := Nat.fromBitsLE (slot 4 (context p))
noncomputable def marginQuery (p : List Bool) := FormulaSignSlotRadialRetainedTrailingGuards.query
  (context (marginChild p)) (word p) (Nat.fromBitsLE (tableChoice 0 (marginIndexPacket p)))
    (Nat.fromBitsLE (tableChoice 1 (marginIndexPacket p))) (marginIndex p)

theorem marginCoordinate_unary : UnaryFn marginCoordinate := by
  have HS : (fun p => FormulaSignSlotRadialJointLayout.source true (header p)) ∈ FP :=
    mem_FP_comp (f := header) (g := FormulaSignSlotRadialJointLayout.source true)
      header_FP (FormulaSignSlotRadialJointLayout.source_FP true)
  exact FormulaSignSlotMargin.objective_unary.comp HS
theorem marginIndexPacket_FP : marginIndexPacket ∈ FP :=
  mem_FP_pair id_mem_FP (marginCoordinate_unary.replicate_mem_FP true)
theorem marginChild_FP : marginChild ∈ FP := mem_FP_comp
  (mem_FP_pair id_mem_FP (BinaryFn.ofUnary marginCoordinate_unary).bits_mem_FP) indexedPacket_FP
theorem marginIndex_binary : BinaryFn marginIndex := by
  have HS : (fun p => slot 4 (context p)) ∈ FP := mem_FP_comp (f := context) (g := slot 4) context_FP (slot_FP 4)
  exact BinaryFn.fromBits HS
theorem marginQuery_FP : marginQuery ∈ FP := by
  have HC := mem_FP_comp marginChild_FP context_FP
  have H0 : BinaryFn (fun p => Nat.fromBitsLE (tableChoice 0 (marginIndexPacket p))) :=
    (BinaryFn.fromBits (tableChoice_FP 0)).comp marginIndexPacket_FP
  have H1 : BinaryFn (fun p => Nat.fromBitsLE (tableChoice 1 (marginIndexPacket p))) :=
    (BinaryFn.fromBits (tableChoice_FP 1)).comp marginIndexPacket_FP
  exact mem_FP_pair (mem_FP_pair HC word_FP)
    (mem_FP_pair H0.bits_mem_FP (mem_FP_pair H1.bits_mem_FP (mem_FP_pair marginIndex_binary.bits_mem_FP (constFn_mem_FP []))))

attribute [local irreducible] marginCoordinate

noncomputable def MarginGuard (p : List Bool) :=
  FormulaSignSlotRadialRetainedTrailingGuards.Guards HN HT HA HR false indexedRadial centerRefs (marginQuery p)
theorem margin_guard_evaluator : SpaceFunction (fun p => [decide (MarginGuard p)]) :=
  (FormulaSignSlotRadialRetainedTrailingGuards.evaluator HN HT HA HR false indexedRadial centerRefs
    indexedRadial_FP centerRefs_FP).precompose marginQuery marginQuery_FP

noncomputable def marginMeaningAt (c : List Bool) (v : ℕ → ℝ) (tau D ell : ℕ) : Prop :=
  FormulaSignSlotRadialCenterTrailingSelection.Guards c (fun j => v j.val) tau D ell
attribute [local irreducible] marginMeaningAt
private theorem marginMeaningAt_congr (c : List Bool) (v w : ℕ → ℝ) (tau D ell : ℕ)
    (h : ∀ j < FormulaSignSlotSource.dimension (pairFst c), v j = w j) :
    marginMeaningAt c v tau D ell ↔ marginMeaningAt c w tau D ell := by
  have HE : (fun j : Fin (FormulaSignSlotSource.dimension (pairFst c)) => v j.val) =
      (fun j => w j.val) := funext (fun j => h j.val j.isLt)
  unfold marginMeaningAt
  rw [HE]
noncomputable def MarginMeaning (p : List Bool) (hv : Valid p) : Prop := marginMeaningAt
  (FormulaSignSlotRadialCoordinatePacket.packet (FormulaSignSlotRadialJointLayout.source true (header p))
    (marginCoordinate p)) (fun j => values p hv (FormulaSignSlotRadialJointLayout.column 0 j))
      (tauChoice p (marginCoordinate p)) (degreeChoice p (marginCoordinate p)) (marginIndex p)

private theorem margin_choices (field : ℕ) (p : List Bool) :
    tableChoice field (marginIndexPacket p) = WordList.get (slot field (context p)) (marginCoordinate p) := by
  simp only [tableChoice, marginIndexPacket, pairFst_pair, pairSnd_pair, List.length_replicate, WordList.reader_packet]

theorem margin_guard_actual (p : List Bool) (hv : Valid p) : MarginGuard p ↔ MarginMeaning p hv := by
  have HV := indexed_valid p (marginCoordinate p) hv
  have HW : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input HN HT HA HR false)
      (context (marginChild p)) (word (marginChild p)) := full_valid (marginChild p) HV
  let v := FormulaSignSlotRadialRetainedPrincipalTest.center HN HT HA HR false centerRefs
    (context (marginChild p)) (word (marginChild p)) HW
  have HC0 : (fun j : Fin (FormulaSignSlotRadialJointLayout.centerCount (header (marginChild p))) => v j.val) =
      FormulaSignSlotRadialJointGeometry.center (header (marginChild p)) (values (marginChild p) HV) := by
    funext j
    exact retained_center (marginChild p) HV j
  have HH : header (marginChild p) = header p := indexed_header p (marginCoordinate p)
  have HCvalues : values (marginChild p) HV = values p hv := indexed_values p (marginCoordinate p) hv
  rw [HH, HCvalues] at HC0
  have HE := FormulaSignSlotRadialRetainedTrailingGuards.guards_packet HN HT HA HR false indexedRadial centerRefs
    (context (marginChild p)) (word (marginChild p)) HW
      (tauChoice p (marginCoordinate p)) (degreeChoice p (marginCoordinate p)) (marginIndex p)
  have HE0 : FormulaSignSlotRadialRetainedTrailingGuards.Guards HN HT HA HR false indexedRadial centerRefs
      (FormulaSignSlotRadialRetainedTrailingGuards.query (context (marginChild p)) (word (marginChild p))
        (tauChoice p (marginCoordinate p)) (degreeChoice p (marginCoordinate p)) (marginIndex p)) ↔
      marginMeaningAt (indexedRadial (context (marginChild p))) v
      (tauChoice p (marginCoordinate p)) (degreeChoice p (marginCoordinate p)) (marginIndex p) := by
    unfold marginMeaningAt v
    exact HE
  have HS : indexedRadial (context (marginChild p)) = FormulaSignSlotRadialCoordinatePacket.packet
      (FormulaSignSlotRadialJointLayout.source true (header p)) (marginCoordinate p) :=
    indexed_source p (marginCoordinate p)
  rw [HS] at HE0
  have HC := marginMeaningAt_congr
    (FormulaSignSlotRadialCoordinatePacket.packet (FormulaSignSlotRadialJointLayout.source true (header p))
      (marginCoordinate p)) v (fun j => values p hv (FormulaSignSlotRadialJointLayout.column 0 j))
      (tauChoice p (marginCoordinate p)) (degreeChoice p (marginCoordinate p)) (marginIndex p) (by
        intro j hj
        rw [FormulaSignSlotRadialCoordinatePacket.root] at hj
        exact congrFun HC0 ⟨j,hj⟩)
  unfold MarginGuard marginQuery
  rw [margin_choices, margin_choices]
  change FormulaSignSlotRadialRetainedTrailingGuards.Guards HN HT HA HR false indexedRadial centerRefs
    (FormulaSignSlotRadialRetainedTrailingGuards.query (context (marginChild p)) (word p)
      (tauChoice p (marginCoordinate p)) (degreeChoice p (marginCoordinate p)) (marginIndex p)) ↔ _
  have HWrd : word (marginChild p) = word p := indexed_word p (marginCoordinate p)
  rw [←HWrd]
  exact HE0.trans HC

/-- The retained trailing query selects the actual geometric margin coordinate. -/
theorem margin_coordinate_selected (p : List Bool) :
    (FormulaSignSlotRadialEliminantInput.coordinate
      (FormulaSignSlotRadialCoordinatePacket.packet (FormulaSignSlotRadialJointLayout.source true (header p))
        (marginCoordinate p))).val = (FormulaSignSlotCenteredRadialGraph.marginIndex
          (FormulaSignSlotRadialJointLayout.source true (header p))).val := by
  rw [FormulaSignSlotRadialCoordinatePacket.selected]
  have HE : marginCoordinate p = (FormulaSignSlotMarginProjection.objectiveIndex
      (FormulaSignSlotRadialJointLayout.source true (header p))).val := by
    unfold marginCoordinate FormulaSignSlotMarginProjection.objectiveIndex
    rfl
  have HI := (FormulaSignSlotMarginProjection.objectiveIndex
    (FormulaSignSlotRadialJointLayout.source true (header p))).isLt
  have HB : marginCoordinate p ≤ FormulaSignSlotCenteredRadialGraph.N
      (FormulaSignSlotRadialJointLayout.source true (header p)) + FormulaSignSlotCenteredRadialGraph.d
      (FormulaSignSlotRadialJointLayout.source true (header p)) := by
    rw [HE]
    change (FormulaSignSlotMarginProjection.objectiveIndex
      (FormulaSignSlotRadialJointLayout.source true (header p))).val < FormulaSignSlotCenteredRadialGraph.N
      (FormulaSignSlotRadialJointLayout.source true (header p)) at HI
    omega
  rw [Nat.min_eq_left HB]
  exact HE

end LeanCanny.Encoding.FormulaSignSlotRadialJointSample
