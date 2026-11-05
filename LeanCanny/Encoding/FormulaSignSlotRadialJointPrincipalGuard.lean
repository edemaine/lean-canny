/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialJointIndexedContext
/-! # Native all-coordinate PSC choices on one unchanged joint word

The loop selects a coordinate in auxiliary metadata. Its node, sampler root,
word, original variables, and center references remain identical.
-/
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
  FormulaSignSlotRadialJointLayout.dimension IntegralMixedPhysicalMarkedPlan.bank slot context

-- A scan child pairs the original packet with a unary coordinate.
def tableChoice (field : ℕ) (z : List Bool) := WordList.reader (pair
  (slot field (context (pairFst z))) (BinaryNatCode.encode (pairSnd z).length))
def principalChild (z : List Bool) := indexedPacket (pair (pairFst z) (BinaryNatCode.encode (pairSnd z).length))
noncomputable def principalQuery (z : List Bool) := FormulaSignSlotRadialRetainedPrincipalSelection.query
  (context (principalChild z)) (word (pairFst z)) (Nat.fromBitsLE (tableChoice 0 z))
    (Nat.fromBitsLE (tableChoice 1 z)) (Nat.fromBitsLE (tableChoice 2 z))

theorem tableChoice_FP (field : ℕ) : tableChoice field ∈ FP := by
  have HC : (fun z => context (pairFst z)) ∈ FP := mem_FP_comp pairFst_mem_FP context_FP
  have HS : (fun z => slot field (context (pairFst z))) ∈ FP :=
    mem_FP_comp (f := fun z => context (pairFst z)) (g := slot field) HC (slot_FP field)
  exact mem_FP_comp (mem_FP_pair HS (BinaryFn.ofUnary (UnaryFn.length pairSnd_mem_FP)).bits_mem_FP)
    WordList.reader_FP

theorem principalChild_FP : principalChild ∈ FP := mem_FP_comp
  (mem_FP_pair pairFst_mem_FP (BinaryFn.ofUnary (UnaryFn.length pairSnd_mem_FP)).bits_mem_FP) indexedPacket_FP

theorem principalQuery_FP : principalQuery ∈ FP := by
  have HC : (fun z => context (principalChild z)) ∈ FP := mem_FP_comp principalChild_FP context_FP
  have HW : (fun z => word (pairFst z)) ∈ FP := mem_FP_comp (f := pairFst) (g := word) pairFst_mem_FP word_FP
  have H0 := (BinaryFn.fromBits (tableChoice_FP 0)).bits_mem_FP
  have H1 := (BinaryFn.fromBits (tableChoice_FP 1)).bits_mem_FP
  have H2 := (BinaryFn.fromBits (tableChoice_FP 2)).bits_mem_FP
  exact mem_FP_pair (mem_FP_pair HC HW) (mem_FP_pair H0 (mem_FP_pair H1 (mem_FP_pair H2 (constFn_mem_FP []))))

noncomputable def PrincipalAt (z : List Bool) : Prop :=
  FormulaSignSlotRadialRetainedPrincipalGuards.Guards HN HT HA HR false indexedRadial centerRefs (principalQuery z)
noncomputable def PrincipalGuard (p : List Bool) : Prop :=
  ∀ i < FormulaSignSlotRadialJointLayout.spatialCount (header p), PrincipalAt (pair p (List.replicate i true))

theorem principal_at_evaluator : SpaceFunction (fun z => [decide (PrincipalAt z)]) :=
  (FormulaSignSlotRadialRetainedPrincipalGuards.evaluator HN HT HA HR false indexedRadial centerRefs
    indexedRadial_FP centerRefs_FP).precompose principalQuery principalQuery_FP

theorem principal_guard_evaluator : SpaceFunction (fun p => [decide (PrincipalGuard p)]) := by
  have HC := FormulaSignSlotRadialJointLayout.spatialCount_unary.comp header_FP
  exact (principal_at_evaluator.forall_unary HC).congr (funext fun p => by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [PrincipalGuard, List.cons.injEq, and_true, decide_eq_true_eq])

def tauChoice (p : List Bool) (i : ℕ) := Nat.fromBitsLE (WordList.get (slot 0 (context p)) i)
def degreeChoice (p : List Bool) (i : ℕ) := Nat.fromBitsLE (WordList.get (slot 1 (context p)) i)
def pscChoice (p : List Bool) (i : ℕ) := Nat.fromBitsLE (WordList.get (slot 2 (context p)) i)

private theorem tableChoice_child (field : ℕ) (p : List Bool) (i : ℕ) :
    tableChoice field (pair p (List.replicate i true)) = WordList.get (slot field (context p)) i := by
  simp only [tableChoice, pairFst_pair, pairSnd_pair, List.length_replicate, WordList.reader_packet]
private theorem principalChild_child (p : List Bool) (i : ℕ) :
    principalChild (pair p (List.replicate i true)) = indexed p i := by
  simp only [principalChild, pairFst_pair, pairSnd_pair, List.length_replicate, indexed]
private theorem principalQuery_child (p : List Bool) (i : ℕ) :
    principalQuery (pair p (List.replicate i true)) = FormulaSignSlotRadialRetainedPrincipalSelection.query
      (context (indexed p i)) (word (indexed p i)) (tauChoice p i) (degreeChoice p i) (pscChoice p i) := by
  simp only [principalQuery, principalChild_child, pairFst_pair, tableChoice_child,
    tauChoice, degreeChoice, pscChoice, indexed_word]

noncomputable def principalMeaningAt (c : List Bool) (v : ℕ → ℝ) (tau D k : ℕ) : Prop :=
  FormulaSignSlotRadialCenterSquarefreeSelection.Guards c (fun j => v j.val) tau D k
attribute [local irreducible] principalMeaningAt

private theorem principalMeaningAt_congr (c : List Bool) (v w : ℕ → ℝ) (tau D k : ℕ)
    (h : ∀ j < FormulaSignSlotSource.dimension (pairFst c), v j = w j) :
    principalMeaningAt c v tau D k ↔ principalMeaningAt c w tau D k := by
  have HE : (fun j : Fin (FormulaSignSlotSource.dimension (pairFst c)) => v j.val) =
      (fun j => w j.val) := funext (fun j => h j.val j.isLt)
  unfold principalMeaningAt
  rw [HE]

noncomputable def PrincipalMeaning (p : List Bool) (hv : Valid p) : Prop :=
  ∀ i < FormulaSignSlotRadialJointLayout.spatialCount (header p),
    principalMeaningAt
      (FormulaSignSlotRadialCoordinatePacket.packet (FormulaSignSlotRadialJointLayout.source true (header p)) i)
      (fun j => values p hv (FormulaSignSlotRadialJointLayout.column 0 j))
      (tauChoice p i) (degreeChoice p i) (pscChoice p i)

theorem principal_at_actual (p : List Bool) (hv : Valid p) (i : ℕ) :
    PrincipalAt (pair p (List.replicate i true)) ↔
      principalMeaningAt
        (FormulaSignSlotRadialCoordinatePacket.packet (FormulaSignSlotRadialJointLayout.source true (header p)) i)
        (fun j => values p hv (FormulaSignSlotRadialJointLayout.column 0 j))
        (tauChoice p i) (degreeChoice p i) (pscChoice p i) := by
  have HV := indexed_valid p i hv
  have HW : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input HN HT HA HR false)
      (context (indexed p i)) (word (indexed p i)) := full_valid (indexed p i) HV
  let v := FormulaSignSlotRadialRetainedPrincipalTest.center HN HT HA HR false centerRefs
    (context (indexed p i)) (word (indexed p i)) HW
  have HC0 : (fun j : Fin (FormulaSignSlotRadialJointLayout.centerCount (header (indexed p i))) => v j.val) =
      FormulaSignSlotRadialJointGeometry.center (header (indexed p i)) (values (indexed p i) HV) := by
    funext j
    exact retained_center (indexed p i) HV j
  rw [indexed_header, indexed_values] at HC0
  have HE := FormulaSignSlotRadialRetainedPrincipalSelection.guards_packet HN HT HA HR false
    indexedRadial centerRefs (context (indexed p i)) (word (indexed p i)) HW
      (tauChoice p i) (degreeChoice p i) (pscChoice p i)
  have HE0 : FormulaSignSlotRadialRetainedPrincipalGuards.Guards HN HT HA HR false indexedRadial centerRefs
      (FormulaSignSlotRadialRetainedPrincipalSelection.query (context (indexed p i)) (word (indexed p i))
        (tauChoice p i) (degreeChoice p i) (pscChoice p i)) ↔
      principalMeaningAt (indexedRadial (context (indexed p i))) v
        (tauChoice p i) (degreeChoice p i) (pscChoice p i) := by
    unfold principalMeaningAt
    exact HE
  rw [indexed_source] at HE0
  have HC := principalMeaningAt_congr
    (FormulaSignSlotRadialCoordinatePacket.packet (FormulaSignSlotRadialJointLayout.source true (header p)) i)
    v (fun j => values p hv (FormulaSignSlotRadialJointLayout.column 0 j))
    (tauChoice p i) (degreeChoice p i) (pscChoice p i) (by
      intro j hj
      rw [FormulaSignSlotRadialCoordinatePacket.root] at hj
      exact congrFun HC0 ⟨j,hj⟩)
  unfold PrincipalAt
  rw [principalQuery_child]
  exact HE0.trans HC

theorem principal_guard_actual (p : List Bool) (hv : Valid p) : PrincipalGuard p ↔ PrincipalMeaning p hv :=
  forall_congr' (fun i => forall_congr' (fun _ => principal_at_actual p hv i))

end LeanCanny.Encoding.FormulaSignSlotRadialJointSample
