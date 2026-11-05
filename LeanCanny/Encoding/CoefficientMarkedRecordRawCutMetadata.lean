/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordFullCutHead
public import LeanCanny.Encoding.IntegralFramedTraceCutTask
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordBank
/-! # Literal certified raw-cut tasks retain their original prefix metadata -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordRawCutMetadata
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask Polynomial
open IntegralMixedAuxiliaryMarkedRecordPlan (parameters plan data certifiedParameters certifiedPlan certifiedData)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

def descriptor (ctx : List Bool) (k : ℕ) := pair ctx
  (pair (List.replicate (CoefficientMarkedRecordCutSource.birth (n := n) ctx k) true) [])
def terminal (ctx : List Bool) := CoefficientMarkedRecordRowLayout.key (n := n) ctx
  (IntegralMixedCausalRecordPlanBits.count ctx) []

private theorem planned_birth (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (L F C : List Bool → ℕ) (key : List Bool) :
    (IntegralMixedFramedHistoryFamilyBits.family (IntegralMixedFramedNormalizationBits.planned P L F C)
      (IntegralMixedFramedNormalizationBits.plannedPlan P D L F C)
      (IntegralMixedFramedNormalizationBits.plannedData P D H L F C)).birth key =
      (IntegralMixedFramedHistoryFamilyBits.family P D H).birth key := rfl

private theorem planned_degree (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (L F C : List Bool → ℕ) (key : List Bool) :
    (IntegralMixedFramedHistoryFamilyBits.family (IntegralMixedFramedNormalizationBits.planned P L F C)
      (IntegralMixedFramedNormalizationBits.plannedPlan P D L F C)
      (IntegralMixedFramedNormalizationBits.plannedData P D H L F C)).degree key =
      (IntegralMixedFramedHistoryFamilyBits.family P D H).degree key := by
  exact congrArg (fun s => s.degree) (IntegralMixedFramedCutPlanning.selection P D H L F C key)

variable {R : List Bool → ℕ} (hR : BinaryFn R)
local notation "PC" => certifiedParameters hn ht ha hR
local notation "DC" => certifiedPlan hn ht ha hR
local notation "HC" => certifiedData hn ht ha hR
local notation "G" => IntegralMixedFramedHistoryFamilyBits.family PC DC HC

noncomputable def parent (ctx : List Bool) (k : ℕ) := IntegralFramedTraceCutTask.task PC (descriptor (n := n) ctx k)

attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedSourceIntegerRecordAppend.plan IntegralMixedSourceIntegerRecordAppend.data
  IntegralMixedAuxiliaryMarkedIntegerPlan.seed

theorem raw_birth_lt_cap (ctx : List Bool) (k : ℕ) (hk : k < IntegralMixedCausalRecordPlanBits.count ctx) :
    CoefficientMarkedRecordCutSource.birth (n := n) ctx k < (PC).cap ctx := by
  have HH := IntegralMixedAuxiliaryMarkedRecordPlan.room hn ht ha ctx
  rw [CoefficientMarkedRecordCutSource.birth, CoefficientMarkedRecordActual.codes_length,
    CoefficientMarkedPreludeActual.indices_length]
  change IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx+8+k < (parameters hn ht ha).cap ctx
  omega

theorem parent_root (ctx : List Bool) (k : ℕ) : RankedHistoryTask.root (parent hn ht ha hR ctx k) = ctx :=
  (IntegralFramedTraceCutTask.task_root PC _).trans (pairFst_pair _ _)

theorem parent_birth (ctx : List Bool) (k : ℕ) (hk : k < IntegralMixedCausalRecordPlanBits.count ctx) :
    birth PC (parent hn ht ha hR ctx k) = CoefficientMarkedRecordCutSource.birth (n := n) ctx k := by
  have HB := raw_birth_lt_cap hn ht ha hR ctx k hk
  have HR : IntegralFramedTraceCutTask.stage (descriptor (n := n) ctx k) ≤
      birthCap PC (pairFst (descriptor (n := n) ctx k)) := by
    simp only [descriptor, IntegralFramedTraceCutTask.stage_packet, List.length_replicate, pairFst_pair, birthCap]
    omega
  exact (IntegralFramedTraceCutTask.task_birth PC _ HR).trans (by
    simp only [descriptor, IntegralFramedTraceCutTask.stage_packet, List.length_replicate])

theorem parent_saved (ctx : List Bool) (k : ℕ) (hk : k < IntegralMixedCausalRecordPlanBits.count ctx) :
    IntegralMixedVirtualTaskBits.saved PC (parent hn ht ha hR ctx k) =
      CoefficientMarkedRecordRowLayout.key (n := n) ctx k (BinaryNatCode.encode 2) := by
  unfold IntegralMixedVirtualTaskBits.saved
  rw [parent_root, parent_birth hn ht ha hR ctx k hk]
  have HX := IntegralFramedTraceCutTask.task_context PC (descriptor (n := n) ctx k)
  change get PC .slot15 (parent hn ht ha hR ctx k) = 2 at HX
  rw [HX]
  simp only [CoefficientMarkedRecordRowLayout.key, CoefficientMarkedRecordCutSource.birth,
    CoefficientMarkedRecordActual.codes_length]

theorem parent_active (ctx : List Bool) (k : ℕ) (hk : k < IntegralMixedCausalRecordPlanBits.count ctx) :
    IntegralMixedFramedFullCutProbeBits.Active PC (parent hn ht ha hR ctx k) := by
  constructor
  · unfold IntegralMixedVirtualCaps.valid
    rw [parent_root, parent_birth hn ht ha hR ctx k hk]
    exact raw_birth_lt_cap hn ht ha hR ctx k hk
  · have HX := IntegralFramedTraceCutTask.task_context PC (descriptor (n := n) ctx k)
    change get PC .slot15 (parent hn ht ha hR ctx k) = 2 at HX
    change 2 ≤ get PC .slot15 (parent hn ht ha hR ctx k) ∧ get PC .slot15 (parent hn ht ha hR ctx k) ≤ 4
    rw [HX]
    decide

theorem parent_arity (ctx : List Bool) (k : ℕ) (hk : k < IntegralMixedCausalRecordPlanBits.count ctx) :
    IntegralMixedFramedFullCutHead.arity PC DC HC (fun _ => parent hn ht ha hR ctx k) [] =
      CoefficientMarkedRecordCutSource.birth (n := n) ctx k := by
  change (G).birth (IntegralMixedVirtualTaskBits.saved PC (parent hn ht ha hR ctx k)) = _
  rw [parent_saved hn ht ha hR ctx k hk]
  have HB := planned_birth (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R)
    (fun _ => 3) (IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR)
    (CoefficientMarkedRecordRowLayout.key (n := n) ctx k (BinaryNatCode.encode 2))
  exact HB.trans (CoefficientMarkedRecordRows.family_birth hn ht ha ctx R k hk.le _).symm

theorem declared_degree (ctx : List Bool) (k : ℕ) (hk : k < IntegralMixedCausalRecordPlanBits.count ctx)
    (hc : IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code ctx k) = false) :
    (G).degree (IntegralMixedVirtualTaskBits.saved PC (parent hn ht ha hR ctx k)) =
      (CoefficientMarkedRecordCutSource.cut hn ht ha ctx k).degree := by
  rw [parent_saved hn ht ha hR ctx k hk]
  exact (planned_degree (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R)
    (fun _ => 3) (IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR) _).trans
      (CoefficientMarkedRecordCutSelection.degree_eq hn ht ha ctx R k hk hc _)

theorem terminal_count (ctx : List Bool) :
    (IntegralMixedFramedBankSnapshotBits.atKey PC DC HC (terminal (n := n) ctx)).count =
      IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n ctx := by
  have HK : IntegralMixedAuxiliaryMarkedRecordPlan.bankKey n (pair ctx []) = terminal (n := n) ctx := by
    simp only [IntegralMixedAuxiliaryMarkedRecordPlan.bankKey, terminal, CoefficientMarkedRecordRowLayout.key,
      pairFst_pair, IntegralMixedAuxiliaryMarkedRecordPlan.fullCount, CoefficientMarkedPreludeActual.indices_length]
  have HB := IntegralMixedAuxiliaryMarkedRecordPlan.bank_count hn ht ha hR (pair ctx [])
  simpa only [HK, pairFst_pair] using HB

theorem terminal_valid (ctx : List Bool) (k : ℕ) (hk : k < IntegralMixedCausalRecordPlanBits.count ctx) :
    IntegralMixedFramedFullCutTerminalHead.Valid PC DC HC
      (fun _ => parent hn ht ha hR ctx k) (fun _ => terminal (n := n) ctx) [] := by
  change IntegralMixedFramedFullCutHead.arity PC DC HC (fun _ => parent hn ht ha hR ctx k) [] ≤
    (IntegralMixedFramedBankSnapshotBits.atKey PC DC HC (terminal (n := n) ctx)).count
  rw [parent_arity hn ht ha hR ctx k hk, terminal_count]
  simp only [CoefficientMarkedRecordCutSource.birth, CoefficientMarkedRecordActual.codes_length,
    CoefficientMarkedPreludeActual.indices_length, IntegralMixedAuxiliaryMarkedRecordPlan.fullCount]
  omega

theorem suffix_newer (ctx : List Bool) (k : ℕ) (hk : k < IntegralMixedCausalRecordPlanBits.count ctx) :
    IntegralMixedFramedFullCutTerminalHead.newer PC DC HC
      (fun _ => parent hn ht ha hR ctx k) (fun _ => terminal (n := n) ctx) [] =
      IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n ctx-CoefficientMarkedRecordCutSource.birth (n := n) ctx k+1 := by
  unfold IntegralMixedFramedFullCutTerminalHead.newer IntegralMixedFramedFullCutTerminalHead.count
  rw [parent_arity hn ht ha hR ctx k hk, terminal_count]

theorem degree_clip (ctx : List Bool) (k : ℕ) (hk : k < IntegralMixedCausalRecordPlanBits.count ctx)
    (hc : IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code ctx k) = false) :
    IntegralMixedFramedFullCutHead.degree PC (fun _ => parent hn ht ha hR ctx k)
      (fun _ => (CoefficientMarkedRecordCutSource.cut hn ht ha ctx k).degree) [] =
      (CoefficientMarkedRecordCutSource.cut hn ht ha ctx k).degree := by
  unfold IntegralMixedFramedFullCutHead.degree
  apply min_eq_left
  let key := IntegralMixedVirtualTaskBits.saved PC (parent hn ht ha hR ctx k)
  have HH := ((G).degree_bound key).trans ((G).scalar_cap key)
  have HS := IntegralMixedValueTaskBounds.scalar_le_root_cap PC G
    (IntegralMixedFramedHistoryFamilyBits.geometry PC DC HC) (parent hn ht ha hR ctx k)
  have HT := HH.trans HS
  change (G).degree (IntegralMixedVirtualTaskBits.saved PC (parent hn ht ha hR ctx k)) ≤ _ at HT
  rw [declared_degree hn ht ha hR ctx k hk hc] at HT
  exact HT

end LeanCanny.Encoding.CoefficientMarkedRecordRawCutMetadata
