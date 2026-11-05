/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordHeight
public import LeanCanny.Encoding.IntegralMixedSourceIntegerRecordPullbackPlanned
public import LeanCanny.Encoding.IntegralFramedBankQuery
/-! # Native controls for literal provider leaves and the complete causal script -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPlan
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFramedStepHeight
open IntegralMixedFramedCompanionUniformBits (lifted liftedPlan)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def tables := IntegralMixedCausalPlanBits.tables parameters
  (IntegralMixedSourceIntegerRecordAppend.originalRecords parameters (fun root _=>spatial root) positive (fun root _=>spatial_degree root) spatial_cap count source_cap source source_nonzero source_degree_cap)
theorem tables_native : IntegralMixedHeaderTablesBits.Access tables :=
  IntegralMixedSourceIntegerRecordAppend.tables_native parameters (fun root _=>spatial root) positive (fun root _=>spatial_degree root) spatial_cap count source_cap source source_nonzero source_degree_cap access count_unary
theorem tables_represents : IntegralMixedFramedHeaderBits.Represents parameters plan data tables :=
  IntegralMixedSourceIntegerRecordAppend.tables_represent parameters (fun root _=>spatial root) positive (fun root _=>spatial_degree root) spatial_cap count source_cap source source_nonzero source_degree_cap room source_width

noncomputable abbrev certifiedParameters := IntegralMixedFramedNormalizationBits.planned parameters (fun _=>3) factor seed
noncomputable abbrev certifiedPlan := IntegralMixedFramedNormalizationBits.plannedPlan parameters plan (fun _=>3) factor seed
noncomputable abbrev certifiedData := IntegralMixedFramedNormalizationBits.plannedData parameters plan data (fun _=>3) factor seed

theorem certifiedAccess : Access certifiedParameters :=
  IntegralMixedFramedNormalizationBits.planned_access parameters access (BinaryFn.const 3) factor_binary seed_binary
theorem certifiedInputs : FamilyInputs certifiedParameters certifiedPlan (fun _=>3) factor seed :=
  IntegralMixedFramedNormalizationBits.planned_familyInputs _ _ _ _ _ familyInputs
noncomputable def certifiedControls := IntegralMixedSourceIntegerRecordAppend.plannedControls parameters (fun root _=>spatial root) positive (fun root _=>spatial_degree root) spatial_cap count source_cap source source_nonzero source_degree_cap room source_width
  access count_unary source_access savedReaders savedReaders_native scope snapshot
  (fun _=>3) factor seed (BinaryFn.const 3) factor_binary seed_binary
theorem certifiedBounds : IntegralMixedFramedCurrentQNativeBits.Bounds certifiedParameters certifiedPlan certifiedData certifiedControls :=
  IntegralMixedSourceIntegerRecordAppend.plannedBounds parameters (fun root _=>spatial root) positive (fun root _=>spatial_degree root) spatial_cap count source_cap source source_nonzero source_degree_cap room source_width
    access count_unary source_access savedReaders savedReaders_native scope snapshot
    (fun _=>3) factor seed (BinaryFn.const 3) factor_binary seed_binary familyInputs factor_positive (fun _=>by decide)

noncomputable def certifiedCallerData := IntegralMixedFramedRootPullback.data certifiedParameters certifiedPlan certifiedData
  pairFst IntegralMixedFramedModulusPacket.extra
noncomputable def certifiedCallerControls := IntegralMixedSourceIntegerRecordPullback.plannedCallerControls parameters (fun root _=>spatial root) positive (fun root _=>spatial_degree root) spatial_cap count source_cap source source_nonzero source_degree_cap room source_width
  pairFst IntegralMixedFramedModulusPacket.extra access count_unary source_access
  pairFst_mem_FP IntegralMixedFramedModulusPacket.extra_binary savedReaders savedReaders_native scope snapshot
  (fun _=>3) factor seed (BinaryFn.const 3) factor_binary seed_binary

theorem certifiedCallerBounds : IntegralMixedFramedCurrentQNativeBits.Bounds (lifted certifiedParameters)
    (liftedPlan certifiedParameters certifiedPlan) certifiedCallerData certifiedCallerControls :=
  IntegralMixedSourceIntegerRecordPullback.plannedCallerBounds parameters (fun root _=>spatial root) positive (fun root _=>spatial_degree root) spatial_cap count source_cap source source_nonzero source_degree_cap room source_width
    pairFst IntegralMixedFramedModulusPacket.extra access count_unary source_access
    pairFst_mem_FP IntegralMixedFramedModulusPacket.extra_binary savedReaders savedReaders_native scope snapshot
    (fun _=>3) factor seed (BinaryFn.const 3) factor_binary seed_binary familyInputs factor_positive (fun _=>by decide)

theorem certifiedRepresents : IntegralMixedFramedHeaderBits.Represents certifiedParameters certifiedPlan certifiedData tables :=
  BoundedRegularIntegerCurrentQBits.represents_planned parameters plan data tables tables_represents (fun _=>3) factor seed
theorem certified_state (key : List Bool) :
    HEq ((IntegralMixedFramedHistoryFamilyBits.family certifiedParameters certifiedPlan certifiedData).state key)
      ((IntegralMixedFramedHistoryFamilyBits.family parameters plan data).state key) :=
  BoundedRegularIntegerCurrentQBits.state_planned parameters plan data (fun _=>3) factor seed key

noncomputable def bankKey (input : List Bool) := IntegralMixedFramedHistoryFamilyBits.keyAt (pairFst input)
  (fullCount (pairFst input)) []
theorem bankKey_FP : bankKey ∈ FP := mem_FP_pair pairFst_mem_FP
  (mem_FP_pair (BinaryFn.ofUnary (fullCount_unary.comp pairFst_mem_FP)).bits_mem_FP (constFn_mem_FP []))

private theorem snapshot_count (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) :
    (IntegralMixedFramedBankSnapshotBits.atKey P D H key).count = (IntegralMixedFramedHistoryFamilyBits.family P D H).birth key := rfl

theorem bank_count (input : List Bool) :
    (IntegralMixedFramedBankSnapshotBits.atKey certifiedParameters certifiedPlan certifiedData (bankKey input)).count =
      fullCount (pairFst input) := by
  rw [snapshot_count,IntegralMixedFramedHistoryFamilyBits.family_birth]
  exact IntegralMixedFramedHistoryFamilyBits.keyAt_prefix certifiedParameters (pairFst input) _ []
    (by change fullCount _ ≤ fullCount _+2+1; omega)

theorem fullCount_positive (root : List Bool) : 0<fullCount root := by
  change 0<FormulaSignSlotRadialProviderIntegerPlan.number (providerContext root)+8+_
  omega

noncomputable def bankIndex (input : List Bool) := Nat.fromBitsLE (pairSnd input) % fullCount (pairFst input)
theorem bankIndex_unary : UnaryFn bankIndex := by
  have HC : UnaryFn (fun input=>fullCount (pairFst input)) := fullCount_unary.comp pairFst_mem_FP
  have HI : BinaryFn bankIndex := (BinaryFn.fromBits pairSnd_mem_FP).mod (BinaryFn.ofUnary HC)
  refine (UnaryFn.fromBitsLE_min HI.bits_mem_FP HC).of_eq (fun q=>?_)
  rw [BinaryNatCode.encode,Nat.fromBitsLE_bits]
  exact min_eq_left (Nat.le_of_lt (Nat.mod_lt _ (fullCount_positive _)))

noncomputable def bank : IntegralFramedBankQuery.Bank where
  parameters := certifiedParameters
  plan := certifiedPlan
  data := certifiedData
  nodes _ := 3
  factor := factor
  seed := seed
  bounds := certifiedInputs
  key := bankKey
  positive input := by rw [bank_count]; exact fullCount_positive _
  coordinate input := ⟨bankIndex input,by rw [bank_count]; exact Nat.mod_lt _ (fullCount_positive _)⟩
noncomputable def bank_access : IntegralFramedBankQuery.Access bank where
  parameters := certifiedAccess
  liftedData := certifiedCallerData
  controls := certifiedCallerControls
  bounds := certifiedCallerBounds
  nodes := BinaryFn.const 3
  factor := factor_binary
  seed := seed_binary
  key := bankKey_FP
  coordinate := bankIndex_unary

end LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPlan
