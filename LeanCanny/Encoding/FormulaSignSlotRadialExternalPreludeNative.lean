/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialExternalPrelude
public import LeanCanny.Encoding.BoundedRegularLowHeight
public import LeanCanny.Algebra.IntegralMixedSourceIntegerBounds
public import LeanCanny.Algebra.BoundedRegularIntegerCurrentQRootControls
/-! # Actual native controls for the external coordinate prelude

Only the original implicit coordinate Source and literal old spatial term
are charged. Planning rebuilds exact caller-modulus controls and preserves
the raw state at the same key; no external word is reused as a replay word.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialExternalPreludeNative
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Connectivity LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFramedStepHeight
open IntegralMixedFramedCompanionUniformBits (lifted liftedPlan)
open FormulaSignSlotRadialExternalPrelude
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def integerMass := IntegerPolynomialFiniteMassEnvelope.height source source_access count count_unary
noncomputable def seed (ctx : List Bool) := integerMass ctx+BoundedRegularLowHeight.height readers ctx

theorem seed_binary : BinaryFn seed :=
  (IntegerPolynomialFiniteMassEnvelope.height_binary source source_access count count_unary).add
    (BoundedRegularLowHeight.height_binary readers_native)

theorem default_height (root : List Bool) :
    InstructionBounds (seed root+1) 1 (parameters.sourceWidth root) (parameters.degree root) 1
      (IntegralMixedFramedHistoryFamilyBits.defaultInstruction parameters plan root) := by
  dsimp only [IntegralMixedFramedHistoryFamilyBits.defaultInstruction,plan,IntegralMixedSourceIntegerPrelude.plan]
  have HS : BoundedRegularLowHeight.height readers root≤seed root := Nat.le_add_left _ _
  constructor
  · intro e
    exact (BoundedRegularLowHeight.coefficient readers root e).trans
      (Nat.pow_le_pow_right (by decide) (by omega))
  · change (BoundedRegularLowModularTerm.source readers root).leading.natAbs.size≤_
    rw [BoundedRegularLowHeight.leading readers]
    have HL : BoundedFullWriter.regularizationExponent readers root+1≤BoundedRegularLowHeight.height readers root := by
      unfold BoundedRegularLowHeight.height
      omega
    omega
  · rw [spatial_degree]
    exact le_rfl
  · rw [spatial_degree]
  · rw [spatial_degree]
    exact source_cap root
  · intro k
    rw [Polynomial.coeff_X]
    split_ifs
    · simpa only [Int.natAbs_one] using (Nat.one_le_two_pow (n:=1*(seed root+1)+1))
    · exact Nat.zero_le _

theorem familyInputs : FamilyInputs parameters plan (fun _=>1) (fun _=>1) seed := by
  apply IntegralMixedSourceIntegerPrelude.family_inputs
  · exact default_height
  · intro root j hj
    have H:=IntegerPolynomialFiniteMassEnvelope.mass_le source source_access count count_unary root j hj
    change _ ≤ integerMass root at H
    unfold seed
    omega

noncomputable def originalSyntax : BoundedRegularIntegerCurrentQBits.Original parameters plan data where
  regular := savedReaders
  native := savedReaders_native
  scope key := by
    simpa only [savedReaders,BoundedFullWriter.Readers.comp,readers,BoundedRegularLowCoefficient.readers,
      Function.comp_apply,TermView.term_toBits,number,FormulaSignSlotRadialExternalContext.number] using
      CanonicalAuxiliaryCandidateCover.equation_scope (original (pairFst key))
  snapshot := snapshot
  zero := IntegralMixedSourceIntegerPrelude.zeroRules _ _ _ _ _ _ _ _ _ _ _
  integer := IntegralMixedSourceIntegerPrelude.source parameters source count
  integer_native := IntegralMixedSourceIntegerPrelude.native_access parameters access source source_access count_unary
  query := id
  query_FP := id_mem_FP
  integer_eq := IntegralMixedSourceIntegerPrelude.polynomial _ _ _ _ _ _ _ _ _

noncomputable abbrev certifiedParameters := IntegralMixedFramedNormalizationBits.planned parameters (fun _=>1) (fun _=>1) seed
noncomputable abbrev certifiedPlan := IntegralMixedFramedNormalizationBits.plannedPlan parameters plan (fun _=>1) (fun _=>1) seed
noncomputable abbrev certifiedData := IntegralMixedFramedNormalizationBits.plannedData parameters plan data (fun _=>1) (fun _=>1) seed

theorem certifiedAccess : Access certifiedParameters :=
  IntegralMixedFramedNormalizationBits.planned_access parameters access (BinaryFn.const 1) (BinaryFn.const 1) seed_binary

theorem certifiedInputs : FamilyInputs certifiedParameters certifiedPlan (fun _=>1) (fun _=>1) seed :=
  IntegralMixedFramedNormalizationBits.planned_familyInputs _ _ _ _ _ familyInputs

noncomputable def certifiedCallerData := IntegralMixedFramedRootPullback.data certifiedParameters certifiedPlan certifiedData
  pairFst IntegralMixedFramedModulusPacket.extra

theorem certifiedRepresents : IntegralMixedFramedHeaderBits.Represents certifiedParameters certifiedPlan certifiedData tables :=
  BoundedRegularIntegerCurrentQBits.represents_planned parameters plan data tables tables_represents (fun _=>1) (fun _=>1) seed

noncomputable def certifiedCallerControls :=
  BoundedRegularIntegerCurrentQBits.pullbackControls certifiedParameters certifiedAccess certifiedPlan certifiedData
    (originalSyntax.planned (fun _=>1) (fun _=>1) seed) tables tables_native certifiedRepresents
    pairFst pairFst_mem_FP IntegralMixedFramedModulusPacket.extra IntegralMixedFramedModulusPacket.extra_binary
    (fun _=>1) (fun _=>1) seed (BinaryFn.const 1) (BinaryFn.const 1) seed_binary

theorem certifiedCallerBounds : IntegralMixedFramedCurrentQNativeBits.Bounds (lifted certifiedParameters)
    (liftedPlan certifiedParameters certifiedPlan) certifiedCallerData certifiedCallerControls :=
  BoundedRegularIntegerCurrentQBits.pullbackBounds certifiedParameters certifiedAccess certifiedPlan certifiedData
    (originalSyntax.planned (fun _=>1) (fun _=>1) seed) tables tables_native certifiedRepresents
    pairFst pairFst_mem_FP IntegralMixedFramedModulusPacket.extra IntegralMixedFramedModulusPacket.extra_binary
    (fun _=>1) (fun _=>1) seed (BinaryFn.const 1) (BinaryFn.const 1) seed_binary
    certifiedInputs (fun _=>le_rfl) (fun _=>le_rfl)
    (IntegralMixedFramedNormalizationBits.planned_budget parameters (fun _=>1) (fun _=>1) seed)

theorem certified_state (key : List Bool) :
    HEq ((IntegralMixedFramedHistoryFamilyBits.family certifiedParameters certifiedPlan certifiedData).state key)
      ((IntegralMixedFramedHistoryFamilyBits.family parameters plan data).state key) :=
  BoundedRegularIntegerCurrentQBits.state_planned parameters plan data (fun _=>1) (fun _=>1) seed key

end LeanCanny.Encoding.FormulaSignSlotRadialExternalPreludeNative
