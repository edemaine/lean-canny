/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPlan
/-! # Source-only height bounds for the complete provider record sequence -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPlan
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFramedStepHeight
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotRadialProviderIntegerSource.source FormulaSignSlotRadialExternalCoordinates.source

noncomputable def readers := FormulaSignSlotRadialProviderIntegerPlan.readers.comp providerContext
theorem readers_native : readers.PolyTime := FormulaSignSlotRadialProviderIntegerPlan.readers_native.comp providerContext_FP
noncomputable def savedReaders := readers.comp pairFst
theorem savedReaders_native : savedReaders.PolyTime := readers_native.comp pairFst_mem_FP
private theorem source_comp (R : BoundedFullWriter.Readers) (f : List Bool → List Bool) (key : List Bool) :
    HEq (BoundedRegularLowModularTerm.source R (f key)) (BoundedRegularLowModularTerm.source (R.comp f) key) := HEq.rfl

theorem spatial_readers (root : List Bool) : HEq (spatial root) (BoundedRegularLowModularTerm.source readers root) :=
  source_comp FormulaSignSlotRadialProviderIntegerPlan.readers providerContext root

theorem snapshot : BoundedRegularFramedOriginalBits.Snapshot parameters plan savedReaders where
  ambient _ := rfl
  source key := (heq_of_eq (instruction_source key)).trans
    ((spatial_readers (pairFst key)).trans (source_comp readers pairFst key))

theorem scope (key : List Bool) :
    (LeanCanny.ETR.TermView.term (savedReaders.source key)).arity ≤ savedReaders.dim key := by
  simpa only [savedReaders,readers,BoundedFullWriter.Readers.comp,
    FormulaSignSlotRadialProviderIntegerPlan.readers,FormulaSignSlotRadialExternalPrelude.readers,
    BoundedRegularLowCoefficient.readers,Function.comp_apply,LeanCanny.ETR.TermView.term_toBits,
    FormulaSignSlotRadialExternalPrelude.number,FormulaSignSlotRadialExternalContext.number] using
    LeanCanny.Connectivity.CanonicalAuxiliaryCandidateCover.equation_scope
      (FormulaSignSlotRadialExternalPrelude.original (providerContext (pairFst key)))

noncomputable def integerMass := IntegerPolynomialFiniteMassEnvelope.height source source_access count count_unary
noncomputable def seed (root : List Bool) := integerMass root+BoundedRegularLowHeight.height readers root
noncomputable def factor (root : List Bool) := parameters.cap root+1

theorem seed_binary : BinaryFn seed :=
  (IntegerPolynomialFiniteMassEnvelope.height_binary source source_access count count_unary).add
    (BoundedRegularLowHeight.height_binary readers_native)
theorem factor_binary : BinaryFn factor := BinaryFn.ofUnary (access.cap.add (UnaryFn.const 1))
theorem factor_positive (root : List Bool) : 1≤factor root := Nat.succ_le_succ (Nat.zero_le _)

private theorem reader_instruction_bounds (R : BoundedFullWriter.Readers) (r : List Bool)
    {n B W D C F : ℕ} (S : SpatialSource n) (hn : n=R.dim r+3)
    (hS : HEq S (BoundedRegularLowModularTerm.source R r))
    (hcap : PurePowerReductionBounds.dimension (n+1) S.degree≤2^B)
    (hd : S.degree=D) (hw : D.size≤W)
    (ha : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) D≤2^B)
    (hs : BoundedRegularLowHeight.height R r≤C) (hf : 1≤F) :
    InstructionBounds (C+1) F W D 3
      (⟨S,hcap,IntegralMixedFullHistoryScript.defaultCommand⟩ : Instruction n B) := by
  subst n
  have ES := eq_of_heq hS
  subst S
  have HE : C+1≤F*(C+1)+1 := by nlinarith
  constructor
  · intro e
    exact (BoundedRegularLowHeight.coefficient R r e).trans
      (Nat.pow_le_pow_right (by decide) (hs.trans (by omega)))
  · change (BoundedRegularLowModularTerm.source R r).leading.natAbs.size≤_
    rw [BoundedRegularLowHeight.leading R]
    have HL : BoundedFullWriter.regularizationExponent R r+1≤BoundedRegularLowHeight.height R r := by
      unfold BoundedRegularLowHeight.height
      omega
    omega
  · rw [hd]
    exact hw
  · exact hd.le
  · rw [hd]
    exact ha
  · intro k
    rw [Polynomial.coeff_X]
    split_ifs
    · simpa only [Int.natAbs_one] using (Nat.one_le_two_pow (n:=F*(C+1)+1))
    · exact Nat.zero_le _

theorem sourceBounds (root : List Bool) :
    InstructionBounds (seed root+1) (factor root) (parameters.sourceWidth root) (parameters.degree root) 3
      (⟨spatial root,source_cap root,IntegralMixedFullHistoryScript.defaultCommand⟩ :
        Instruction (parameters.ambient root) (parameters.width root)) :=
  reader_instruction_bounds readers root (spatial root) rfl (spatial_readers root)
    (source_cap root) (spatial_degree root) (source_width root) (spatial_cap root) (Nat.le_add_left _ _) (factor_positive root)

theorem familyInputs : FamilyInputs parameters plan (fun _=>3) factor seed := by
  apply IntegralMixedSourceIntegerRecordAppend.familyInputs parameters (fun root _=>spatial root)
    positive (fun root _=>spatial_degree root) spatial_cap count source_cap source source_nonzero source_degree_cap room
    (fun _=>3) factor seed
  · exact fun _=>le_rfl
  · exact fun root _=>sourceBounds root
  · intro root i hi
    have H := IntegerPolynomialFiniteMassEnvelope.mass_le source source_access count count_unary root i hi
    change _≤ integerMass root at H
    have HS : integerMass root≤seed root := Nat.le_add_right _ _
    have HF := factor_positive root
    nlinarith
  · intro root
    have HF := factor_positive root
    nlinarith
  · exact fun _=>le_rfl

end LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPlan
