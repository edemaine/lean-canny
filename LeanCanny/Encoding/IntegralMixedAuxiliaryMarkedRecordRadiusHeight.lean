/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRadiusGrowth
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordSpace
public import LeanCanny.Encoding.BoundedRegularRadiusLowGrowth
public import LeanCanny.Computation.PolyTimeBinaryRange

/-! # Affine radius ceilings for the actual marked causal record bank

An explicit finite sum replaces the resource envelope only in this proof.
The actual plan, decoded records, and previously constructed controllers stay fixed.
-/

@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordRadiusHeight
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedFramedStepHeight IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedAuxiliaryMarkedIntegerSource (number original)
open IntegralMixedAuxiliaryMarkedRecordPlan (parameters plan data access factor)
open IntegralMixedAuxiliaryMarkedRadiusModel (massZero massOne)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n : List Bool → ℕ} {t : List Bool → Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

def leafSum (f : List Bool → ℕ) (root : List Bool) : ℕ :=
  ∑ i ∈ Finset.range (number n root + 8), f (pair root (BinaryNatCode.encode i))

include hn in
private theorem leafSum_binary {f : List Bool → ℕ} (hf : BinaryFn f) : BinaryFn (leafSum (n := n) f) := by
  have HI := hf.comp (mem_FP_pair pairFst_mem_FP (BinaryFn.ofUnary UnaryFn.index).bits_mem_FP)
  have HS := BinaryFn.sum ((IntegralMixedAuxiliaryMarkedIntegerSource.number_unary hn).add (UnaryFn.const 8)) HI
  exact HS.of_eq (fun root => by
    simp only [Function.comp_apply, pairFst_pair, pairSnd_pair, List.length_replicate, leafSum])

private theorem leaf_le_sum (f : List Bool → ℕ) (root : List Bool) (i : ℕ) (hi : i < number n root + 8) :
    f (pair root (BinaryNatCode.encode i)) ≤ leafSum (n := n) f root :=
  by
    unfold leafSum
    exact Finset.single_le_sum (f := fun j => f (pair root (BinaryNatCode.encode j))) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hi)

noncomputable def seedSlope (root : List Bool) : ℕ :=
  leafSum (n := n) (massOne hn ht ha) root +
    BoundedRegularRadiusLowModel.heightSlope (number n root) (t (original root)).toData.size

noncomputable def seedOffset (root : List Bool) : ℕ :=
  leafSum (n := n) (massZero hn ht ha) root +
    BoundedRegularRadiusLowModel.heightOffset (number n root) (t (original root)).toData.size (t (original root)).toData.size

noncomputable def seed (R : List Bool → ℕ) (root : List Bool) : ℕ :=
  seedSlope hn ht ha root * R root + seedOffset hn ht ha root

include ht in
private theorem termSize_binary : BinaryFn (fun root => (t (original root)).toData.size) :=
  BinaryFn.ofUnary ((AuxiliaryCandidateRegularLift.allowance_unary ht).comp IntegralMixedAuxiliaryMarkedIntegerPlan.original_FP)

theorem seedSlope_binary : BinaryFn (seedSlope hn ht ha) :=
  (leafSum_binary hn (IntegralMixedAuxiliaryMarkedRadiusModel.massOne_binary hn ht ha)).add
    (BoundedRegularRadiusLowModel.heightSlope_binary (IntegralMixedAuxiliaryMarkedIntegerSource.number_unary hn)
      (termSize_binary ht))

theorem seedOffset_binary : BinaryFn (seedOffset hn ht ha) :=
  (leafSum_binary hn (IntegralMixedAuxiliaryMarkedRadiusModel.massZero_binary hn ht ha)).add
    (BoundedRegularRadiusLowModel.heightOffset_binary (IntegralMixedAuxiliaryMarkedIntegerSource.number_unary hn)
      (termSize_binary ht) (termSize_binary ht))

private theorem low_height_affine (R : List Bool → ℕ) (root : List Bool) :
    BoundedRegularLowHeight.height (IntegralMixedAuxiliaryMarkedIntegerPlan.readers n t R) root =
      BoundedRegularRadiusLowModel.heightSlope (number n root) (t (original root)).toData.size * R root +
        BoundedRegularRadiusLowModel.heightOffset (number n root) (t (original root)).toData.size (t (original root)).toData.size := by
  simp only [BoundedRegularLowHeight.height, BoundedRegularLowHeight.lowMass,
    IntegralMixedAuxiliaryMarkedIntegerPlan.readers, BoundedRegularLowCoefficient.readers,
    BoundedFullWriter.regularizationExponent, BoundedFullWriter.size, BoundedSourceWriter.regularizationExponent,
    BoundedSourceWriter.size, BoundedFullWriter.controls, Function.comp_apply, TermView.term_toBits]
  exact BoundedRegularRadiusLowModel.native_height_affine _ _ _ _

private theorem low_height_le (R : List Bool → ℕ) (root : List Bool) :
    BoundedRegularLowHeight.height (IntegralMixedAuxiliaryMarkedIntegerPlan.readers n t R) root ≤ seed hn ht ha R root := by
  rw [low_height_affine]
  unfold seed seedSlope seedOffset
  nlinarith

theorem integer_mass_le (R : List Bool → ℕ) (root : List Bool) (i : ℕ) (hi : i < number n root + 8) :
    (IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R).mass (pair root (BinaryNatCode.encode i)) ≤
      seed hn ht ha R root := by
  have H := IntegralMixedAuxiliaryMarkedRadiusModel.nativeMass_le hn ht ha R (pair root (BinaryNatCode.encode i))
  simp only [pairFst_pair] at H
  have H0 := leaf_le_sum (massZero hn ht ha) root i hi
  have H1 := leaf_le_sum (massOne hn ht ha) root i hi
  unfold seed seedSlope seedOffset
  change IntegralMixedAuxiliaryMarkedRadiusModel.nativeMass hn ht ha R _ ≤ _
  nlinarith

private theorem source_bounds (R : List Bool → ℕ) (root : List Bool) :
    InstructionBounds (seed hn ht ha R root + 1) (factor hn ht ha root)
      ((parameters hn ht ha).sourceWidth root) ((parameters hn ht ha).degree root) 3
      (⟨IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t R root,
        IntegralMixedAuxiliaryMarkedRecordPlan.source_cap hn ht ha R root,
        IntegralMixedFullHistoryScript.defaultCommand⟩ : Instruction ((parameters hn ht ha).ambient root) ((parameters hn ht ha).width root)) := by
  have HS := low_height_le hn ht ha R root
  have HF := IntegralMixedAuxiliaryMarkedRecordPlan.factor_positive hn ht ha root
  constructor
  · intro e
    exact (BoundedRegularLowHeight.coefficient (IntegralMixedAuxiliaryMarkedIntegerPlan.readers n t R) root e).trans
      (Nat.pow_le_pow_right (by decide) (by nlinarith))
  · change (BoundedRegularLowModularTerm.source (IntegralMixedAuxiliaryMarkedIntegerPlan.readers n t R) root).leading.natAbs.size ≤ _
    rw [BoundedRegularLowHeight.leading]
    have HL : BoundedFullWriter.regularizationExponent (IntegralMixedAuxiliaryMarkedIntegerPlan.readers n t R) root + 1 ≤
        BoundedRegularLowHeight.height (IntegralMixedAuxiliaryMarkedIntegerPlan.readers n t R) root := by
      unfold BoundedRegularLowHeight.height
      omega
    nlinarith
  · rw [IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree]
    exact le_rfl
  · rw [IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree]
    exact le_rfl
  · rw [IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree]
    exact IntegralMixedAuxiliaryMarkedRecordPlan.spatial_cap hn ht ha root
  · intro k
    rw [Polynomial.coeff_X]
    split_ifs
    · simpa only [Int.natAbs_one] using Nat.one_le_two_pow (n := factor hn ht ha root * (seed hn ht ha R root + 1) + 1)
    · exact Nat.zero_le _

theorem familyInputs (R : List Bool → ℕ) :
    FamilyInputs (parameters hn ht ha) (plan hn ht ha R) (fun _ => 3) (factor hn ht ha) (seed hn ht ha R) := by
  apply IntegralMixedSourceIntegerRecordAppend.familyInputs (parameters hn ht ha)
    (fun root _ => IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t R root)
    (IntegralMixedAuxiliaryMarkedRecordPlan.positive hn ht ha)
    (fun root _ => IntegralMixedAuxiliaryMarkedIntegerPlan.spatial_degree n t R root)
    (IntegralMixedAuxiliaryMarkedRecordPlan.spatial_cap hn ht ha) (fun c => number n c + 8)
    (IntegralMixedAuxiliaryMarkedRecordPlan.source_cap hn ht ha R)
    (IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R)
    (IntegralMixedAuxiliaryMarkedIntegerSource.nonzero hn ht ha R)
    (IntegralMixedAuxiliaryMarkedIntegerPlan.source_degree_cap hn ht ha R)
    (IntegralMixedAuxiliaryMarkedRecordPlan.room hn ht ha) (fun _ => 3) (factor hn ht ha) (seed hn ht ha R)
  · exact fun _ => le_rfl
  · exact fun root _ => source_bounds hn ht ha R root
  · intro root i hi
    have HM := integer_mass_le hn ht ha R root i hi
    have HF := IntegralMixedAuxiliaryMarkedRecordPlan.factor_positive hn ht ha root
    nlinarith
  · intro root
    have HF := IntegralMixedAuxiliaryMarkedRecordPlan.factor_positive hn ht ha root
    nlinarith
  · exact fun _ => le_rfl

noncomputable def amplification (root : List Bool) : ℕ :=
  growth ((parameters hn ht ha).ambient root) ((parameters hn ht ha).cap root + 1)
    ((parameters hn ht ha).width root) ((parameters hn ht ha).sourceWidth root)
    ((parameters hn ht ha).degree root) 3 (factor hn ht ha root) ^ ((parameters hn ht ha).cap root + 1)

noncomputable def bankSlope (root : List Bool) := amplification hn ht ha root * seedSlope hn ht ha root
noncomputable def bankOffset (root : List Bool) := amplification hn ht ha root * (seedOffset hn ht ha root + 1)

theorem amplification_binary : BinaryFn (amplification hn ht ha) :=
  (growth_binary (access hn ht ha).ambient ((access hn ht ha).cap.add (UnaryFn.const 1))
    (access hn ht ha).width (access hn ht ha).sourceWidth (access hn ht ha).degree
    (BinaryFn.const 3) (IntegralMixedAuxiliaryMarkedRecordPlan.factor_binary hn ht ha)).powUnary
    ((access hn ht ha).cap.add (UnaryFn.const 1))

theorem bankSlope_binary : BinaryFn (bankSlope hn ht ha) :=
  (amplification_binary hn ht ha).mul (seedSlope_binary hn ht ha)

theorem bankOffset_binary : BinaryFn (bankOffset hn ht ha) :=
  (amplification_binary hn ht ha).mul ((seedOffset_binary hn ht ha).add (BinaryFn.const 1))

theorem familyHeight_le (R : List Bool → ℕ) (key : List Bool) :
    familyHeight (parameters hn ht ha) (fun _ => 3) (factor hn ht ha) (seed hn ht ha R) key ≤
      bankSlope hn ht ha (pairFst key) * R (pairFst key) + bankOffset hn ht ha (pairFst key) := by
  have HP : IntegralMixedFullHistoryFamilyBits.prefixLength (parameters hn ht ha) key ≤
      (parameters hn ht ha).cap (pairFst key) + 1 := min_le_right _ _
  have HG := Nat.pow_le_pow_right (growth_pos ((parameters hn ht ha).ambient (pairFst key))
    ((parameters hn ht ha).cap (pairFst key) + 1) ((parameters hn ht ha).width (pairFst key))
    ((parameters hn ht ha).sourceWidth (pairFst key)) ((parameters hn ht ha).degree (pairFst key))
    3 (factor hn ht ha (pairFst key))) HP
  apply (Nat.mul_le_mul_right (seed hn ht ha R (pairFst key) + 1) HG).trans_eq
  unfold bankSlope bankOffset seed amplification
  ring

theorem bank_bounds (R : List Bool → ℕ) (key : List Bool) :
    ((IntegralMixedFramedHistoryFamilyBits.family (parameters hn ht ha) (plan hn ht ha R)
      (data hn ht ha R)).state key).bank.Bounds
      (bankSlope hn ht ha (pairFst key) * R (pairFst key) + bankOffset hn ht ha (pairFst key)) :=
  (family_bank_bounds (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R)
    (fun _ => 3) (factor hn ht ha) (seed hn ht ha R) (familyInputs hn ht ha R) key).mono
      (familyHeight_le hn ht ha R key)

private theorem planning_bank_bounds (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (L F C : List Bool → ℕ) (key : List Bool) (G : ℕ)
    (HB : ((IntegralMixedFramedHistoryFamilyBits.family P D H).state key).bank.Bounds G) :
    ((IntegralMixedFramedHistoryFamilyBits.family (IntegralMixedFramedNormalizationBits.planned P L F C)
      (IntegralMixedFramedNormalizationBits.plannedPlan P D L F C)
      (IntegralMixedFramedNormalizationBits.plannedData P D H L F C)).state key).bank.Bounds G := HB

attribute [local irreducible] IntegralMixedAuxiliaryMarkedIntegerPlan.seed
  IntegralMixedSourceIntegerRecordAppend.plan IntegralMixedSourceIntegerRecordAppend.data

theorem certified_bank_bounds {R : List Bool → ℕ} (hR : BinaryFn R) (key : List Bool) :
    ((IntegralMixedFramedHistoryFamilyBits.family
      (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha hR)
      (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha hR)
      (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedData hn ht ha hR)).state key).bank.Bounds
      (bankSlope hn ht ha (pairFst key) * R (pairFst key) + bankOffset hn ht ha (pairFst key)) :=
  planning_bank_bounds (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R)
    (fun _ => 3) (factor hn ht ha) (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR) key _
    (bank_bounds hn ht ha R key)

end LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordRadiusHeight
