/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordRadiusRawHeight
public import LeanCanny.Algebra.IntegralMixedFramedTerminalCoordinateSource
public import LeanCanny.Algebra.IntegralMixedFramedZeroTarskiMass

/-! # Actual coordinate-head mass with fixed original selector metadata

Parent, terminal, and degree selectors have no radius argument. The estimate
charges the literal parameter bound instead of inferring its radius stability.
-/

@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordRadiusHeight
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedAuxiliaryMarkedRecordPlan (parameters plan data access factor)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def headOffset (parent : List Bool → List Bool) (e : List Bool → ℕ) (q : List Bool) : ℕ :=
  let root := pairFst (IntegralMixedVirtualTaskBits.saved (parameters hn ht ha) (parent q))
  rawOffset hn ht ha root + ((parameters hn ht ha).cap root + 1) * (parameters hn ht ha).width root + (e q + 1).size

theorem headSlope_binary (parent : List Bool → List Bool) (hp : parent ∈ FP) :
    BinaryFn (fun q => rawSlope hn ht ha
      (pairFst (IntegralMixedVirtualTaskBits.saved (parameters hn ht ha) (parent q)))) :=
  (rawSlope_binary hn ht ha).comp (mem_FP_comp
    (mem_FP_comp hp (IntegralMixedVirtualTaskBits.saved_FP (parameters hn ht ha) (access hn ht ha))) pairFst_mem_FP)

theorem headOffset_binary (parent : List Bool → List Bool) (e : List Bool → ℕ)
    (hp : parent ∈ FP) (he : BinaryFn e) : BinaryFn (headOffset hn ht ha parent e) := by
  have HR : (fun q => pairFst (IntegralMixedVirtualTaskBits.saved (parameters hn ht ha) (parent q))) ∈ FP :=
    mem_FP_comp (mem_FP_comp hp (IntegralMixedVirtualTaskBits.saved_FP (parameters hn ht ha) (access hn ht ha))) pairFst_mem_FP
  have HO : BinaryFn (fun q => rawOffset hn ht ha
      (pairFst (IntegralMixedVirtualTaskBits.saved (parameters hn ht ha) (parent q)))) :=
    (rawOffset_binary hn ht ha).comp HR
  have HC : BinaryFn (fun q => (parameters hn ht ha).cap
      (pairFst (IntegralMixedVirtualTaskBits.saved (parameters hn ht ha) (parent q))) + 1) :=
    BinaryFn.ofUnary (((access hn ht ha).cap.add (UnaryFn.const 1)).comp HR)
  have HW : BinaryFn (fun q => (parameters hn ht ha).width
      (pairFst (IntegralMixedVirtualTaskBits.saved (parameters hn ht ha) (parent q)))) :=
    BinaryFn.ofUnary ((access hn ht ha).width.comp HR)
  exact (HO.add (HC.mul HW)).add ((he.add (BinaryFn.const 1)).size)

attribute [local irreducible] IntegralMixedSourceIntegerRecordAppend.plan IntegralMixedSourceIntegerRecordAppend.data
  IntegralMixedFramedHistoryFamilyBits.family

private theorem old_mass_le (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (L F C : List Bool → ℕ) (key : List Bool) :
    IntegralMixedFramedCoordinatePackedBits.oldMassBound P D H L F C key ≤
      (P.cap (pairFst key) + 1) * P.width (pairFst key) +
        IntegralMixedFramedRawHeight.rootCeiling P L F C (pairFst key) := by
  have HB : (IntegralMixedFramedHistoryFamilyBits.family P D H).birth key ≤ P.cap (pairFst key) + 1 := by
    rw [IntegralMixedFramedHistoryFamilyBits.family_birth]
    exact min_le_right _ _
  have HW : (IntegralMixedFramedHistoryFamilyBits.family P D H).width key = P.width (pairFst key) := by
    unfold IntegralMixedFramedHistoryFamilyBits.family
    rfl
  unfold IntegralMixedFramedCoordinatePackedBits.oldMassBound
  rw [HW]
  exact Nat.add_le_add_right (Nat.mul_le_mul_right (P.width (pairFst key)) HB) _

theorem head_coefficient_mass (R : List Bool → ℕ)
    (parent terminal : List Bool → List Bool) (d e : List Bool → ℕ) (q : List Bool) (y : ℕ) :
    MvMass.mass ((IntegralMixedFramedTerminalCoordinateHeadBits.polynomial
      (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R) parent terminal d e q).coeff y) ≤
      2 ^ (rawSlope hn ht ha (pairFst (IntegralMixedVirtualTaskBits.saved (parameters hn ht ha) (parent q))) *
        R (pairFst (IntegralMixedVirtualTaskBits.saved (parameters hn ht ha) (parent q))) + headOffset hn ht ha parent e q) := by
  have HM := IntegralMixedFramedTerminalCoordinateHeadBits.coefficient_mass (parameters hn ht ha)
    (plan hn ht ha R) (data hn ht ha R) (fun _ => 3) (factor hn ht ha) (seed hn ht ha R)
    (familyInputs hn ht ha R) (IntegralMixedAuxiliaryMarkedRecordPlan.factor_positive hn ht ha)
    (fallback_bounds hn ht ha R) parent terminal d e q y
  apply HM.trans (Nat.pow_le_pow_right (by decide) ?_)
  have HL := old_mass_le (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R)
    (fun _ => 3) (factor hn ht ha) (seed hn ht ha R)
    (IntegralMixedVirtualTaskBits.saved (parameters hn ht ha) (parent q))
  rw [raw_ceiling_affine] at HL
  dsimp only [IntegralMixedFramedCoordinatePackedBits.headMassBound, headOffset]
  omega

theorem zero_head_coefficient_mass (R : List Bool → ℕ)
    (parent terminal : List Bool → List Bool) (d e : List Bool → ℕ) (q : List Bool) (y : ℕ) :
    MvMass.mass ((IntegralMixedFramedZeroTarskiBits.head
      (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R) parent terminal d e q).coeff y) ≤
      2 ^ (rawSlope hn ht ha (pairFst (IntegralMixedVirtualTaskBits.saved (parameters hn ht ha) (parent q))) *
        R (pairFst (IntegralMixedVirtualTaskBits.saved (parameters hn ht ha) (parent q))) + headOffset hn ht ha parent e q) :=
  (FixedWidthBivariateZeroLiftBits.mass _ _ q y).trans (head_coefficient_mass hn ht ha R parent terminal d e q y)

end LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordRadiusHeight
