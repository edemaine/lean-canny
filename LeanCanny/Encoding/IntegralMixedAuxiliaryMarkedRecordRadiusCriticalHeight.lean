/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordRadiusRawHeight

/-! # Actual critical-birth matrices have affine radius height -/

@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordRadiusHeight
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask FixedWidthPolynomial
open IntegralMixedAuxiliaryMarkedRecordPlan (parameters plan data access factor)
open IntegralMixedFramedStepHeight
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

noncomputable def criticalFactor (root : List Bool) :=
  IntegralMixedGlobalHeightBounds.coefficientFactor ((parameters hn ht ha).ambient root)
    (IntegralMixedFramedOriginalBounds.rootRank (parameters hn ht ha) root)
    ((parameters hn ht ha).sourceWidth root) ((parameters hn ht ha).degree root)
    ((parameters hn ht ha).cap root + 1) 3 * (factor hn ht ha root + 2)

noncomputable def criticalSlope (root : List Bool) := criticalFactor hn ht ha root * bankSlope hn ht ha root
noncomputable def criticalOffset (root : List Bool) := criticalFactor hn ht ha root * bankOffset hn ht ha root

theorem criticalFactor_binary : BinaryFn (criticalFactor hn ht ha) :=
  (IntegralMixedGlobalHeightBounds.coefficientFactor_binary (access hn ht ha).ambient
    (IntegralMixedFramedRawHeight.rootRank_binary (parameters hn ht ha) (access hn ht ha))
    (access hn ht ha).sourceWidth (access hn ht ha).degree
    (BinaryFn.ofUnary ((access hn ht ha).cap.add (UnaryFn.const 1))) (BinaryFn.const 3)).mul
    ((IntegralMixedAuxiliaryMarkedRecordPlan.factor_binary hn ht ha).add (BinaryFn.const 2))

theorem criticalSlope_binary : BinaryFn (criticalSlope hn ht ha) :=
  (criticalFactor_binary hn ht ha).mul (bankSlope_binary hn ht ha)

theorem criticalOffset_binary : BinaryFn (criticalOffset hn ht ha) :=
  (criticalFactor_binary hn ht ha).mul (bankOffset_binary hn ht ha)

private theorem critical_coefficient_height {d S B m : ℕ} {P : IntegralMixedHistory.SpatialSource d} {ι : Type}
    (x : IntegralMixedHistory.State P S B m ι) (hm : m ≤ S) (rule : IntegralMixedHistory.CriticalRule d)
    (G C : ℕ) (HB : x.bank.Bounds G) (HC : ∀ e, (P.low.coeff e).natAbs ≤ 2 ^ C)
    (k : ℕ) (r s : Fin (count m B)) :
    (Algebra.leftMulMatrix x.sampler.scalarPrefix.basis.finBasis
      ((IntegralMixedHistory.criticalPolynomial x hm rule).coeff k) r s).natAbs ≤
        2 ^ IntegralMixedHistory.criticalHeight x hm rule G C HB HC :=
  IntegralHistoryCriticalBits.coefficient_height (IntegralMixedHistory.family x hm rule)
    (IntegralMixedHistory.familyBounds x hm rule G C HB HC) [] k r s

noncomputable def criticalState (R : List Bool → ℕ) (key : List Bool) :
    IntegralMixedHistory.State ((actualFamily hn ht ha R).spatial key) ((actualFamily hn ht ha R).cap key)
      ((actualFamily hn ht ha R).width key) ((actualFamily hn ht ha R).birth key)
      ((actualFamily hn ht ha R).physical key) := (actualFamily hn ht ha R).state key

theorem criticalState_eq (R : List Bool → ℕ) (key : List Bool) :
    criticalState hn ht ha R key = (actualFamily hn ht ha R).state key := rfl

attribute [local irreducible] criticalState IntegralMixedSourceIntegerRecordAppend.plan
  IntegralMixedSourceIntegerRecordAppend.data

private theorem criticalState_bank (R : List Bool → ℕ) (key : List Bool) :
    (criticalState hn ht ha R key).bank.Bounds ((originalBounds hn ht ha R).bankHeight key) :=
  Eq.mpr (congrArg (fun x => x.bank.Bounds ((originalBounds hn ht ha R).bankHeight key))
    (criticalState_eq hn ht ha R key)) ((originalBounds hn ht ha R).bank key)

theorem critical_coefficient_bound (R : List Bool → ℕ) (key : List Bool)
    (rule : IntegralMixedHistory.CriticalRule ((parameters hn ht ha).ambient (pairFst key)))
    (hc : (IntegralMixedFramedHistoryFamilyBits.instruction (parameters hn ht ha) (plan hn ht ha R) key).command =
      .critical rule) (k : ℕ)
    (r s : Fin (count ((actualFamily hn ht ha R).birth key) ((actualFamily hn ht ha R).width key))) :
    (Algebra.leftMulMatrix (criticalState hn ht ha R key).sampler.scalarPrefix.basis.finBasis
      ((IntegralMixedHistory.criticalPolynomial (criticalState hn ht ha R key)
        ((actualFamily hn ht ha R).birth_bound key) rule).coeff k) r s).natAbs ≤
      2 ^ (criticalSlope hn ht ha (pairFst key) * R (pairFst key) + criticalOffset hn ht ha (pairFst key)) := by
  let F := actualFamily hn ht ha R
  let H := originalBounds hn ht ha R
  let x := criticalState hn ht ha R key
  have HB := criticalState_bank hn ht ha R key
  have HI := family_instruction_bounds (parameters hn ht ha) (plan hn ht ha R)
    (fun _ => 3) (factor hn ht ha) (seed hn ht ha R) (familyInputs hn ht ha R) key
  have HS := HI.command
  rw [hc] at HS
  have HM : count (F.birth key) (F.width key) ≤ H.rank key :=
    (Nat.pow_le_pow_right (Nat.two_pow_pos _) (Nat.le_succ _)).trans (H.rank_bound key)
  have HE := critical_coefficient_height x (F.birth_bound key) rule (H.bankHeight key) (H.sourceHeight key)
    HB (H.coefficient key) k r s
  have HG := IntegralMixedGlobalHeightBounds.criticalHeight_scaled x (F.birth_bound key) rule
    (H.bankHeight key) (H.sourceHeight key) (H.rank key) (H.sourceWidth key) (H.spatialDegree key) (H.nodes key)
    HB (H.coefficient key) (H.leading key) HM (H.width_bound key) (H.degree_bound key)
    HS.1 HS.2.1 HS.2.2 (H.source_le_bank key)
  apply HE.trans (Nat.pow_le_pow_right (by decide) (HG.trans ?_))
  change IntegralMixedGlobalHeightBounds.coefficientFactor ((parameters hn ht ha).ambient (pairFst key))
    (IntegralMixedFramedOriginalBounds.rootRank (parameters hn ht ha) (pairFst key))
    ((parameters hn ht ha).sourceWidth (pairFst key)) ((parameters hn ht ha).degree (pairFst key))
    ((parameters hn ht ha).cap (pairFst key) + 1) 3 *
      ((factor hn ht ha (pairFst key) + 2) *
        familyHeight (parameters hn ht ha) (fun _ => 3) (factor hn ht ha) (seed hn ht ha R) key) ≤ _
  calc
    _ = criticalFactor hn ht ha (pairFst key) *
        familyHeight (parameters hn ht ha) (fun _ => 3) (factor hn ht ha) (seed hn ht ha R) key := by
      unfold criticalFactor
      ring
    _ ≤ criticalFactor hn ht ha (pairFst key) *
        (bankSlope hn ht ha (pairFst key) * R (pairFst key) + bankOffset hn ht ha (pairFst key)) :=
      Nat.mul_le_mul_left _ (familyHeight_le hn ht ha R key)
    _ = _ := by unfold criticalSlope criticalOffset; ring

end LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedRecordRadiusHeight
