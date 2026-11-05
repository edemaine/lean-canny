/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordCoefficientBounds
public import LeanCanny.Encoding.CoefficientMarkedRecordRawGrowth
public import LeanCanny.Algebra.CoefficientCoordinateCutoffIteration
/-! # An original-input budget for every canonical record cutoff -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordEffectiveCutoff
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory
open CoefficientCoordinateDyadicBounds
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n:List Bool→ℕ} {t:List Bool→LeanCanny.ETR.Term}
  (hn:UnaryFn n) (ht:(fun q=>(t q).toData.toBits)∈FP) (ha:∀q,(t q).arity≤n q)

noncomputable def rankCap (ctx:List Bool):ℕ:=
  (2^CoefficientMarkedIntegerBirth.width hn ht ha ctx)^CoefficientMarkedRecordActual.horizon hn ht ha ctx

noncomputable def budget (ctx:List Bool) (k:ℕ):ℕ:=
  stageBudget (rankCap hn ht ha ctx) (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rawSlope hn ht ha ctx)
    (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rawOffset hn ht ha ctx+1) 0 k

noncomputable def effectiveCutoff (ctx:List Bool):ℕ:=
  budget hn ht ha ctx (IntegralMixedCausalRecordPlanBits.count ctx)

theorem rankCap_binary:BinaryFn (rankCap hn ht ha):=
  ((BinaryFn.const 2).powUnary (IntegralMixedAuxiliaryMarkedIntegerPlan.access hn ht ha).width).powUnary
    ((IntegralMixedAuxiliaryMarkedRecordPlan.access hn ht ha).cap.add (UnaryFn.const 1))

theorem effectiveCutoff_binary:BinaryFn (effectiveCutoff hn ht ha):=
  stageBudget_binary (rankCap_binary hn ht ha)
    (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rawSlope_binary hn ht ha)
    ((IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rawOffset_binary hn ht ha).add (BinaryFn.const 1))
    (BinaryFn.const 0) IntegralMixedCausalRecordPlanBits.count_unary

theorem budget_mono (ctx:List Bool) {i j:ℕ} (h:i≤j):
    budget hn ht ha ctx i≤budget hn ht ha ctx j:=
  stageBudget_mono _ _ _ _ h

theorem rank_le (ctx:List Bool) (k:ℕ) (hk:k≤IntegralMixedCausalRecordPlanBits.count ctx):
    (2^CoefficientMarkedIntegerBirth.width hn ht ha ctx)^
      ((CoefficientMarkedPreludeActual.indices n ctx).length+(CoefficientMarkedRecordActual.codes ctx k).length)≤
      rankCap hn ht ha ctx:=by
  apply Nat.pow_le_pow_right (Nat.two_pow_pos _)
  rw [CoefficientMarkedRecordActual.codes_length]
  exact CoefficientMarkedRecordActual.birth_room hn ht ha ctx k hk

private theorem massBudget_succ_offset (C K H:ℕ):
    IntegerPolynomialDyadic.massBudget C K H+1=IntegerPolynomialDyadic.massBudget C K (H+1):=by
  unfold IntegerPolynomialDyadic.massBudget
  omega

private theorem characteristicBudget_mono_bits (rank:ℕ) {a b:ℕ} (h:a≤b):
    ParameterMatrixMassBounds.characteristicBudget rank a≤
      ParameterMatrixMassBounds.characteristicBudget rank b:=by
  unfold ParameterMatrixMassBounds.characteristicBudget
  exact Nat.add_le_add_left (Nat.mul_le_mul_left rank (Nat.add_le_add_right h 1)) _

theorem budget_step (ctx:List Bool) (k:ℕ) (hk:k≤IntegralMixedCausalRecordPlanBits.count ctx):
    max (budget hn ht ha ctx k)
      (cutBudget ((2^CoefficientMarkedIntegerBirth.width hn ht ha ctx)^
        ((CoefficientMarkedPreludeActual.indices n ctx).length+(CoefficientMarkedRecordActual.codes ctx k).length))
        (budget hn ht ha ctx k) (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rawSlope hn ht ha ctx)
        (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rawOffset hn ht ha ctx+1))≤
      budget hn ht ha ctx (k+1):=
  step_le_budget_succ _ _ _ 0 k (rank_le hn ht ha ctx k hk) le_rfl le_rfl le_rfl


theorem cutoff_le_budget (ctx:List Bool) (k:ℕ) (hk:k≤IntegralMixedCausalRecordPlanBits.count ctx):
    CoefficientMarkedRecordSpecialization.cutoff hn ht ha ctx (CoefficientMarkedRecordActual.horizon hn ht ha ctx)
      (CoefficientMarkedRecordActual.codes ctx k)≤budget hn ht ha ctx k:=by
  induction k with
  | zero=>
    change 0≤budget hn ht ha ctx 0
    exact Nat.zero_le _
  | succ k ih=>
    have hk0:k≤IntegralMixedCausalRecordPlanBits.count ctx:=by omega
    have hklt:k<IntegralMixedCausalRecordPlanBits.count ctx:=by omega
    have HI:=ih hk0
    by_cases hc:IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code ctx k)=true
    · simpa only [CoefficientMarkedRecordActual.codes_succ,CoefficientMarkedRecordSpecialization.cutoff,hc,ite_true] using
        HI.trans (budget_mono hn ht ha ctx (Nat.le_succ k))
    · have hf:=Bool.eq_false_of_not_eq_true hc
      let F:=CoefficientMarkedRecordPrefix.build hn ht ha ctx (CoefficientMarkedRecordActual.horizon hn ht ha ctx)
        (CoefficientMarkedRecordActual.codes ctx k)
      let code:=IntegralMixedCausalRecordPlanBits.code ctx k
      let K:=IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rawSlope hn ht ha ctx
      let H:=IntegralMixedAuxiliaryMarkedRecordRadiusHeight.rawOffset hn ht ha ctx
      let C:=budget hn ht ha ctx k
      have HE:=CoefficientMarkedRecordCoefficientBounds.topEntryBound_of_cutoff_le hn ht ha ctx k hklt hf C HI
      have HB:=CoefficientMarkedRecordSpecialization.entryBits_le hn ht ha ctx F code
        (IntegerPolynomialDyadic.massBudget C K H) HE
      have HB':CoefficientMarkedRecordSpecialization.entryBits hn ht ha ctx F code≤
          IntegerPolynomialDyadic.massBudget C K (H+1):=
        HB.trans_eq (massBudget_succ_offset C K H)
      let rank:=(2^CoefficientMarkedIntegerBirth.width hn ht ha ctx)^
        ((CoefficientMarkedPreludeActual.indices n ctx).length+(CoefficientMarkedRecordActual.codes ctx k).length)
      have HT:=Nat.add_le_add_right (characteristicBudget_mono_bits rank HB') 1
      change ParameterMatrixMassBounds.characteristicBudget rank
        (CoefficientMarkedRecordSpecialization.entryBits hn ht ha ctx F code)+1≤cutBudget rank C K (H+1) at HT
      have HM: max (CoefficientMarkedRecordSpecialization.cutoff hn ht ha ctx
          (CoefficientMarkedRecordActual.horizon hn ht ha ctx) (CoefficientMarkedRecordActual.codes ctx k))
          (ParameterMatrixMassBounds.characteristicBudget rank
            (CoefficientMarkedRecordSpecialization.entryBits hn ht ha ctx F code)+1)≤budget hn ht ha ctx (k+1):=
        (max_le_max HI HT).trans (budget_step hn ht ha ctx k hk0)
      simpa only [CoefficientMarkedRecordActual.codes_succ,CoefficientMarkedRecordSpecialization.cutoff,hf,
        Bool.false_eq_true,ite_false] using HM

theorem cutoff_le_effective (ctx:List Bool) (k:ℕ) (hk:k≤IntegralMixedCausalRecordPlanBits.count ctx):
    CoefficientMarkedRecordSpecialization.cutoff hn ht ha ctx (CoefficientMarkedRecordActual.horizon hn ht ha ctx)
      (CoefficientMarkedRecordActual.codes ctx k)≤effectiveCutoff hn ht ha ctx:=
  (cutoff_le_budget hn ht ha ctx k hk).trans (budget_mono hn ht ha ctx hk)

/-- One original-input cutoff specializes every actual canonical prefix. -/
theorem specializes_above_effective (ctx:List Bool) (radius:List Bool→ℕ) (k:ℕ)
    (hk:k≤IntegralMixedCausalRecordPlanBits.count ctx) (hR:effectiveCutoff hn ht ha ctx≤radius ctx):
    CoefficientHistoryPrefix.Specializes (radius ctx)
      (CoefficientMarkedRecordPrefix.build hn ht ha ctx (CoefficientMarkedRecordActual.horizon hn ht ha ctx)
        (CoefficientMarkedRecordActual.codes ctx k))
      (CoefficientMarkedRecordNative.run hn ht ha ctx radius (CoefficientMarkedRecordActual.horizon hn ht ha ctx)
        (CoefficientMarkedRecordActual.codes ctx k) (CoefficientMarkedRecordActual.prefix_room hn ht ha ctx k hk)):=
  CoefficientMarkedRecordSpecialization.specializes hn ht ha ctx radius
    (CoefficientMarkedRecordActual.horizon hn ht ha ctx) (CoefficientMarkedRecordActual.codes ctx k)
    (CoefficientMarkedRecordActual.prefix_room hn ht ha ctx k hk) ((cutoff_le_effective hn ht ha ctx k hk).trans hR)

end LeanCanny.Encoding.CoefficientMarkedRecordEffectiveCutoff
