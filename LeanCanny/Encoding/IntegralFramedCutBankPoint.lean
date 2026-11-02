/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedCutBankDenominator
/-! # Exact newest bank-point recovery for an actual relative cut

Both horizon and width are those of the actual framed plan. Neither a
legacy bank width nor a raw factor leading replaces the stored denominator.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedCutBankPoint
open LeanCanny.Algebra IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem cap_value (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) :
    (family P D H).cap key=P.cap (pairFst key)+1 := rfl
private theorem width_value (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) :
    (family P D H).width key=P.width (pairFst key) := rfl

attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (c : List Bool) (ha : IntegralMixedFramedFullCutProbeBits.Active P c)
local notation "G" => family P D H
local notation "old" => IntegralMixedVirtualTaskBits.saved P c
local notation "new" => IntegralFramedCutSuccessor.key P c
local notation "x" => IntegralMixedCutSource.Family.state G old
local notation "f" => IntegralMixedRelativeCuts.factor x (IntegralMixedCutSource.Family.birth_bound G old)
  (IntegralMixedCutSource.Family.rule G old) (IntegralMixedCutSource.Family.kind G old)
local notation "d" => IntegralMixedCutSource.Family.degree G old

include ha in
theorem dimension : (G).birth old+1=(G).birth new :=
  (congrArg (fun n=>n+1) ((IntegralMixedFramedHistoryFamilyBits.geometry P D H).birth c)).trans
    (IntegralFramedCutSuccessor.active_count P D H c ha).symm

include ha in
theorem point_newest (hcut : IntegralFramedCreatingCut.ParentCut P D c) (z : ℕ→ℝ) :
    (IntegralMixedFramedBankObservation.ofState ((G).state new)).point z 0=
      IntegralRelativeTruncation.jointQuotient (x).sampler.scalarPrefix f d (fun i=>z i.val) := by
  have HR : pairFst new=pairFst old :=
    (IntegralMixedFramedHistoryFamilyBits.keyAt_root _ _ _).trans (IntegralMixedFullHistoryFamilyBits.saved_root P c).symm
  have HS : (G).cap new=(G).cap old :=
    (cap_value P D H new).trans ((congrArg (fun r=>P.cap r+1) HR).trans (cap_value P D H old).symm)
  have HW : (G).width new=(G).width old :=
    (width_value P D H new).trans ((congrArg P.width HR).trans (width_value P D H old).symm)
  have HM:=dimension P D H c ha
  have HP : UniformIntegralPowerSchedule.weights ((G).cap new) (2^(G).width new) ((G).birth new)
      ⟨0,IntegralFramedCutSuccessor.positive P D H c⟩=
      UniformIntegralPowerSchedule.birth ((G).cap old) (2^(G).width old) ((G).birth old) := by
    change UniformIntegralPowerSchedule.birth ((G).cap new) (2^(G).width new) ((G).birth new-1-0)=_
    rw [Nat.sub_zero,HS,HW,←HM,Nat.add_sub_cancel]
  unfold IntegralMixedFramedBankObservation.Data.point IntegralMixedFramedBankObservation.ofState
  rw [dite_eq_left (IntegralFramedCutSuccessor.positive P D H c)]
  rw [HP]
  change z 0^UniformIntegralPowerSchedule.birth ((G).cap old) (2^(G).width old) ((G).birth old) /
    (((G).state new).bank.denominator ⟨0,IntegralFramedCutSuccessor.positive P D H c⟩ : ℝ)=_
  rw [IntegralFramedCutBankDenominator.newest_denominator P D H c ha hcut]
  rfl

end LeanCanny.Encoding.IntegralFramedCutBankPoint
