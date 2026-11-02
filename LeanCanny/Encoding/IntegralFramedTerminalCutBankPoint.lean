/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedTerminalCutBankDenominator
public import LeanCanny.Algebra.IntegralMixedFramedBankObservation
/-! # Actual terminal retained bank values are the earlier cut quotients

Both the original power schedule and literal stored denominator are
preserved. The denominator is normalized at the actual old prefix basis;
it is not replaced by a raw polynomial leading coefficient.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedTerminalCutBankPoint
open LeanCanny.Algebra IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
set_option backward.isDefEq.respectTransparency false

private theorem cap_value (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :
    (family P D H).cap q=P.cap (pairFst q)+1 := rfl
private theorem width_value (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :
    (family P D H).width q=P.width (pairFst q) := rfl
attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (c terminal : List Bool) (ha : IntegralMixedFramedFullCutProbeBits.Active P c)
  (hcut : IntegralFramedCreatingCut.ParentCut P D c) (hroot : pairFst terminal=RankedHistoryTask.root c)
  (hfit : birth P c<(family P D H).birth terminal) (z : ℕ→ℝ)
local notation "G" => family P D H
local notation "parent" => IntegralMixedVirtualTaskBits.saved P c
local notation "old" => IntegralMixedCutSource.Family.state G parent
local notation "degree" => IntegralMixedCutSource.Family.degree G parent
local notation "rule" => IntegralMixedCutSource.Family.rule G parent
local notation "kind" => IntegralMixedCutSource.Family.kind G parent
local notation "bound" => IntegralMixedCutSource.Family.birth_bound G parent
local notation "factor" => IntegralMixedRelativeCuts.factor old bound rule kind

include ha hcut hroot hfit in
theorem point_eq :
    (IntegralMixedFramedBankObservation.ofState ((G).state terminal)).point z ((G).birth terminal-birth P c-1)=
      IntegralRelativeTruncation.jointQuotient (old).sampler.scalarPrefix factor degree
        (fun i=>z (i.val+((G).birth terminal-(birth P c+1)))) := by
  have HI:=IntegralFramedTerminalCutBankDenominator.index_lt P D H c terminal hfit
  have HR : pairFst terminal=pairFst parent := hroot.trans (IntegralMixedFullHistoryFamilyBits.saved_root P c).symm
  have HS : (G).cap terminal=(G).cap parent :=
    (cap_value P D H terminal).trans ((congrArg (fun r=>P.cap r+1) HR).trans (cap_value P D H parent).symm)
  have HB : (G).width terminal=(G).width parent :=
    (width_value P D H terminal).trans ((congrArg P.width HR).trans (width_value P D H parent).symm)
  have HM : (G).birth parent=birth P c := (IntegralMixedFramedHistoryFamilyBits.geometry P D H).birth c
  have HW : UniformIntegralPowerSchedule.weights ((G).cap terminal) (2^(G).width terminal) ((G).birth terminal)
      ⟨(G).birth terminal-birth P c-1,HI⟩=
      UniformIntegralPowerSchedule.birth ((G).cap parent) (2^(G).width parent) ((G).birth parent) := by
    change UniformIntegralPowerSchedule.birth ((G).cap terminal) (2^(G).width terminal)
      ((G).birth terminal-1-((G).birth terminal-birth P c-1))=_
    have HE : (G).birth terminal-1-((G).birth terminal-birth P c-1)=(G).birth parent := by omega
    rw [HE,HS,HB]
  unfold IntegralMixedFramedBankObservation.Data.point IntegralMixedFramedBankObservation.ofState
  rw [dite_eq_left HI,HW]
  change z ((G).birth terminal-birth P c-1)^UniformIntegralPowerSchedule.birth ((G).cap parent) (2^(G).width parent) ((G).birth parent) /
    (((G).state terminal).bank.denominator ⟨(G).birth terminal-birth P c-1,HI⟩:ℝ)=_
  rw [IntegralFramedTerminalCutBankDenominator.retained_denominator P D H c terminal ha hcut hroot hfit]
  unfold IntegralRelativeTruncation.jointQuotient
  simp only [Fin.val_zero,Nat.zero_add,Nat.sub_sub]

end LeanCanny.Encoding.IntegralFramedTerminalCutBankPoint
