/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedHistoryProducer
public import LeanCanny.Algebra.IntegralMixedFramedCompanionSource
public import LeanCanny.Algebra.IntegralMixedFramedBankObservation
/-! # Same-root saved prefixes retain literal bank quotients

Denominators are the same creating leading integer. Raw scalar suffixes
use the OLD weights, preserved by the global schedule; no power ratio or
new hom evaluation is needed. Both caller keys remain explicit.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedBankObservationShift
open LeanCanny.Encoding LeanCanny.Geometry IntegralCriticalHistoryTask UniformIntegralPowerSchedule
open IntegralMixedFramedHistoryFamilyBits (Plan family keyAt prefixLength)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (old terminal : List Bool) (hroot : pairFst terminal=pairFst old)
    (hfit : (family P D H).birth old≤(family P D H).birth terminal)

include hroot in
theorem denominator (i : Fin ((family P D H).birth old)) :
    ((family P D H).state terminal).bank.denominator (embed hfit i)=
      ((family P D H).state old).bank.denominator i :=by
  have HB : prefixLength P terminal-1-(embed hfit i).val=prefixLength P old-1-i.val :=by
    rw [←IntegralMixedFramedHistoryFamilyBits.family_birth P D H terminal,
      ←IntegralMixedFramedHistoryFamilyBits.family_birth P D H old]
    dsimp only [embed]
    have HI:=i.isLt
    omega
  have HK : keyAt (pairFst terminal) (prefixLength P terminal-1-(embed hfit i).val) []=
      keyAt (pairFst old) (prefixLength P old-1-i.val) []:=
    congrArg₂ (fun root birth=>keyAt root birth []) hroot HB
  have HT : ((family P D H).state terminal).bank.denominator (embed hfit i)=
      IntegralMixedFramedCompanionBits.leading P D H
        (keyAt (pairFst terminal) (prefixLength P terminal-1-(embed hfit i).val) []) :=
    IntegralMixedFramedHistoryFamilyBits.retained_leading_key P D H terminal (embed hfit i) []
  have HO : ((family P D H).state old).bank.denominator i=
      IntegralMixedFramedCompanionBits.leading P D H (keyAt (pairFst old) (prefixLength P old-1-i.val) []) :=
    IntegralMixedFramedHistoryFamilyBits.retained_leading_key P D H old i []
  exact HT.trans ((congrArg (IntegralMixedFramedCompanionBits.leading P D H) HK).trans HO.symm)

include hroot in
theorem point (z : Fin ((family P D H).birth terminal)→ℝ) (i : Fin ((family P D H).birth old)) :
    IntegralMixedCanonicalBankPoint.point ((family P D H).state old) (z∘embed hfit) i=
      IntegralMixedCanonicalBankPoint.point ((family P D H).state terminal) z (embed hfit i) :=by
  have HC : (family P D H).cap terminal=(family P D H).cap old:=
    congrArg (fun root=>P.cap root+1) hroot
  have HW : (family P D H).width terminal=(family P D H).width old:=congrArg P.width hroot
  have HP : weights ((family P D H).cap old) (2^(family P D H).width old) ((family P D H).birth old) i=
      weights ((family P D H).cap terminal) (2^(family P D H).width terminal) ((family P D H).birth terminal) (embed hfit i) :=by
    rw [HC,HW]
    exact (old_embed _ _ hfit i).symm
  exact congrArg₂ (fun (a : ℝ) (d : ℤ)=>a/(d:ℝ))
    (congrArg (fun w=>z (embed hfit i)^w) HP) (denominator P D H old terminal hroot hfit i).symm

include hroot in
theorem point_cons (z : Fin ((family P D H).birth terminal)→ℝ)
    (hc : (family P D H).birth old+1=(family P D H).birth terminal)
    (i : Fin ((family P D H).birth old+1)) :
    IntegralMixedCanonicalBankPoint.point ((family P D H).state terminal) z (Fin.cast hc i)=
      (Fin.cons (α:=fun _ : Fin ((family P D H).birth old+1)=>ℝ)
        (IntegralMixedCanonicalBankPoint.point ((family P D H).state terminal) z (Fin.cast hc 0))
        (IntegralMixedCanonicalBankPoint.point ((family P D H).state old) (z∘embed hfit))) i :=by
  refine Fin.cases rfl (fun j=>?_) i
  have HI : Fin.cast hc j.succ=embed hfit j:=by
    apply Fin.ext
    dsimp only [Fin.val_cast,Fin.val_succ,embed]
    omega
  change IntegralMixedCanonicalBankPoint.point ((family P D H).state terminal) z (Fin.cast hc j.succ)=_
  rw [HI]
  exact (point P D H old terminal hroot hfit z j).symm

end LeanCanny.Algebra.IntegralMixedFramedBankObservationShift
