/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalNaturalWitness
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalBankObservations
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalPointCorrelation
/-! # The complete native search is exactly the actual joint-witness search -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalInterval
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open FormulaSignSlotRadialProviderCriticalPrefixes (birth key input positive)
open IntegralMixedFramedHistoryFamilyBits (family instruction)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "BK" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "K" => FormulaSignSlotRadialProviderCriticalPrefixes.key false
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank

noncomputable def parentArray (q : List Bool)
    (hp : SquareSampleCompleteVertices.Valid (input false) q
      (IntegralMixedPhysicalCriticalQuery.parentWord q)) : ℕ→ℝ :=
  IntegralFramedPhysicalSquare.naturalPoint (BK).parameters (BK).plan (BK).data
    (BK).nodes (BK).factor (BK).seed (BK).bounds (K) (positive false)
    q (IntegralMixedPhysicalCriticalQuery.parentWord q) hp

theorem parentArray_joint (q : List Bool)
    (hp : SquareSampleCompleteVertices.Valid (input false) q
      (IntegralMixedPhysicalCriticalQuery.parentWord q))
    (j : Fin (IntegralFramedPhysicalSquare.count (BK).parameters (BK).plan (K q))) :
    IntegralFramedPhysicalSquare.joint (BK).parameters (BK).plan (BK).data
      (BK).nodes (BK).factor (BK).seed (BK).bounds (K) (positive false)
      q (IntegralMixedPhysicalCriticalQuery.parentWord q) hp j=parentArray q hp j.val :=
  (IntegralFramedPhysicalSquare.naturalPoint_at (BK).parameters (BK).plan (BK).data
    (BK).nodes (BK).factor (BK).seed (BK).bounds (K) (positive false)
    q (IntegralMixedPhysicalCriticalQuery.parentWord q) hp j).symm

theorem language_iff_naturalWitness (q : List Bool)
    (hp : SquareSampleCompleteVertices.Valid (input false) q
      (IntegralMixedPhysicalCriticalQuery.parentWord q)) (hg : Guard q)
    (F : IntegralMixedFrozenFrame.Frame ((BK).parameters.ambient (pairFst (K q))))
    (HP : IntegralMixedFrozenFrame.PrefixFrozen F)
    (HA : IntegralMixedFrozenFrame.AtomicRows F ((family (BK).parameters (BK).plan (BK).data).birth (K q)))
    (h : Fin ((BK).parameters.ambient (pairFst (K q))+1)) (hh : h∉F.frozen)
    (hc : (instruction (BK).parameters (BK).plan (K q)).command=.critical (HA.pointData h h hh hh).rule) :
    q∈language ↔
      ∃u∈Set.Ioo
        (endpointValue q hp (Nat.fromBitsLE (IntegralMixedPhysicalCriticalQuery.leftWord q)))
        (endpointValue q hp (Nat.fromBitsLE (IntegralMixedPhysicalCriticalQuery.rightWord q))),
        NaturalWitness q F HA h hh (parentArray q hp) u :=by
  change (∃w,w.length=width q ∧ pair q w∈witnessLanguage)↔_
  constructor
  · rintro ⟨w,_,hw⟩
    simp only [witnessLanguage,Set.mem_ofPred_eq,pairFst_pair,pairSnd_pair] at hw
    obtain ⟨_,_,hv,hagree,hcorr,hlo,hhi⟩:=hw
    let z:=IntegralFramedPhysicalSquare.naturalPoint (BK).parameters (BK).plan (BK).data
      (BK).nodes (BK).factor (BK).seed (BK).bounds (key true) (positive true) q w hv
    have HZ (j : Fin (IntegralFramedPhysicalSquare.count (BK).parameters (BK).plan (key true q))) :
        IntegralFramedPhysicalSquare.joint (BK).parameters (BK).plan (BK).data
          (BK).nodes (BK).factor (BK).seed (BK).bounds (key true)
          (positive true) q w hv j=z j.val :=
      (IntegralFramedPhysicalSquare.naturalPoint_at (BK).parameters (BK).plan (BK).data
        (BK).nodes (BK).factor (BK).seed (BK).bounds (key true)
        (positive true) q w hv j).symm
    have HC : newestPoint q w hv=stepPoint q F HA h hh z :=by
      exact (correlation_iff_pointRule_at q w hv z HZ F HP HA h hh hc).mp hcorr
    have HI:=(interval_iff_parent q w hp hv hg hagree).mp ⟨hlo,hhi⟩
    rw [HC] at HI
    refine ⟨_,HI,z,IntegralFramedPhysicalSquare.naturalPoint_roots _ _ _ _ _ _ _ _ _ _ _ _,?_,?_,rfl⟩
    · intro i
      have hi : i.val<birth false q :=by
        simpa only [FormulaSignSlotRadialProviderCriticalPrefixes.key_birth false q] using i.isLt
      have HE:=(agrees_iff_observations q w hp hv z HZ).mp hagree i.val hi
      have HR:=IntegralMixedPhysicalCriticalObservation.retained_observation (BK).parameters (BK).plan (BK).data
        (K q) (HA.pointData h h hh hh).rule z q (parent_room q) hc i
      rw [←child_key q] at HR
      exact (bank_point_observation false q _ hp _
        (parentArray_joint q hp) i.val hi).symm.trans (HE.trans HR)
    · exact (newest_observation q w hv z HZ).symm.trans HC
  · rintro ⟨u,hu,z,hz,hm,hnew,ht0⟩
    obtain ⟨w,hv,HZ⟩:=IntegralFramedPhysicalSquare.exists_joint_natural (BK).parameters (BK).plan (BK).data
      (BK).nodes (BK).factor (BK).seed (BK).bounds (key true) (positive true) q z hz
    have HAgree : FormulaSignSlotRadialProviderCriticalBankEquality.agrees (pair q w) :=by
      apply (agrees_iff_observations q w hp hv z HZ).mpr
      intro i hi
      let j : Fin ((family (BK).parameters (BK).plan (BK).data).birth (K q)):=⟨i,by
        rw [FormulaSignSlotRadialProviderCriticalPrefixes.key_birth]
        exact hi⟩
      have HR:=IntegralMixedPhysicalCriticalObservation.retained_observation (BK).parameters (BK).plan (BK).data
        (K q) (HA.pointData h h hh hh).rule z q (parent_room q) hc j
      rw [←child_key q] at HR
      exact (bank_point_observation false q _ hp _
        (parentArray_joint q hp) i hi).trans ((hm j).trans HR.symm)
    have HC : newestPoint q w hv=stepPoint q F HA h hh z :=
      (newest_observation q w hv z HZ).trans hnew
    have HCorr:=(correlation_iff_pointRule_at q w hv z HZ F HP HA h hh hc).mpr HC
    have HI : value false (pair q w)=InfinitesimalSign.encode 1 ∧
        value true (pair q w)=InfinitesimalSign.encode 1 :=by
      apply (interval_iff_parent q w hp hv hg HAgree).mpr
      rw [HC,ht0]
      exact hu
    refine ⟨w,?_,?_⟩
    · exact (Classical.choose hv).1
    · simpa only [witnessLanguage,Set.mem_ofPred_eq,pairFst_pair,pairSnd_pair] using
        And.intro hg (And.intro hp (And.intro hv (And.intro HAgree (And.intro HCorr HI))))

end LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalInterval
