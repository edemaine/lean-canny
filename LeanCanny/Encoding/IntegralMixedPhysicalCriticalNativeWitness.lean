/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalCriticalNaturalWitness
public import LeanCanny.Encoding.IntegralMixedPhysicalCriticalBankObservations
public import LeanCanny.Encoding.IntegralMixedPhysicalCriticalPointCorrelation
/-! # The complete native search is exactly the actual joint-witness search -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalCriticalInterval
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedPhysicalMarkedPlan (bank)
open IntegralMixedPhysicalCriticalPrefixes (birth key input positive)
open IntegralMixedFramedHistoryFamilyBits (family instruction)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R) (outer : Bool)
attribute [local irreducible] bank
local notation "BK" => bank hn ht ha hR outer
local notation "K" => key n outer false

noncomputable def parentArray (q : List Bool)
    (hp : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer false) q
      (IntegralMixedPhysicalCriticalQuery.parentWord q)) : ℕ→ℝ :=
  IntegralFramedPhysicalSquare.naturalPoint (BK).parameters (BK).plan (BK).data
    (BK).nodes (BK).factor (BK).seed (BK).bounds (K) (positive hn ht ha hR outer false)
    q (IntegralMixedPhysicalCriticalQuery.parentWord q) hp

theorem parentArray_joint (q : List Bool)
    (hp : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer false) q
      (IntegralMixedPhysicalCriticalQuery.parentWord q))
    (j : Fin (IntegralFramedPhysicalSquare.count (BK).parameters (BK).plan (K q))) :
    IntegralFramedPhysicalSquare.joint (BK).parameters (BK).plan (BK).data
      (BK).nodes (BK).factor (BK).seed (BK).bounds (K) (positive hn ht ha hR outer false)
      q (IntegralMixedPhysicalCriticalQuery.parentWord q) hp j=parentArray hn ht ha hR outer q hp j.val :=
  (IntegralFramedPhysicalSquare.naturalPoint_at (BK).parameters (BK).plan (BK).data
    (BK).nodes (BK).factor (BK).seed (BK).bounds (K) (positive hn ht ha hR outer false)
    q (IntegralMixedPhysicalCriticalQuery.parentWord q) hp j).symm

theorem language_iff_naturalWitness (q : List Bool)
    (hp : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer false) q
      (IntegralMixedPhysicalCriticalQuery.parentWord q)) (hg : Guard n outer q)
    (F : IntegralMixedFrozenFrame.Frame ((BK).parameters.ambient (pairFst (K q))))
    (HP : IntegralMixedFrozenFrame.PrefixFrozen F)
    (HA : IntegralMixedFrozenFrame.AtomicRows F ((family (BK).parameters (BK).plan (BK).data).birth (K q)))
    (h : Fin ((BK).parameters.ambient (pairFst (K q))+1)) (hh : h∉F.frozen)
    (hc : (instruction (BK).parameters (BK).plan (K q)).command=.critical (HA.pointData h h hh hh).rule) :
    q∈language hn ht ha hR outer ↔
      ∃u∈Set.Ioo
        (endpointValue hn ht ha hR outer q hp (Nat.fromBitsLE (IntegralMixedPhysicalCriticalQuery.leftWord q)))
        (endpointValue hn ht ha hR outer q hp (Nat.fromBitsLE (IntegralMixedPhysicalCriticalQuery.rightWord q))),
        NaturalWitness hn ht ha hR outer q F HA h hh (parentArray hn ht ha hR outer q hp) u :=by
  change (∃w,w.length=width hn ht ha hR outer q ∧ pair q w∈witnessLanguage hn ht ha hR outer)↔_
  constructor
  · rintro ⟨w,_,hw⟩
    simp only [witnessLanguage,Set.mem_ofPred_eq,pairFst_pair,pairSnd_pair] at hw
    obtain ⟨_,_,hv,hagree,hcorr,hlo,hhi⟩:=hw
    let z:=IntegralFramedPhysicalSquare.naturalPoint (BK).parameters (BK).plan (BK).data
      (BK).nodes (BK).factor (BK).seed (BK).bounds (key n outer true) (positive hn ht ha hR outer true) q w hv
    have HZ (j : Fin (IntegralFramedPhysicalSquare.count (BK).parameters (BK).plan (key n outer true q))) :
        IntegralFramedPhysicalSquare.joint (BK).parameters (BK).plan (BK).data
          (BK).nodes (BK).factor (BK).seed (BK).bounds (key n outer true)
          (positive hn ht ha hR outer true) q w hv j=z j.val :=
      (IntegralFramedPhysicalSquare.naturalPoint_at (BK).parameters (BK).plan (BK).data
        (BK).nodes (BK).factor (BK).seed (BK).bounds (key n outer true)
        (positive hn ht ha hR outer true) q w hv j).symm
    have HC : newestPoint hn ht ha hR outer q w hv=stepPoint hn ht ha hR outer q F HA h hh z :=by
      exact (correlation_iff_pointRule_at hn ht ha hR outer q w hv z HZ F HP HA h hh hc).mp hcorr
    have HI:=(interval_iff_parent hn ht ha hR outer q w hp hv hg hagree).mp ⟨hlo,hhi⟩
    rw [HC] at HI
    refine ⟨_,HI,z,IntegralFramedPhysicalSquare.naturalPoint_roots _ _ _ _ _ _ _ _ _ _ _ _,?_,?_,rfl⟩
    · intro i
      have hi : i.val<birth n outer false q :=by
        simpa only [IntegralMixedPhysicalCriticalPrefixes.key_birth hn ht ha hR outer false q] using i.isLt
      have HE:=(agrees_iff_observations hn ht ha hR outer q w hp hv z HZ).mp hagree i.val hi
      have HR:=IntegralMixedPhysicalCriticalObservation.retained_observation (BK).parameters (BK).plan (BK).data
        (K q) (HA.pointData h h hh hh).rule z q (parent_room hn ht ha hR outer q) hc i
      rw [←child_key hn ht ha hR outer q] at HR
      exact (bank_point_observation hn ht ha hR outer false q _ hp _
        (parentArray_joint hn ht ha hR outer q hp) i.val hi).symm.trans (HE.trans HR)
    · exact (newest_observation hn ht ha hR outer q w hv z HZ).symm.trans HC
  · rintro ⟨u,hu,z,hz,hm,hnew,ht0⟩
    obtain ⟨w,hv,HZ⟩:=IntegralFramedPhysicalSquare.exists_joint_natural (BK).parameters (BK).plan (BK).data
      (BK).nodes (BK).factor (BK).seed (BK).bounds (key n outer true) (positive hn ht ha hR outer true) q z hz
    have HAgree : IntegralMixedPhysicalCriticalBankEquality.agrees hn ht ha hR outer (pair q w) :=by
      apply (agrees_iff_observations hn ht ha hR outer q w hp hv z HZ).mpr
      intro i hi
      let j : Fin ((family (BK).parameters (BK).plan (BK).data).birth (K q)):=⟨i,by
        rw [IntegralMixedPhysicalCriticalPrefixes.key_birth hn ht ha hR outer]
        exact hi⟩
      have HR:=IntegralMixedPhysicalCriticalObservation.retained_observation (BK).parameters (BK).plan (BK).data
        (K q) (HA.pointData h h hh hh).rule z q (parent_room hn ht ha hR outer q) hc j
      rw [←child_key hn ht ha hR outer q] at HR
      exact (bank_point_observation hn ht ha hR outer false q _ hp _
        (parentArray_joint hn ht ha hR outer q hp) i hi).trans ((hm j).trans HR.symm)
    have HC : newestPoint hn ht ha hR outer q w hv=stepPoint hn ht ha hR outer q F HA h hh z :=
      (newest_observation hn ht ha hR outer q w hv z HZ).trans hnew
    have HCorr:=(correlation_iff_pointRule_at hn ht ha hR outer q w hv z HZ F HP HA h hh hc).mpr HC
    have HI : value hn ht ha hR outer false (pair q w)=InfinitesimalSign.encode 1 ∧
        value hn ht ha hR outer true (pair q w)=InfinitesimalSign.encode 1 :=by
      apply (interval_iff_parent hn ht ha hR outer q w hp hv hg HAgree).mpr
      rw [HC,ht0]
      exact hu
    refine ⟨w,?_,?_⟩
    · exact (Classical.choose hv).1
    · simpa only [witnessLanguage,Set.mem_ofPred_eq,pairFst_pair,pairSnd_pair] using
        And.intro hg (And.intro hp (And.intro hv (And.intro HAgree (And.intro HCorr HI))))

end LeanCanny.Encoding.IntegralMixedPhysicalCriticalInterval
