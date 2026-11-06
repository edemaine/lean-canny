/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalNativeWitness
/-! # The native probe language detects exactly actual real critical heights

The old interpreting hom is derived from the fixed parent complete word.
Both directions use the actual successor's full rows and the same bank.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalInterval
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open FormulaSignSlotRadialProviderCriticalPrefixes (key input positive)
open IntegralMixedFramedHistoryFamilyBits (family instruction)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "BK" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "K" => FormulaSignSlotRadialProviderCriticalPrefixes.key false
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank
  IntegralMixedHistory.reframe IntegralMixedFramedHistoryScript.run

noncomputable local instance languageFamilyFintype (q : List Bool) :
    Fintype ((family (BK).parameters (BK).plan (BK).data).physical (K q)) :=
  inferInstanceAs (Fintype (IntegralMixedFramedHistoryScript.Index (Fin 0)
    (IntegralMixedFramedHistoryFamilyBits.commands (BK).parameters (BK).plan (K q))))

noncomputable def parentValues (q : List Bool)
    (hp : SquareSampleCompleteVertices.Valid (input false) q
      (IntegralMixedPhysicalCriticalQuery.parentWord q))
    (i : Fin ((family (BK).parameters (BK).plan (BK).data).birth (K q))) : ℝ :=
  (IntegralMixedFullBankObservation.atFamily (BK).parameters (BK).plan (BK).data (K q)).point
    (parentArray q hp) i.val

theorem language_iff_realCritical (q : List Bool)
    (hp : SquareSampleCompleteVertices.Valid (input false) q
      (IntegralMixedPhysicalCriticalQuery.parentWord q)) (hg : Guard q)
    (F : IntegralMixedFrozenFrame.Frame ((BK).parameters.ambient (pairFst (K q))))
    (HP : IntegralMixedFrozenFrame.PrefixFrozen F) (HF : IntegralMixedFrozenFrame.FreeNormal F)
    (HA : IntegralMixedFrozenFrame.AtomicRows F ((family (BK).parameters (BK).plan (BK).data).birth (K q)))
    (h : Fin ((BK).parameters.ambient (pairFst (K q))+1)) (hh : h∉F.frozen)
    (hc : (instruction (BK).parameters (BK).plan (K q)).command=.critical (HA.pointData h h hh hh).rule)
    (hn0 : 0<(family (BK).parameters (BK).plan (BK).data).ambient (K q)) (charge : ℕ)
    (hd : ((family (BK).parameters (BK).plan (BK).data).spatial (K q)).degree=BoundedZeroSource.powerDegree charge)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap
      ((family (BK).parameters (BK).plan (BK).data).ambient (K q)+1)
      ((family (BK).parameters (BK).plan (BK).data).spatial (K q)).degree≤
        2^(family (BK).parameters (BK).plan (BK).data).width (K q)) :
    q∈language ↔
      ∃u∈Set.Ioo
        (endpointValue q hp (Nat.fromBitsLE (IntegralMixedPhysicalCriticalQuery.leftWord q)))
        (endpointValue q hp (Nat.fromBitsLE (IntegralMixedPhysicalCriticalQuery.rightWord q))),
      u∈IntegralMixedFrozenFrame.realCriticalValues
        ((family (BK).parameters (BK).plan (BK).data).spatial (K q))
        (IntegralMixedFrozenFrame.line F h) (parentValues q hp) h :=by
  have HInterp:=IntegralFramedPhysicalSquare.exists_interpretation (BK).parameters (BK).plan (BK).data
    (BK).nodes (BK).factor (BK).seed (BK).bounds (K) (positive false)
    q (IntegralMixedPhysicalCriticalQuery.parentWord q) hp
  rcases HInterp with ⟨φ,Hφ,Hvalues⟩
  have HV (i : Fin ((family (BK).parameters (BK).plan (BK).data).birth (K q))) :
      φ (((family (BK).parameters (BK).plan (BK).data).state (K q)).bank.numerator i)/
        (((family (BK).parameters (BK).plan (BK).data).state (K q)).bank.denominator i:ℝ)=
        parentValues q hp i :=
    (Hvalues i).trans (IntegralFramedPhysicalSquare.bank_naturalPoint (BK).parameters (BK).plan (BK).data
      (BK).nodes (BK).factor (BK).seed (BK).bounds (K) (positive false)
      q (IntegralMixedPhysicalCriticalQuery.parentWord q) hp i).symm
  have HE (u : ℝ) : NaturalWitness q F HA h hh (parentArray q hp) u ↔
      u∈IntegralMixedFrozenFrame.realCriticalValues
        ((family (BK).parameters (BK).plan (BK).data).spatial (K q))
        (IntegralMixedFrozenFrame.line F h) (parentValues q hp) h :=by
    apply (naturalWitness_iff_actual q F HA h hh _ u hc φ HV).trans
    exact IntegralMixedFrozenFrame.realCriticalWitness_iff
      ((family (BK).parameters (BK).plan (BK).data).state (K q))
      (IntegralMixedFramedHistoryFamilyBits.family_canonical (BK).parameters (BK).plan (BK).data (K q))
      ((family (BK).parameters (BK).plan (BK).data).birth_bound (K q)) hn0 charge hd hcap F HA HP HF h hh
      (IntegralFramedPhysicalSquare.rawPoint (BK).parameters (BK).plan (BK).data
        (BK).nodes (BK).factor (BK).seed (BK).bounds (K) (positive false)
        q (IntegralMixedPhysicalCriticalQuery.parentWord q) hp)
      (IntegralFramedPhysicalSquare.raw_roots (BK).parameters (BK).plan (BK).data
        (BK).nodes (BK).factor (BK).seed (BK).bounds (K) (positive false)
        q (IntegralMixedPhysicalCriticalQuery.parentWord q) hp) φ
      (by simpa only [IntegralFramedPhysicalSquare.rawPoint,Function.comp_apply] using Hφ)
      (parentValues q hp) HV u
  rw [language_iff_naturalWitness q hp hg F HP HA h hh hc]
  constructor
  · rintro ⟨u,hu,hw⟩
    exact ⟨u,hu,(HE u).mp hw⟩
  · rintro ⟨u,hu,hw⟩
    exact ⟨u,hu,(HE u).mpr hw⟩

theorem not_language_iff_disjoint (q : List Bool)
    (hp : SquareSampleCompleteVertices.Valid (input false) q
      (IntegralMixedPhysicalCriticalQuery.parentWord q)) (hg : Guard q)
    (F : IntegralMixedFrozenFrame.Frame ((BK).parameters.ambient (pairFst (K q))))
    (HP : IntegralMixedFrozenFrame.PrefixFrozen F) (HF : IntegralMixedFrozenFrame.FreeNormal F)
    (HA : IntegralMixedFrozenFrame.AtomicRows F ((family (BK).parameters (BK).plan (BK).data).birth (K q)))
    (h : Fin ((BK).parameters.ambient (pairFst (K q))+1)) (hh : h∉F.frozen)
    (hc : (instruction (BK).parameters (BK).plan (K q)).command=.critical (HA.pointData h h hh hh).rule)
    (hn0 : 0<(family (BK).parameters (BK).plan (BK).data).ambient (K q)) (charge : ℕ)
    (hd : ((family (BK).parameters (BK).plan (BK).data).spatial (K q)).degree=BoundedZeroSource.powerDegree charge)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap
      ((family (BK).parameters (BK).plan (BK).data).ambient (K q)+1)
      ((family (BK).parameters (BK).plan (BK).data).spatial (K q)).degree≤
        2^(family (BK).parameters (BK).plan (BK).data).width (K q)) :
    q∉language ↔
      Disjoint
        (Set.Ioo
          (endpointValue q hp (Nat.fromBitsLE (IntegralMixedPhysicalCriticalQuery.leftWord q)))
          (endpointValue q hp (Nat.fromBitsLE (IntegralMixedPhysicalCriticalQuery.rightWord q))))
        (IntegralMixedFrozenFrame.realCriticalValues
          ((family (BK).parameters (BK).plan (BK).data).spatial (K q))
          (IntegralMixedFrozenFrame.line F h) (parentValues q hp) h) :=by
  rw [language_iff_realCritical q hp hg F HP HF HA h hh hc hn0 charge hd hcap,
    Set.disjoint_left]
  constructor
  · intro HN u hu hc0
    exact HN ⟨u,hu,hc0⟩
  · intro HD ⟨u,hu,hc0⟩
    exact HD hu hc0

end LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalInterval
