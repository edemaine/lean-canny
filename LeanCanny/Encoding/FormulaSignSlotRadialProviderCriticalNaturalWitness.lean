/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalStageMetadata
public import LeanCanny.Encoding.IntegralMixedPhysicalCriticalStepCapture
public import LeanCanny.Encoding.IntegralMixedPhysicalCriticalObservation
public import LeanCanny.Geometry.IntegralMixedRealCriticalWitness
/-! # Natural-column witnesses are exactly the literal geometric witnesses -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalInterval
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open FormulaSignSlotRadialProviderCriticalPrefixes (key)
open IntegralMixedFramedHistoryFamilyBits (family instruction)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "BK" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "T" => FormulaSignSlotRadialProviderRecordPlan.tables
local notation "K" => FormulaSignSlotRadialProviderCriticalPrefixes.key false
local notation "NR" => FormulaSignSlotRadialProviderAtomic.bank_represents
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank FormulaSignSlotRadialProviderRecordPlan.tables

noncomputable local instance familyFintype (q : List Bool) : Fintype ((family (BK).parameters (BK).plan (BK).data).physical (K q)) :=
  inferInstanceAs (Fintype (IntegralMixedFramedHistoryScript.Index (Fin 0)
    (IntegralMixedFramedHistoryFamilyBits.commands (BK).parameters (BK).plan (K q))))


noncomputable def stepPoint (q : List Bool)
    (F : IntegralMixedFrozenFrame.Frame ((BK).parameters.ambient (pairFst (K q))))
    (HA : IntegralMixedFrozenFrame.AtomicRows F ((family (BK).parameters (BK).plan (BK).data).birth (K q)))
    (h : Fin ((BK).parameters.ambient (pairFst (K q))+1)) (hh : h∉F.frozen) (z : ℕ→ℝ) : ℝ :=
  IntegralMixedCriticalReadback.point (S:=(family (BK).parameters (BK).plan (BK).data).cap (K q)) (B:=(family (BK).parameters (BK).plan (BK).data).width (K q)) (m:=(family (BK).parameters (BK).plan (BK).data).birth (K q))
    (IntegralMixedFramedCriticalSuccessorRows.tuple (BK).parameters (BK).plan (BK).data (K q)
      (HA.pointData h h hh hh).rule z) h

noncomputable def NaturalWitness (q : List Bool)
    (F : IntegralMixedFrozenFrame.Frame ((BK).parameters.ambient (pairFst (K q))))
    (HA : IntegralMixedFrozenFrame.AtomicRows F ((family (BK).parameters (BK).plan (BK).data).birth (K q)))
    (h : Fin ((BK).parameters.ambient (pairFst (K q))+1)) (hh : h∉F.frozen) (parent : ℕ→ℝ) (u : ℝ) : Prop :=
  ∃z : ℕ→ℝ,
    (∀i,(IntegralMixedFramedPhysicalRowTransport.keyRow (BK).parameters (BK).plan (key true q) i).eval₂
      (Int.castRingHom ℝ) z=0) ∧
    (∀i : Fin ((family (BK).parameters (BK).plan (BK).data).birth (K q)),
      (IntegralMixedFullBankObservation.atFamily (BK).parameters (BK).plan (BK).data (K q)).point parent i.val=
        (IntegralMixedFullBankObservation.atFamily (BK).parameters (BK).plan (BK).data (K q)).point z i.val) ∧
    (IntegralMixedFullBankObservation.atFamily (BK).parameters (BK).plan (BK).data (key true q)).point z 0=
      stepPoint q F HA h hh z ∧
    stepPoint q F HA h hh z=u

theorem naturalWitness_iff_actual (q : List Bool)
  (F : IntegralMixedFrozenFrame.Frame ((BK).parameters.ambient (pairFst (K q))))
  (HA : IntegralMixedFrozenFrame.AtomicRows F ((family (BK).parameters (BK).plan (BK).data).birth (K q)))
  (h : Fin ((BK).parameters.ambient (pairFst (K q))+1)) (hh : h∉F.frozen)
 (parent : ℕ→ℝ) (u : ℝ)
    (hc : (instruction (BK).parameters (BK).plan (K q)).command=.critical (HA.pointData h h hh hh).rule)
    (φ : ((family (BK).parameters (BK).plan (BK).data).state (K q)).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀i,φ (((family (BK).parameters (BK).plan (BK).data).state (K q)).bank.numerator i)/(((family (BK).parameters (BK).plan (BK).data).state (K q)).bank.denominator i:ℝ)=
      (IntegralMixedFullBankObservation.atFamily (BK).parameters (BK).plan (BK).data (K q)).point parent i.val) :
    NaturalWitness q F HA h hh parent u ↔
      IntegralMixedFrozenFrame.RealCriticalWitness ((family (BK).parameters (BK).plan (BK).data).state (K q)) ((family (BK).parameters (BK).plan (BK).data).birth_bound (K q)) F HA h hh φ u :=by
  constructor
  · rintro ⟨z,hz,hm,hn0,ht0⟩
    refine ⟨IntegralMixedFramedCriticalSuccessorRows.tuple (BK).parameters (BK).plan (BK).data (K q)
      (HA.pointData h h hh hh).rule z,?_,?_,?_,ht0⟩
    · apply (IntegralMixedFramedCriticalSuccessorRows.rows_zero_iff _ _ _ (K q) _ z).mp
      intro i
      have HE:=hz i
      rw [child_key q,
        IntegralMixedFramedCriticalSuccessorRows.keyRow_successor _ _ _ (K q) q
          (parent_room q) _ hc i] at HE
      exact HE
    · intro i
      exact (hφ i).trans ((hm i).trans
        (IntegralMixedPhysicalCriticalObservation.old_observation _ _ _ (K q) _ z i))
    · have HE:=IntegralMixedPhysicalCriticalObservation.new_observation (BK).parameters (BK).plan (BK).data
        (K q) (HA.pointData h h hh hh).rule z q (parent_room q) hc
      rw [←child_key q] at HE
      exact HE.symm.trans hn0
  · rintro ⟨y,hy,hm,hn0,ht0⟩
    let z:=IntegralMixedPhysicalCriticalStepCapture.natural (BK).parameters (BK).plan (BK).data
      (K q) (HA.pointData h h hh hh).rule y
    have HT:=IntegralMixedPhysicalCriticalStepCapture.tuple_natural (BK).parameters (BK).plan (BK).data
      (K q) (HA.pointData h h hh hh).rule y
    refine ⟨z,?_,?_,?_,?_⟩
    · intro i
      rw [child_key q,
        IntegralMixedFramedCriticalSuccessorRows.keyRow_successor _ _ _ (K q) q
          (parent_room q) _ hc i]
      exact IntegralMixedPhysicalCriticalStepCapture.roots_natural _ _ _ (K q) _ y hy i
    · intro i
      have HE:=IntegralMixedPhysicalCriticalObservation.old_observation (BK).parameters (BK).plan (BK).data
        (K q) (HA.pointData h h hh hh).rule z i
      change _=IntegralMixedCanonicalBankPoint.point _
        (fun j=>IntegralMixedFramedCriticalSuccessorRows.tuple _ _ _ (K q) _ z
          (Sum.inl (Sum.inl (((family (BK).parameters (BK).plan (BK).data).state (K q)).sampler.scalar j)))) i at HE
      rw [HT] at HE
      exact (hφ i).symm.trans ((hm i).trans HE.symm)
    · have HE:=IntegralMixedPhysicalCriticalObservation.new_observation (BK).parameters (BK).plan (BK).data
        (K q) (HA.pointData h h hh hh).rule z q (parent_room q) hc
      rw [←child_key q,HT] at HE
      unfold stepPoint
      rw [HT]
      exact HE.trans hn0
    · unfold stepPoint
      rw [HT]
      exact ht0

end LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalInterval
