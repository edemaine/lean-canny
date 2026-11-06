/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalInterval
public import LeanCanny.Algebra.IntegralMixedFramedCriticalGuardOrigin
/-! # The appended critical guard compares the actual newest bank quotient

The physical coordinate is read from the same complete child tuple with its
creating power. No interpreting hom or simplicity of roots is assumed.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalInterval
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open FormulaSignSlotRadialProviderCriticalPrefixes (birth key input positive)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "NB" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "NT" => FormulaSignSlotRadialProviderRecordPlan.tables
local notation "NR" => FormulaSignSlotRadialProviderAtomic.bank_represents
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank FormulaSignSlotRadialProviderRecordPlan.tables

private theorem indexedPoint_cast {n S B m a b : ℕ} {P : IntegralMixedHistory.SpatialSource n}
    {ι : Type} (x : IntegralMixedHistory.State P S B m ι)
    (e : ι≃Fin a) (h : b=a) (z : Fin a→ℝ) :
    IntegralMixedFullBankPoint.indexedPoint x (e.trans (finCongr h.symm)) (fun i=>z (Fin.cast h i))=
      IntegralMixedFullBankPoint.indexedPoint x e z :=by
  cases h
  rfl

private theorem indexedPoint_key_cast (G : IntegralMixedCutSource.Family)
    (a : List Bool→ℕ) (e : ∀k,G.physical k≃Fin (a k))
    (k l : List Bool) (hk : k=l) (b : ℕ) (h : b=a k) (h' : b=a l) (z : Fin (a l)→ℝ)
    (i : Fin (G.birth k)) (j : Fin (G.birth l)) (hij : i.val=j.val) :
    IntegralMixedFullBankPoint.indexedPoint (G.state k) ((e k).trans (finCongr h.symm))
      (fun t=>z (Fin.cast h' t)) i=
      IntegralMixedFullBankPoint.indexedPoint (G.state l) (e l) z j :=by
  cases hk
  have HI : i=j:=Fin.ext hij
  cases HI
  exact congrFun (indexedPoint_cast (G.state k) (e k) h z) i

private theorem guard_packet (S : SquareSampleInput.Inputs) (P : Parameters)
    (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (T : IntegralMixedHeaderTablesBits.Tables) (L F C : List Bool→ℕ)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (key : List Bool→List Bool) (stage : List Bool→ℕ)
    (hcount : ∀ c d,IntegralMixedFramedCriticalGuardBits.count P T
      (IntegralFramedPhysicalCriticalGuardTest.keyDatum key) (pair c d)=S.count c)
    (c w d : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w) :
    IntegralFramedPhysicalCriticalGuardTest.value S P D H T L F C hs key stage hcount
      (pair (pair c w) d)=InfinitesimalSign.encode (SignType.sign
        ((IntegralMixedFramedCriticalGuardBits.polynomial P D H T
          (IntegralFramedPhysicalCriticalGuardTest.keyDatum key) stage (pair c d)).eval₂
            (Int.castRingHom ℝ) (fun i=>(SquareSampleCompleteVertices.candidate S c w hv).val
              (Fin.cast (hcount c d) i)))) :=by
  simpa only [IntegralFramedPhysicalCriticalGuardTest.source,FixedWidthSuffixLiftBits.shift,
    Nat.zero_add,Fin.cast] using
    IntegralFramedPhysicalCriticalGuardTest.packet S P D H T L F C hs key stage hcount c w d hv

noncomputable def correlationTuple (q v : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input true) q v) :
    Fin (IntegralMixedFramedCriticalGuardBits.count (NB).parameters
      NT (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key true)) (pair q []))→ℝ :=
  fun i=>(SquareSampleCompleteVertices.candidate (input true) q v hv).val
    (Fin.cast (guard_count q []) i)

theorem correlation_age (q : List Bool) :
    IntegralMixedFramedCriticalGuardBits.age (NB).parameters
      (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key true)) (stage) (pair q [])=0 :=by
  have HB:=FormulaSignSlotRadialProviderCriticalPrefixes.key_birth true q
  rw [IntegralMixedFramedHistoryFamilyBits.family_birth] at HB
  simp only [IntegralMixedFramedCriticalGuardBits.age,IntegralFramedPhysicalCriticalGuardTest.keyDatum,
    stage,pairFst_pair,HB,FormulaSignSlotRadialProviderCriticalPrefixes.consecutive]
  omega

theorem correlation_actualPoint (q v : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input true) q v)
    (hactive : IntegralMixedFramedCriticalGuardBits.Active (NB).parameters
      NT (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key true))
      (stage) (pair q [])) :
    IntegralMixedFramedCriticalGuard.actualPoint (NB).parameters
      (NB).plan (NB).data NT
      NR (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key true))
      (stage) (pair q []) hactive (correlationTuple q v hv)=
    IntegralFramedPhysicalSquare.point (NB).parameters
      (NB).plan (NB).data
      (NB).nodes (NB).factor
      (NB).seed (NB).bounds
      (key true) (positive true) q v hv
      ⟨0,positive true q⟩ :=by
  unfold IntegralMixedFramedCriticalGuard.actualPoint
  have HI : (⟨IntegralMixedFramedCriticalGuardBits.age (NB).parameters
      (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key true)) (stage) (pair q []),
      IntegralMixedFramedCriticalGuardBits.age_lt (NB).parameters
        (NB).plan (NB).data NT
        (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key true)) (stage) (pair q []) hactive⟩ :
      Fin ((IntegralMixedFramedHistoryFamilyBits.family (NB).parameters
        (NB).plan (NB).data).birth
          (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key true) (pair q []))))=
        ⟨0,by simpa only [IntegralFramedPhysicalCriticalGuardTest.keyDatum,pairFst_pair] using
          positive true q⟩ :=
    Fin.ext (correlation_age q)
  rw [HI]
  unfold IntegralFramedPhysicalSquare.point IntegralMixedFramedCriticalGuard.fullEquiv
    correlationTuple IntegralFramedPhysicalSquare.joint
  exact indexedPoint_key_cast
    (IntegralMixedFramedHistoryFamilyBits.family (NB).parameters
      (NB).plan (NB).data)
    (fun k=>IntegralMixedFramedPhysicalIndex.arity (IntegralMixedFramedHistoryFamilyBits.commands
      (NB).parameters (NB).plan k))
    (fun k=>IntegralMixedFramedPhysicalIndex.enumerate (IntegralMixedFramedHistoryFamilyBits.commands
      (NB).parameters (NB).plan k))
    _ _ (congrArg (key true) (pairFst_pair q [])) _
    (IntegralMixedFramedCriticalGuardBits.count_actual (NB).parameters
      (NB).plan (NB).data NT
      NR (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key true)) (pair q []))
    (guard_count q []) _ _ _ rfl

theorem correlation_iff_newest (q v : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input true) q v)
    (hactive : IntegralMixedFramedCriticalGuardBits.Active (NB).parameters
      NT (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key true))
      (stage) (pair q [])) :
    correlation (pair q v)=InfinitesimalSign.encode 0 ↔
    IntegralFramedPhysicalSquare.point (NB).parameters
      (NB).plan (NB).data
      (NB).nodes (NB).factor
      (NB).seed (NB).bounds
      (key true) (positive true) q v hv
      ⟨0,positive true q⟩=
    correlationTuple q v hv
      ⟨IntegralMixedFramedCriticalGuardBits.physical (NB).parameters
        NT (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key true))
        (stage) (pair q []),
        IntegralMixedFramedCriticalGuardBits.physical_lt (NB).parameters
          (NB).plan (NB).data NT
          NR (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key true))
          (stage) (pair q []) hactive⟩^
      IntegralMixedFramedCriticalGuardBits.physicalPower (NB).parameters
        (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key true)) (stage) (pair q []) :=by
  have HP:=guard_packet (input true)
    (NB).parameters (NB).plan (NB).data
    NT (NB).nodes (NB).factor
    (NB).seed (NB).bounds (key true) (stage)
    (guard_count) q v [] hv
  unfold correlation
  simp only [Function.comp_apply,probe]
  rw [HP,SquareSampleTestSign.encode_eq_iff,sign_eq_zero_iff]
  have HE:=IntegralMixedFramedCriticalGuard.zero_iff_actualPoint _ _ _ _ NR
    _ _ _ hactive (correlationTuple q v hv)
  rw [correlation_actualPoint q v hv hactive] at HE
  unfold correlationTuple at HE
  exact HE

end LeanCanny.Encoding.FormulaSignSlotRadialProviderCriticalInterval
