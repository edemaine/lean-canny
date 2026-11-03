/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalCriticalInterval
public import LeanCanny.Algebra.IntegralMixedFramedCriticalGuardOrigin
/-! # The appended critical guard compares the actual newest bank quotient

The physical coordinate is read from the same complete child tuple with its
creating power. No interpreting hom or simplicity of roots is assumed.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalCriticalInterval
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedPhysicalMarkedPlan (bank tables represents)
open IntegralMixedPhysicalCriticalPrefixes (birth key input positive)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R) (outer : Bool)
attribute [local irreducible] bank tables

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
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer true) q v) :
    Fin (IntegralMixedFramedCriticalGuardBits.count (bank hn ht ha hR outer).parameters
      (tables hn ht ha hR outer) (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key n outer true)) (pair q []))→ℝ :=
  fun i=>(SquareSampleCompleteVertices.candidate (input hn ht ha hR outer true) q v hv).val
    (Fin.cast (guard_count hn ht ha hR outer q []) i)

theorem correlation_age (q : List Bool) :
    IntegralMixedFramedCriticalGuardBits.age (bank hn ht ha hR outer).parameters
      (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key n outer true)) (stage n outer) (pair q [])=0 :=by
  have HB:=IntegralMixedPhysicalCriticalPrefixes.key_birth hn ht ha hR outer true q
  rw [IntegralMixedFramedHistoryFamilyBits.family_birth] at HB
  simp only [IntegralMixedFramedCriticalGuardBits.age,IntegralFramedPhysicalCriticalGuardTest.keyDatum,
    stage,pairFst_pair,HB,IntegralMixedPhysicalCriticalPrefixes.consecutive]
  omega

theorem correlation_actualPoint (q v : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer true) q v)
    (hactive : IntegralMixedFramedCriticalGuardBits.Active (bank hn ht ha hR outer).parameters
      (tables hn ht ha hR outer) (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key n outer true))
      (stage n outer) (pair q [])) :
    IntegralMixedFramedCriticalGuard.actualPoint (bank hn ht ha hR outer).parameters
      (bank hn ht ha hR outer).plan (bank hn ht ha hR outer).data (tables hn ht ha hR outer)
      (represents hn ht ha hR outer) (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key n outer true))
      (stage n outer) (pair q []) hactive (correlationTuple hn ht ha hR outer q v hv)=
    IntegralFramedPhysicalSquare.point (bank hn ht ha hR outer).parameters
      (bank hn ht ha hR outer).plan (bank hn ht ha hR outer).data
      (bank hn ht ha hR outer).nodes (bank hn ht ha hR outer).factor
      (bank hn ht ha hR outer).seed (bank hn ht ha hR outer).bounds
      (key n outer true) (positive hn ht ha hR outer true) q v hv
      ⟨0,positive hn ht ha hR outer true q⟩ :=by
  unfold IntegralMixedFramedCriticalGuard.actualPoint
  have HI : (⟨IntegralMixedFramedCriticalGuardBits.age (bank hn ht ha hR outer).parameters
      (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key n outer true)) (stage n outer) (pair q []),
      IntegralMixedFramedCriticalGuardBits.age_lt (bank hn ht ha hR outer).parameters
        (bank hn ht ha hR outer).plan (bank hn ht ha hR outer).data (tables hn ht ha hR outer)
        (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key n outer true)) (stage n outer) (pair q []) hactive⟩ :
      Fin ((IntegralMixedFramedHistoryFamilyBits.family (bank hn ht ha hR outer).parameters
        (bank hn ht ha hR outer).plan (bank hn ht ha hR outer).data).birth
          (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key n outer true) (pair q []))))=
        ⟨0,by simpa only [IntegralFramedPhysicalCriticalGuardTest.keyDatum,pairFst_pair] using
          positive hn ht ha hR outer true q⟩ :=
    Fin.ext (correlation_age hn ht ha hR outer q)
  rw [HI]
  unfold IntegralFramedPhysicalSquare.point IntegralMixedFramedCriticalGuard.fullEquiv
    correlationTuple IntegralFramedPhysicalSquare.joint
  exact indexedPoint_key_cast
    (IntegralMixedFramedHistoryFamilyBits.family (bank hn ht ha hR outer).parameters
      (bank hn ht ha hR outer).plan (bank hn ht ha hR outer).data)
    (fun k=>IntegralMixedFramedPhysicalIndex.arity (IntegralMixedFramedHistoryFamilyBits.commands
      (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan k))
    (fun k=>IntegralMixedFramedPhysicalIndex.enumerate (IntegralMixedFramedHistoryFamilyBits.commands
      (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan k))
    _ _ (congrArg (key n outer true) (pairFst_pair q [])) _
    (IntegralMixedFramedCriticalGuardBits.count_actual (bank hn ht ha hR outer).parameters
      (bank hn ht ha hR outer).plan (bank hn ht ha hR outer).data (tables hn ht ha hR outer)
      (represents hn ht ha hR outer) (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key n outer true)) (pair q []))
    (guard_count hn ht ha hR outer q []) _ _ _ rfl

theorem correlation_iff_newest (q v : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer true) q v)
    (hactive : IntegralMixedFramedCriticalGuardBits.Active (bank hn ht ha hR outer).parameters
      (tables hn ht ha hR outer) (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key n outer true))
      (stage n outer) (pair q [])) :
    correlation hn ht ha hR outer (pair q v)=InfinitesimalSign.encode 0 ↔
    IntegralFramedPhysicalSquare.point (bank hn ht ha hR outer).parameters
      (bank hn ht ha hR outer).plan (bank hn ht ha hR outer).data
      (bank hn ht ha hR outer).nodes (bank hn ht ha hR outer).factor
      (bank hn ht ha hR outer).seed (bank hn ht ha hR outer).bounds
      (key n outer true) (positive hn ht ha hR outer true) q v hv
      ⟨0,positive hn ht ha hR outer true q⟩=
    correlationTuple hn ht ha hR outer q v hv
      ⟨IntegralMixedFramedCriticalGuardBits.physical (bank hn ht ha hR outer).parameters
        (tables hn ht ha hR outer) (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key n outer true))
        (stage n outer) (pair q []),
        IntegralMixedFramedCriticalGuardBits.physical_lt (bank hn ht ha hR outer).parameters
          (bank hn ht ha hR outer).plan (bank hn ht ha hR outer).data (tables hn ht ha hR outer)
          (represents hn ht ha hR outer) (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key n outer true))
          (stage n outer) (pair q []) hactive⟩^
      IntegralMixedFramedCriticalGuardBits.physicalPower (bank hn ht ha hR outer).parameters
        (IntegralFramedPhysicalCriticalGuardTest.keyDatum (key n outer true)) (stage n outer) (pair q []) :=by
  have HP:=guard_packet (input hn ht ha hR outer true)
    (bank hn ht ha hR outer).parameters (bank hn ht ha hR outer).plan (bank hn ht ha hR outer).data
    (tables hn ht ha hR outer) (bank hn ht ha hR outer).nodes (bank hn ht ha hR outer).factor
    (bank hn ht ha hR outer).seed (bank hn ht ha hR outer).bounds (key n outer true) (stage n outer)
    (guard_count hn ht ha hR outer) q v [] hv
  unfold correlation
  simp only [Function.comp_apply,probe]
  rw [HP,SquareSampleTestSign.encode_eq_iff,sign_eq_zero_iff]
  have HE:=IntegralMixedFramedCriticalGuard.zero_iff_actualPoint _ _ _ _ (represents hn ht ha hR outer)
    _ _ _ hactive (correlationTuple hn ht ha hR outer q v hv)
  rw [correlation_actualPoint hn ht ha hR outer q v hv hactive] at HE
  unfold correlationTuple at HE
  exact HE

end LeanCanny.Encoding.IntegralMixedPhysicalCriticalInterval
