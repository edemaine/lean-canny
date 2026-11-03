/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalPointCompanionSemantics
public import LeanCanny.Encoding.IntegralFramedPhysicalCriticalAnchor
/-! # The native physical block is the geometric creating point of the same word -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalPointCompanionScan
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedPhysicalMarkedPlan (bank tables represents)
open IntegralMixedFramedCriticalGuardBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R :List Bool→ℕ} (hR :BinaryFn R) (outer :Bool)
local notation "B"=>bank hn ht ha hR outer
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "T"=>tables hn ht ha hR outer
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha hR outer
attribute [local irreducible] bank tables

theorem full_positive (c :List Bool) :
    0<(IntegralMixedFramedHistoryFamilyBits.family P (B).plan (B).data).birth ((B).key c):=
  (B).positive c

attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedFramedPhysicalIndex.prefixArity UniformIntegralPowerSchedule.physical

theorem active_direct (c :List Bool) (b :ℕ) (hb :Active hn ht ha hR outer c b) :
    IntegralMixedFramedCriticalGuardBits.Active P T (B).key (fun _=>b) c :=by
  simpa only [IntegralMixedPhysicalPointCompanionScan.Active,IntegralMixedFramedCriticalGuardBits.Active,
    IntegralMixedFramedCriticalGuardBits.header,
    IntegralFramedPhysicalCriticalGuardTest.keyDatum,IntegralFramedPhysicalCriticalGuardScan.stage,
    pairFst_pair,pairSnd_pair,List.length_replicate] using hb

theorem geometricPoint_readback (c w :List Bool) (hv :SquareSampleCompleteVertices.Valid S c w)
    (b :ℕ) (hb :Active hn ht ha hR outer c b) :
    geometricPoint hn ht ha hR outer c w hv b=
      IntegralMixedFramedCriticalAnchor.geometricPoint P (B).plan (B).key (fun _=>b) c
        (IntegralFramedPhysicalCriticalReadback.tuple P (B).plan (B).data (B).nodes (B).factor (B).seed
          (B).bounds (B).key (full_positive hn ht ha hR outer) c w hv) :=by
  funext i
  have HC:=IntegralMixedPhysicalGuardScan.count_eq hn ht ha hR outer c []
  have HC' :count P T (B).key c=(S).count c:=by
    simpa only [IntegralMixedFramedCriticalGuardBits.count,IntegralMixedFramedCriticalGuardBits.packet,
      IntegralFramedPhysicalCriticalGuardTest.keyDatum,Function.comp_apply,pairFst_pair] using HC
  have HL:=IntegralMixedFramedPointEqualityBits.column_lt P T (B).key (fun _=>i.val) (fun _=>b) c
    (active_direct hn ht ha hR outer c b hb) i.isLt
  have HI :IntegralMixedFramedPhysicalIndex.prefixArity P T (pair ((B).key c) (List.replicate b true))+i.val<(S).count c:=
    HL.trans_eq HC'
  unfold geometricPoint IntegralMixedPhysicalPointEquality.block
  rw [dite_eq_left HI]
  unfold IntegralMixedFramedCriticalAnchor.geometricPoint IntegralFramedPhysicalCriticalReadback.tuple
    IntegralMixedFramedBankObservation.extend
  rw [←IntegralMixedFramedPhysicalIndex.prefixArity_packet P (B).plan (B).data T
    (represents hn ht ha hR outer)]
  have HI' :IntegralMixedFramedPhysicalIndex.prefixArity P T (pair ((B).key c) (List.replicate b true))+i.val<
      IntegralFramedPhysicalSquare.count P (B).plan ((B).key c):=HI
  rw [dite_eq_left HI']
  rfl

theorem exists_critical (c w :List Bool) (hv :SquareSampleCompleteVertices.Valid S c w)
    (b :ℕ) (hb :Active hn ht ha hR outer c b)
    (r :IntegralMixedHistory.CriticalRule ((P).ambient (pairFst ((B).key c))))
    (hc :(IntegralMixedFramedRootPullback.instructionAt P (B).plan (pairFst ((B).key c)) b).command=.critical r) :
    ∃hcs :IntegralMixedFramedHistoryFamilyBits.commands P (B).plan ((B).key c)=
      (IntegralMixedFramedHistoryFamilyBits.commands P (B).plan ((B).key c)).take
        (age P (B).key (fun _=>b) c)++
      ⟨(IntegralMixedFramedRootPullback.instructionAt P (B).plan (pairFst ((B).key c)) b).source,
        (IntegralMixedFramedRootPullback.instructionAt P (B).plan (pairFst ((B).key c)) b).source_cap,.critical r⟩::
        IntegralMixedFramedHistoryScript.paddedPast
          (IntegralMixedFramedHistoryFamilyBits.defaultInstruction P (B).plan (pairFst ((B).key c)))
          ((B).plan.rules (pairFst ((B).key c))) b,
    let x:=IntegralFramedPhysicalCriticalReadback.oldState P (B).plan (B).data (B).key c _ _ r _ _ hcs
    ∃φ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀i,φ (x.sampler.scalarPrefix.basis.generator i)=
        IntegralFramedPhysicalCriticalReadback.tuple P (B).plan (B).data (B).nodes (B).factor (B).seed
          (B).bounds (B).key (full_positive hn ht ha hR outer) c w hv
          (IntegralMixedFramedPhysicalIndex.enumerate _ (x.sampler.scalar i)).val^
          UniformIntegralPowerSchedule.weights ((P).cap (pairFst ((B).key c))+1)
            (2^(P).width (pairFst ((B).key c))) _ i) ∧
      IntegralMixedCriticalReadback.CriticalPoint x
        (IntegralFramedPhysicalCriticalReadback.older_room P (B).plan (B).data (B).key c _ _ r _ _ hcs) r φ
        (geometricPoint hn ht ha hR outer c w hv b) :=by
  obtain ⟨s,hs,hcs,φ,hφ,HP⟩:=IntegralFramedPhysicalCriticalReadback.exists_active_point P (B).plan (B).data
    (B).nodes (B).factor (B).seed (B).bounds T (represents hn ht ha hR outer) (B).key
    (full_positive hn ht ha hR outer) (fun _=>b) c w hv (active_direct hn ht ha hR outer c b hb)
  have Hsr :s=r:=IntegralMixedFullHistoryScript.Command.critical.inj (hs.symm.trans hc)
  subst s
  exact ⟨hcs,φ,hφ,(geometricPoint_readback hn ht ha hR outer c w hv b hb).symm ▸ HP⟩

end LeanCanny.Encoding.IntegralMixedPhysicalPointCompanionScan
