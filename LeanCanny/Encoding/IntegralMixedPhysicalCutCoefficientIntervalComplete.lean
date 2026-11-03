/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalCutCoefficientComplete
public import LeanCanny.Encoding.IntegralMixedPhysicalCutCoefficientInterval
/-! # Reserved interval acceptance is complete at an honest old interpretation

The native coefficient guards are derived from factor validity and the actual
stored specialized degree. No true factor root at the fresh padded head is
required. The old hom is fixed by the SAME full sampler word throughout.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalCutCoefficientComplete
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (family)
open IntegralMixedPhysicalMarkedPlan (bank tables)
open IntegralMixedPhysicalCutOpenInterval (parent Bounds birthWord)
open IntegralMixedPhysicalCutOrderedInterval (endpoint left_bound right_bound)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] bank tables IntegralMixedFramedHistoryFamilyBits.family
variable {n : List Bool→ℕ} {t : List Bool→Term}
 (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R : List Bool→ℕ} (hR : BinaryFn R) (outer : Bool)
local notation "B" => bank hn ht ha hR outer
local notation "P" => IntegralFramedBankQuery.Bank.parameters B
local notation "D" => IntegralFramedBankQuery.Bank.plan B
local notation "H" => IntegralFramedBankQuery.Bank.data B
local notation "G" => family P D H
variable (q w : List Bool)
 (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR outer) q w)
local notation "p" => parent hn ht ha hR outer q
local notation "old" => IntegralMixedVirtualTaskBits.saved P p
local notation "x" => IntegralMixedCutSource.Family.state G old
local notation "hm" => IntegralMixedCutSource.Family.birth_bound G old
local notation "r" => IntegralMixedCutSource.Family.rule G old
local notation "kind" => IntegralMixedCutSource.Family.kind G old
local notation "offset" => IntegralFramedTerminalCutTest.count P D H
 (IntegralFramedPhysicalTraceCutSource.taskKey B) p-IntegralMixedCutSource.Family.birth G old

theorem full_tail (hb : Bounds hn ht ha hR outer (pair q w))
    (φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (hφ : Tail hn ht ha hR outer q w hv φ) :
    ∀i,φ ((x).sampler.scalarPrefix.basis.generator i)=
      IntegralFramedPhysicalSquare.scalarTuple P D H (B).nodes (B).factor (B).seed (B).bounds
        (B).key (B).positive q w hv
        (UniformIntegralPowerSchedule.embed (IntegralMixedPhysicalCutLocalInterpretation.fits hn ht ha hR outer q w hb) i)^
        UniformIntegralPowerSchedule.weights ((P).cap (pairFst old)+1) (2^(G).width old) ((G).birth old) i :=by
  intro i
  have HC : IntegralFramedTerminalCutTest.count P D H
      (IntegralFramedPhysicalTraceCutSource.taskKey B) p=(G).birth ((B).key q) :=
    IntegralFramedPhysicalTraceCutSource.count_parent B
      (IntegralMixedPhysicalTraceCutTest.key_context hn ht ha hR outer) q (birthWord q)
  have HX : IntegralFramedPhysicalSuffixTest.rawTuple B q w hv (i.val+offset)=
      IntegralFramedPhysicalSquare.scalarTuple P D H (B).nodes (B).factor (B).seed (B).bounds
        (B).key (B).positive q w hv
        (UniformIntegralPowerSchedule.embed (IntegralMixedPhysicalCutLocalInterpretation.fits hn ht ha hR outer q w hb) i) :=by
    refine (congrArg (IntegralFramedPhysicalSuffixTest.rawTuple B q w hv)
      (congrArg (fun v=>i.val+(v-(G).birth old)) HC)).trans ?_
    have HI : i.val+((G).birth ((B).key q)-(G).birth old)<(G).birth ((B).key q) :=by
      have HH:=i.isLt
      have HF:=IntegralMixedPhysicalCutLocalInterpretation.fits hn ht ha hR outer q w hb
      omega
    unfold IntegralFramedPhysicalSuffixTest.rawTuple IntegralMixedFramedBankObservation.extend
    rw [dite_eq_left HI]
    apply congrArg _
    apply Fin.ext
    exact Nat.add_comm _ _
  have HW : (G).cap old=IntegralMixedFramedChoiceProbeSourceBits.horizon P p :=
    IntegralFramedPhysicalTraceCutSource.parent_horizon B q (birthWord q)
  have HCap : (G).cap old=(P).cap (pairFst old)+1 :=by
    unfold IntegralMixedFramedHistoryFamilyBits.family
    rfl
  exact (hφ i).trans (congrArg₂ (fun (a : ℝ) (e : ℕ)=>a^e) HX
    (congrArg (fun S=>UniformIntegralPowerSchedule.weights S (2^(G).width old) ((G).birth old) i)
      (HW.symm.trans HCap)))

theorem empty_iff_at (hb : Bounds hn ht ha hR outer (pair q w))
    (φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (hφ : Tail hn ht ha hR outer q w hv φ)
    (hvalid : IntegralMixedRelativeCuts.Valid x hm r φ kind)
    (hdegree : ((IntegralMixedRelativeCuts.factor x hm r kind).map φ.toRingHom).natDegree=(G).degree old) :
    pair q w∈IntegralMixedPhysicalCutCoefficientInterval.language hn ht ha hR outer ↔
      endpoint hn ht ha hR outer false q w hv (left_bound hn ht ha hR outer q w hb)<
        endpoint hn ht ha hR outer true q w hv (right_bound hn ht ha hR outer q w hb) ∧
      ∀a,(IntegralMixedFramedFullCutIntervalSelected.factor P D H (parent hn ht ha hR outer) q φ).eval a=0→
        a∉Set.Ioo (endpoint hn ht ha hR outer false q w hv (left_bound hn ht ha hR outer q w hb))
          (endpoint hn ht ha hR outer true q w hv (right_bound hn ht ha hR outer q w hb)) :=by
  have hg:=(guards_iff_valid_degree hn ht ha hR outer q w hv hb φ hφ).mpr ⟨hvalid,hdegree⟩
  obtain ⟨ψ,hψ,_,_,_,HI⟩:=IntegralMixedPhysicalCutCoefficientInterval.interpreted_empty_iff hn ht ha hR outer q w hv hb hg
  have HF:=full_tail hn ht ha hR outer q w hv hb φ hφ
  have HX : ψ=φ :=(x).sampler.scalarPrefix.basis.algHom_ext ψ φ (fun i=>(hψ i).trans (HF i).symm)
  simpa only [HX] using HI

end LeanCanny.Encoding.IntegralMixedPhysicalCutCoefficientComplete
