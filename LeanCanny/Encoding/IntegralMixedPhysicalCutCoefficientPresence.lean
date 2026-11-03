/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalCutCoefficientIntervalComplete
public import LeanCanny.Algebra.IntegralMixedSelectedBadMembership
/-! # Failure of a reserved native interval test is an actual selected-factor root

The older interpretation is obtained from the SAME valid full word and its
coefficient guards.  Ordered endpoints make the negative interval answer
exactly root presence, including constant and rootless factors.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalCutCoefficientPresence
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (family)
open IntegralMixedPhysicalMarkedPlan (bank)
open IntegralMixedPhysicalCutOpenInterval (parent Bounds birthWord)
open IntegralMixedPhysicalCutOrderedInterval (endpoint left_bound right_bound)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] bank family IntegralFramedPhysicalSquare.input IntegralFramedPhysicalSquare.point
 IntegralMixedPhysicalCutOpenInterval.parent IntegralMixedVirtualTaskBits.saved
 IntegralMixedFramedFullCutIntervalSelected.factor IntegralFramedPhysicalSquare.scalarTuple
variable {n : List Bool→ℕ} {t : List Bool→Term}
 (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R : List Bool→ℕ} (hR : BinaryFn R) (outer : Bool)
local notation "B"=>bank hn ht ha hR outer
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "D"=>IntegralFramedBankQuery.Bank.plan B
local notation "H"=>IntegralFramedBankQuery.Bank.data B
local notation "G"=>family P D H
variable (q w : List Bool)
 (hv : SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha hR outer) q w)
 (hb : Bounds hn ht ha hR outer (pair q w))
local notation "old"=>IntegralMixedVirtualTaskBits.saved P (parent hn ht ha hR outer q)
local notation "x"=>IntegralMixedCutSource.Family.state G old
local notation "hm"=>IntegralMixedCutSource.Family.birth_bound G old
local notation "r"=>IntegralMixedCutSource.Family.rule G old
local notation "k"=>IntegralMixedCutSource.Family.kind G old

abbrev FullTail (φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) : Prop:=
 ∀i,φ ((x).sampler.scalarPrefix.basis.generator i)=
   IntegralFramedPhysicalSquare.scalarTuple P D H (B).nodes (B).factor (B).seed (B).bounds
     (B).key (B).positive q w hv
     (UniformIntegralPowerSchedule.embed (IntegralMixedPhysicalCutLocalInterpretation.fits hn ht ha hR outer q w hb) i)^
     UniformIntegralPowerSchedule.weights ((P).cap (pairFst old)+1) (2^(G).width old) ((G).birth old) i

theorem interpreted_present_iff
    (hg : IntegralMixedPhysicalCutCoefficientOnly.Guards hn ht ha hR outer (pair q w))
    (hab : endpoint hn ht ha hR outer false q w hv (left_bound hn ht ha hR outer q w hb)<
      endpoint hn ht ha hR outer true q w hv (right_bound hn ht ha hR outer q w hb)) :
    ∃φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      FullTail hn ht ha hR outer q w hv hb φ ∧
      IntegralMixedRelativeCuts.Valid x hm r φ k ∧
      ((IntegralMixedRelativeCuts.factor x hm r k).map φ.toRingHom).natDegree=(G).degree old ∧
      (pair q w∉IntegralMixedPhysicalCutCoefficientInterval.language hn ht ha hR outer ↔
        ∃u∈Set.Ioo (endpoint hn ht ha hR outer false q w hv (left_bound hn ht ha hR outer q w hb))
          (endpoint hn ht ha hR outer true q w hv (right_bound hn ht ha hR outer q w hb)),
          (IntegralMixedRelativeCuts.factor x hm r k).eval₂ φ.toRingHom u=0) :=by
 obtain ⟨φ,hφ,HV,_,HD,HI⟩:=IntegralMixedPhysicalCutCoefficientInterval.interpreted_empty_iff
   hn ht ha hR outer q w hv hb hg
 have HD' : ((IntegralMixedRelativeCuts.factor x hm r k).map φ.toRingHom).natDegree=(G).degree old:=by
   simpa only [IntegralMixedFramedFullCutIntervalSelected.factor,IntegralMixedFramedFullCutHead.saved] using
     HD.trans (IntegralMixedPhysicalCutOpenInterval.degree_eq hn ht ha hR outer q)
 refine ⟨φ,hφ,HV,HD',?_⟩
 have HI' : pair q w∈IntegralMixedPhysicalCutCoefficientInterval.language hn ht ha hR outer ↔
     endpoint hn ht ha hR outer false q w hv (left_bound hn ht ha hR outer q w hb)<
       endpoint hn ht ha hR outer true q w hv (right_bound hn ht ha hR outer q w hb) ∧
     ∀u,(IntegralMixedRelativeCuts.factor x hm r k).eval₂ φ.toRingHom u=0→
       u∉Set.Ioo (endpoint hn ht ha hR outer false q w hv (left_bound hn ht ha hR outer q w hb))
         (endpoint hn ht ha hR outer true q w hv (right_bound hn ht ha hR outer q w hb)):=by
   simpa only [IntegralMixedFramedFullCutIntervalSelected.factor,IntegralMixedFramedFullCutHead.saved,Polynomial.eval_map] using HI
 rw [HI']
 simp only [hab,true_and,not_forall,not_not,exists_prop]
 exact exists_congr (fun u=>and_comm)

end LeanCanny.Encoding.IntegralMixedPhysicalCutCoefficientPresence
