/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalCutRoot
public import LeanCanny.Encoding.IntegralMixedPhysicalTraceCutGuardComplete
/-! # The actual untruncated factor receipt is complete for a native cut guard -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalCutCoefficientSemantics
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedPhysicalMarkedPlan (bank)
open IntegralMixedPhysicalMarkedTest (input sampleContext)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term}
  (hn :UnaryFn n) (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R :List Bool→ℕ} (hR :BinaryFn R) (outer :Bool)
  (ctx w u :List Bool)
  (hv :SquareSampleCompleteVertices.Valid (input hn ht ha hR outer) (sampleContext ctx) w)
local notation "B"=>bank hn ht ha hR outer
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "D"=>IntegralFramedBankQuery.Bank.plan B
local notation "H"=>IntegralFramedBankQuery.Bank.data B
local notation "p"=>IntegralFramedPhysicalTraceCutSource.parent B (sampleContext ctx) u
local notation "G"=>IntegralMixedFramedHistoryFamilyBits.family P D H
local notation "old"=>IntegralMixedVirtualTaskBits.saved P p
local notation "x"=>IntegralMixedCutSource.Family.state G old
local notation "bound"=>IntegralMixedCutSource.Family.birth_bound G old
local notation "rule"=>IntegralMixedCutSource.Family.rule G old
local notation "kind"=>IntegralMixedCutSource.Family.kind G old
local notation "degree"=>IntegralMixedCutSource.Family.degree G old
local notation "offset"=>IntegralFramedTerminalCutTest.count P D H
  (IntegralFramedPhysicalTraceCutSource.taskKey B) p-IntegralMixedCutSource.Family.birth G old
attribute [local irreducible] bank IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedPhysicalTraceCutGuards.head IntegralMixedPhysicalTraceCutGuards.sign

theorem bankQuotient_zero_of_head
    (hfit :birth P p<(G).birth ((B).key (sampleContext ctx))) (hb :birth P p=u.length)
    (hh :IntegralMixedPhysicalTraceCutGuards.head hn ht ha hR outer (stage ctx w u)=InfinitesimalSign.encode 0) :
    bankQuotient hn ht ha hR outer ctx w u hv=0:=by
  have HT :(G).birth ((B).key (sampleContext ctx))=
      IntegralMixedPhysicalReplayNew.count hn ht ha hR outer (sampleContext ctx):=rfl
  have HR:=(head_zero_iff hn ht ha hR outer ctx w u hv (by rw [←HT,←hb];exact hfit)).mp hh
  have HI :(G).birth ((B).key (sampleContext ctx))-birth P p-1<
      (G).birth ((B).key (sampleContext ctx)):=by omega
  unfold bankQuotient IntegralMixedFramedBankObservation.Data.point IntegralMixedFramedBankObservation.ofState
  rw [dite_eq_left HI]
  have HRaw :IntegralFramedPhysicalSuffixTest.rawTuple B (sampleContext ctx) w hv
      ((G).birth ((B).key (sampleContext ctx))-birth P p-1)=0:=by
    simpa only [HT,hb] using HR
  rw [HRaw,zero_pow (Nat.ne_of_gt (UniformIntegralPowerSchedule.weights_pos _ _ _ _)),zero_div]

theorem guards_of_factor_receipt
    (hfit :birth P p<(G).birth ((B).key (sampleContext ctx))) (hb :birth P p=u.length)
    (hactive :IntegralMixedFramedFullCutProbeBits.Active P p)
    (φ :(x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ :∀i,φ ((x).sampler.scalarPrefix.basis.generator i)=
      IntegralFramedPhysicalSuffixTest.rawTuple B (sampleContext ctx) w hv (i.val+offset)^
        UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon P p)
          (2^(G).width old) ((G).birth old) i)
    (hc :IntegralMixedRelativeCuts.CoefficientGuards x bound rule φ kind degree)
    (hr :(IntegralMixedRelativeCuts.factor x bound rule kind).eval₂ φ.toRingHom
      (bankQuotient hn ht ha hR outer ctx w u hv)=0) :
    IntegralMixedPhysicalTraceCutGuards.Guards hn ht ha hR outer (stage ctx w u):=by
  have HM :(G).birth old=birth P p:=(IntegralMixedFramedHistoryFamilyBits.geometry P D H).birth p
  apply guards_of_coefficient_receipt hn ht ha hR outer ctx w u hv (HM.trans_le hfit.le) hactive φ hφ hc
  intro hh
  have HZ:=bankQuotient_zero_of_head hn ht ha hR outer ctx w u hv hfit hb hh
  rw [HZ,Polynomial.eval₂_at_zero] at hr
  exact hr

/-- Soundness and completeness use the SAME old algebra and SAME full tuple.
The native head condition is derived from the actual factor root, even at zero. -/
theorem guards_iff_factor_receipt
    (hfit :birth P p<(G).birth ((B).key (sampleContext ctx))) (hb :birth P p=u.length)
    (hactive :IntegralMixedFramedFullCutProbeBits.Active P p)
    (hcut :IntegralFramedCreatingCut.ParentCut P D p) :
    IntegralMixedPhysicalTraceCutGuards.Guards hn ht ha hR outer (stage ctx w u)↔
      ∃φ :(x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
        (∀i,φ ((x).sampler.scalarPrefix.basis.generator i)=
          IntegralFramedPhysicalSuffixTest.rawTuple B (sampleContext ctx) w hv (i.val+offset)^
            UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon P p)
              (2^(G).width old) ((G).birth old) i) ∧
        IntegralMixedRelativeCuts.CoefficientGuards x bound rule φ kind degree ∧
        (IntegralMixedRelativeCuts.factor x bound rule kind).eval₂ φ.toRingHom
          (bankQuotient hn ht ha hR outer ctx w u hv)=0:=by
  constructor
  · intro hg
    obtain ⟨φ,hφ,hvalid,hdegree,hroot⟩:=exists_factor_root hn ht ha hR outer ctx w u hv hactive hcut hfit hb hg
    exact ⟨φ,hφ,(IntegralMixedRelativeCuts.coefficientGuards_iff_valid_degree x bound rule φ kind degree).mpr
      ⟨hvalid,hdegree⟩,hroot⟩
  · rintro ⟨φ,hφ,hc,hr⟩
    exact guards_of_factor_receipt hn ht ha hR outer ctx w u hv hfit hb hactive φ hφ hc hr

end LeanCanny.Encoding.IntegralMixedPhysicalCutCoefficientSemantics
