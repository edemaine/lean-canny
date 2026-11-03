/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalTraceCutParent
public import LeanCanny.Encoding.IntegralMixedPhysicalTraceCutGuards

/-! # Original full cut queries read one actual chronological parent -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalCutCoefficientSemantics
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedPhysicalMarkedPlan (bank tables represents)
open IntegralMixedPhysicalMarkedTest (input sampleContext)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R) (outer : Bool)

theorem native_value : IntegralMixedPhysicalTraceCutTest.value hn ht ha hR outer=
    IntegralFramedPhysicalTraceCutSource.value (bank hn ht ha hR outer)
      (IntegralMixedPhysicalTraceCutTest.key_context hn ht ha hR outer)
      (IntegralMixedPhysicalTraceCutTest.factor_positive hn ht ha hR outer)
      (IntegralMixedPhysicalTraceCutTest.fallback hn ht ha hR outer)
      (tables hn ht ha hR outer) (represents hn ht ha hR outer) :=rfl

def stage (ctx w u : List Bool) :=pair (pair ctx w) u

theorem sign_packet (ctx w u : List Bool) (e k : ℕ) :
    IntegralMixedPhysicalTraceCutGuards.sign hn ht ha hR outer
      (FiniteCoefficientSignScan.query (stage ctx w u) e k)=
    IntegralFramedPhysicalTraceCutSource.value (bank hn ht ha hR outer)
      (IntegralMixedPhysicalTraceCutTest.key_context hn ht ha hR outer)
      (IntegralMixedPhysicalTraceCutTest.factor_positive hn ht ha hR outer)
      (IntegralMixedPhysicalTraceCutTest.fallback hn ht ha hR outer)
      (tables hn ht ha hR outer) (represents hn ht ha hR outer)
      (pair (pair (sampleContext ctx) w) (IntegralFramedPhysicalTraceCutSource.datum u e k)) :=by
  simpa only [IntegralMixedPhysicalTraceCutGuards.sign,Function.comp_apply,IntegralMixedPhysicalTraceCutGuards.query,
    FiniteCoefficientSignScan.query,stage,IntegralFramedTraceCutGuards.root,IntegralFramedTraceCutGuards.word,
    IntegralFramedPhysicalTraceCutSource.datum,pairFst_pair,pairSnd_pair] using
      congrFun (native_value hn ht ha hR outer)
        (pair (pair (sampleContext ctx) w) (IntegralFramedPhysicalTraceCutSource.datum u e k))

theorem parent_packet (ctx w u : List Bool) :
    IntegralFramedTraceCutGuards.parent (bank hn ht ha hR outer).parameters (stage ctx w u)=
      IntegralFramedPhysicalTraceCutSource.parent (bank hn ht ha hR outer) (sampleContext ctx) u :=by
  simp only [IntegralFramedTraceCutGuards.parent,Function.comp_apply,IntegralFramedTraceCutGuards.descriptor,
    IntegralFramedTraceCutGuards.root,stage,IntegralFramedPhysicalTraceCutSource.parent,sampleContext,
    pairFst_pair,pairSnd_pair]

attribute [local irreducible] bank tables IntegralMixedPhysicalTraceCutGuards.sign

variable (ctx w u : List Bool)
  (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer) (sampleContext ctx) w)
local notation "B" => bank hn ht ha hR outer
local notation "P" => IntegralFramedBankQuery.Bank.parameters B
local notation "D" => IntegralFramedBankQuery.Bank.plan B
local notation "H" => IntegralFramedBankQuery.Bank.data B
local notation "p" => IntegralFramedPhysicalTraceCutSource.parent B (sampleContext ctx) u
local notation "G" => IntegralMixedFramedHistoryFamilyBits.family P D H
local notation "old" => IntegralMixedVirtualTaskBits.saved P p
local notation "x" => IntegralMixedCutSource.Family.state G old
local notation "offset" => IntegralFramedTerminalCutTest.count P D H
  (IntegralFramedPhysicalTraceCutSource.taskKey B) p-IntegralMixedCutSource.Family.birth G old

theorem exists_coefficient_evaluation
    (hfit : (G).birth old≤(G).birth ((B).key (sampleContext ctx)))
    (hactive : IntegralMixedFramedFullCutProbeBits.Active P p) :
    ∃φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀i,φ ((x).sampler.scalarPrefix.basis.generator i)=
        IntegralFramedPhysicalSuffixTest.rawTuple B (sampleContext ctx) w hv (i.val+offset)^
          UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon P p)
            (2^(G).width old) ((G).birth old) i) ∧
      ∀e k,e≤2^(P).width (RankedHistoryTask.root p)→k≤2^(P).width (RankedHistoryTask.root p)→
        IntegralMixedPhysicalTraceCutGuards.sign hn ht ha hR outer
          (FiniteCoefficientSignScan.query (stage ctx w u) e k)=InfinitesimalSign.encode
          (SignType.sign (φ ((IntegralMixedRelativeCuts.factor x (IntegralMixedCutSource.Family.birth_bound G old)
            (IntegralMixedCutSource.Family.rule G old)
            (IntegralMixedRelativeCuts.atChoice (IntegralMixedCutSource.Family.rule G old)
              (IntegralMixedCutSource.Family.kind G old) k)).coeff e))) :=by
  have HR : pairFst ((B).key (sampleContext ctx))=pairFst (sampleContext ctx) :=by
    exact (IntegralMixedPhysicalMarkedPlan.key_root hn ht ha hR outer ctx).trans (pairFst_pair ctx []).symm
  obtain ⟨φ,hφ,HE⟩:=IntegralFramedPhysicalTraceCutSource.exists_coefficient_evaluation B
    (IntegralMixedPhysicalTraceCutTest.key_context hn ht ha hR outer) (sampleContext ctx) w hv u
    (IntegralMixedPhysicalTraceCutTest.factor_positive hn ht ha hR outer)
    (IntegralMixedPhysicalTraceCutTest.fallback hn ht ha hR outer)
    (tables hn ht ha hR outer) (represents hn ht ha hR outer) HR hfit hactive
  exact ⟨φ,hφ,fun e k he hk=>(sign_packet hn ht ha hR outer ctx w u e k).trans (HE e k he hk)⟩

end LeanCanny.Encoding.IntegralMixedPhysicalCutCoefficientSemantics
