/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalCutHead
public import LeanCanny.Encoding.IntegralFramedPhysicalCutRootGuard
/-! # Native full cut guards certify the actual retained quotient root -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalCutCoefficientSemantics
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedPhysicalMarkedPlan (bank tables represents)
open IntegralMixedPhysicalMarkedTest (input sampleContext)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] bank tables IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedPhysicalTraceCutGuards.sign IntegralMixedPhysicalTraceCutGuards.head

private theorem kind_choice (G : IntegralMixedCutSource.Family) (key : List Bool) :
    IntegralMixedRawKindBits.choice G key=IntegralMixedRelativeCuts.choiceIndex (G.rule key) (G.kind key) :=by
  cases hk:G.kind key <;> simp only [IntegralMixedRawKindBits.choice,IntegralMixedRelativeCuts.choiceIndex,hk]

variable {n : List Bool→ℕ} {t : List Bool→Term}
  (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R) (outer : Bool)
  (ctx w u : List Bool)
  (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR outer) (sampleContext ctx) w)
local notation "B" => bank hn ht ha hR outer
local notation "P" => IntegralFramedBankQuery.Bank.parameters B
local notation "D" => IntegralFramedBankQuery.Bank.plan B
local notation "H" => IntegralFramedBankQuery.Bank.data B
local notation "p" => IntegralFramedPhysicalTraceCutSource.parent B (sampleContext ctx) u
local notation "G" => IntegralMixedFramedHistoryFamilyBits.family P D H
local notation "old" => IntegralMixedVirtualTaskBits.saved P p
local notation "x" => IntegralMixedCutSource.Family.state G old
local notation "bound" => IntegralMixedCutSource.Family.birth_bound G old
local notation "rule" => IntegralMixedCutSource.Family.rule G old
local notation "kind" => IntegralMixedCutSource.Family.kind G old
local notation "degree" => IntegralMixedCutSource.Family.degree G old
local notation "offset" => IntegralFramedTerminalCutTest.count P D H
  (IntegralFramedPhysicalTraceCutSource.taskKey B) p-IntegralMixedCutSource.Family.birth G old
noncomputable def bankQuotient : ℝ := IntegralMixedFramedBankObservation.Data.point
  (IntegralMixedFramedBankObservation.ofState ((G).state ((B).key (sampleContext ctx))))
  (IntegralFramedPhysicalSuffixTest.rawTuple B (sampleContext ctx) w hv)
  ((G).birth ((B).key (sampleContext ctx))-IntegralCriticalHistoryTask.birth P p-1)
local notation "quotient" => bankQuotient hn ht ha hR outer ctx w u hv

theorem exists_factor_root
    (hactive : IntegralMixedFramedFullCutProbeBits.Active P p)
    (hcut : IntegralFramedCreatingCut.ParentCut P D p)
    (hfit : IntegralCriticalHistoryTask.birth P p<(G).birth ((B).key (sampleContext ctx)))
    (hb : IntegralCriticalHistoryTask.birth P p=u.length)
    (hg : IntegralMixedPhysicalTraceCutGuards.Guards hn ht ha hR outer (stage ctx w u)) :
    ∃φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀i,φ ((x).sampler.scalarPrefix.basis.generator i)=
        IntegralFramedPhysicalSuffixTest.rawTuple B (sampleContext ctx) w hv (i.val+offset)^
          UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon P p)
            (2^(G).width old) ((G).birth old) i) ∧
      IntegralMixedRelativeCuts.Valid x bound rule φ kind ∧
      ((IntegralMixedRelativeCuts.factor x bound rule kind).map φ.toRingHom).natDegree=degree ∧
      (IntegralMixedRelativeCuts.factor x bound rule kind).eval₂ φ.toRingHom quotient=0 :=by
  have HM : (G).birth old=IntegralCriticalHistoryTask.birth P p :=
    (IntegralMixedFramedHistoryFamilyBits.geometry P D H).birth p
  have HF : (G).birth old≤(G).birth ((B).key (sampleContext ctx)):=HM.trans_le hfit.le
  obtain ⟨φ,hφ,HC⟩:=exists_coefficient_guards hn ht ha hR outer ctx w u hv HF hactive hg
  have HR : pairFst ((B).key (sampleContext ctx))=RankedHistoryTask.root p :=
    (IntegralMixedPhysicalMarkedPlan.key_root hn ht ha hR outer ctx).trans (root_parent hn ht ha hR outer ctx u).symm
  have HS:=IntegralFramedPhysicalTraceCutSource.factor_root_guard B
    (IntegralMixedPhysicalTraceCutTest.key_context hn ht ha hR outer) (sampleContext ctx) w hv u
    hactive hcut HR hfit φ hφ HC
  have HRoot : (IntegralMixedRelativeCuts.factor x bound rule kind).eval₂ φ.toRingHom
      (IntegralRelativeTruncation.jointQuotient (x).sampler.scalarPrefix
        (IntegralMixedRelativeCuts.factor x bound rule kind) degree
        (IntegralFramedPhysicalTraceCutSource.cutTuple B (sampleContext ctx) w hv u))=0 :=by
    apply HS.mpr
    rcases hg.2.2.2 with HH|HZ
    · left
      have HT : (G).birth ((B).key (sampleContext ctx))=
          IntegralMixedPhysicalReplayNew.count hn ht ha hR outer (sampleContext ctx) :=rfl
      have HH' := mt (head_zero_iff hn ht ha hR outer ctx w u hv (by rw [←HT,←hb];exact hfit)).mpr HH
      simpa only [IntegralFramedPhysicalTraceCutSource.cutTuple,Fin.val_zero,Nat.zero_add,HT,hb,Nat.sub_sub] using HH'
    · right
      have HK : IntegralMixedRawKindBits.choice G old≤2^(P).width (RankedHistoryTask.root p) :=
        (IntegralMixedRawKindBits.choice_le G old).trans
          (by simpa only [(IntegralMixedFramedHistoryFamilyBits.geometry P D H).width p] using (G).scalar_cap old)
      have HE:=IntegralFramedPhysicalTraceCutSource.evaluation B
        (IntegralMixedPhysicalTraceCutTest.key_context hn ht ha hR outer)
        (IntegralMixedPhysicalTraceCutTest.factor_positive hn ht ha hR outer)
        (IntegralMixedPhysicalTraceCutTest.fallback hn ht ha hR outer)
        (tables hn ht ha hR outer) (represents hn ht ha hR outer) (sampleContext ctx) w hv u hactive
        (HF.trans_eq (IntegralFramedPhysicalTraceCutSource.count_parent B
          (IntegralMixedPhysicalTraceCutTest.key_context hn ht ha hR outer) (sampleContext ctx) u).symm)
        φ hφ 0 (IntegralMixedRawKindBits.choice G old) (Nat.zero_le _) HK
      have HE':=(sign_packet hn ht ha hR outer ctx w u 0 (IntegralMixedRawKindBits.choice G old)).trans HE
      rw [kind_choice,IntegralMixedRelativeCuts.atChoice_self] at HE'
      have HCQ : IntegralFramedTraceCutGuards.choice P D H (stage ctx w u)=IntegralMixedRawKindBits.choice G old :=by
        unfold IntegralFramedTraceCutGuards.choice
        rw [parent_packet]
      change IntegralMixedPhysicalTraceCutGuards.sign hn ht ha hR outer
        (FiniteCoefficientSignScan.query (stage ctx w u) 0
          (IntegralFramedTraceCutGuards.choice P D H (stage ctx w u)))=InfinitesimalSign.encode 0 at HZ
      rw [HCQ,kind_choice,HE'] at HZ
      exact sign_eq_zero_iff.mp ((SquareSampleTestSign.encode_eq_iff _ _).mp HZ)
  have HQ:=IntegralFramedTerminalCutBankPoint.point_eq P D H p ((B).key (sampleContext ctx)) hactive hcut HR hfit
    (IntegralFramedPhysicalSuffixTest.rawTuple B (sampleContext ctx) w hv)
  exact ⟨φ,hφ,IntegralMixedRelativeCuts.coefficientGuards_valid _ _ _ _ _ _ HC,
    IntegralMixedRelativeCuts.coefficientGuards_degree _ _ _ _ _ _ HC,
    (congrArg (fun z : ℝ=>(IntegralMixedRelativeCuts.factor x bound rule kind).eval₂ φ.toRingHom z) HQ).trans HRoot⟩

end LeanCanny.Encoding.IntegralMixedPhysicalCutCoefficientSemantics
