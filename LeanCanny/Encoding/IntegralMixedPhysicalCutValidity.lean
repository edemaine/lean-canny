/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalCutCoefficientSemantics
public import LeanCanny.Algebra.IntegralMixedRelativeCutFiniteGuards

/-! # Accepted full cut tests certify the actual relative factor and degree -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalCutCoefficientSemantics
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedPhysicalMarkedPlan (bank)
open IntegralMixedPhysicalMarkedTest (input sampleContext)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] bank IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedPhysicalTraceCutGuards.sign IntegralMixedPhysicalTraceCutGuards.head

private theorem choice_eq (G : IntegralMixedCutSource.Family) (key : List Bool) :
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
local notation "offset" => IntegralFramedTerminalCutTest.count P D H
  (IntegralFramedPhysicalTraceCutSource.taskKey B) p-IntegralMixedCutSource.Family.birth G old

theorem root_parent : RankedHistoryTask.root p=ctx :=by
  simp only [IntegralFramedPhysicalTraceCutSource.parent,IntegralFramedTraceCutTask.task_root,sampleContext,pairFst_pair]

theorem exists_coefficient_guards
    (hfit : (G).birth old≤(G).birth ((B).key (sampleContext ctx)))
    (hactive : IntegralMixedFramedFullCutProbeBits.Active P p)
    (hg : IntegralMixedPhysicalTraceCutGuards.Guards hn ht ha hR outer (stage ctx w u)) :
    ∃φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀i,φ ((x).sampler.scalarPrefix.basis.generator i)=
        IntegralFramedPhysicalSuffixTest.rawTuple B (sampleContext ctx) w hv (i.val+offset)^
          UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon P p)
            (2^(G).width old) ((G).birth old) i) ∧
      IntegralMixedRelativeCuts.CoefficientGuards x bound rule φ kind ((G).degree old) :=by
  obtain ⟨φ,hφ,HE⟩:=exists_coefficient_evaluation hn ht ha hR outer ctx w u hv hfit hactive
  have HN:=(G).scalar_cap old
  rw [(IntegralMixedFramedHistoryFamilyBits.geometry P D H).width p,root_parent hn ht ha hR outer ctx u] at HN
  have HK : IntegralMixedRawKindBits.choice G old≤2^(P).width ctx :=
    (IntegralMixedRawKindBits.choice_le G old).trans HN
  have HD : (G).degree old≤2^(P).width ctx := ((G).degree_bound old).trans HN
  have HG:=hg
  simp only [IntegralMixedPhysicalTraceCutGuards.Guards,FiniteCoefficientSignScan.Guards,
    IntegralFramedTraceCutGuards.choice,IntegralFramedTraceCutGuards.degree,IntegralFramedTraceCutGuards.cap] at HG
  simp only [parent_packet hn ht ha hR outer ctx w u] at HG
  simp only [IntegralFramedTraceCutGuards.root,stage,pairFst_pair] at HG
  rcases HG with ⟨hLower,hLeading,hHigher,_⟩
  have HZ (e k : ℕ) (he : e≤2^(P).width ctx) (hk : k≤2^(P).width ctx) :
      FiniteCoefficientSignScan.Zero (IntegralMixedPhysicalTraceCutGuards.sign hn ht ha hR outer)
        (stage ctx w u) e k ↔
      φ ((IntegralMixedRelativeCuts.factor x bound rule (IntegralMixedRelativeCuts.atChoice rule kind k)).coeff e)=0 :=by
    unfold FiniteCoefficientSignScan.Zero
    rw [HE e k (by simpa only [root_parent hn ht ha hR outer ctx u] using he)
      (by simpa only [root_parent hn ht ha hR outer ctx u] using hk)]
    exact (SquareSampleTestSign.encode_eq_iff _ _).trans sign_eq_zero_iff
  refine ⟨φ,hφ,?_,?_,?_⟩
  · intro k hk e he
    have hk' : k<IntegralMixedRawKindBits.choice G old :=by rw [choice_eq];exact hk
    have HE':=(HZ e k (he.trans HN) (hk'.le.trans HK)).mp
      (hLower k hk' e (Nat.lt_succ_of_le (he.trans HN)))
    rw [IntegralMixedRelativeCuts.atChoice_lower _ _ _ hk] at HE'
    exact HE'
  · intro hz
    apply hLeading
    apply (HZ ((G).degree old) (IntegralMixedRawKindBits.choice G old) HD HK).mpr
    rw [choice_eq,IntegralMixedRelativeCuts.atChoice_self]
    exact hz
  · intro e he hcap
    have HE':=(HZ e (IntegralMixedRawKindBits.choice G old) (hcap.trans HN) HK).mp
      (hHigher e (Nat.lt_succ_of_le (hcap.trans HN)) he)
    rw [choice_eq,IntegralMixedRelativeCuts.atChoice_self] at HE'
    exact HE'

include hv in
theorem exists_valid_and_degree
    (hfit : (G).birth old≤(G).birth ((B).key (sampleContext ctx)))
    (hactive : IntegralMixedFramedFullCutProbeBits.Active P p)
    (hg : IntegralMixedPhysicalTraceCutGuards.Guards hn ht ha hR outer (stage ctx w u)) :
    ∃φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      IntegralMixedRelativeCuts.Valid x bound rule φ kind ∧
      ((IntegralMixedRelativeCuts.factor x bound rule kind).map φ.toRingHom).natDegree=(G).degree old :=by
  obtain ⟨φ,_,HC⟩:=exists_coefficient_guards hn ht ha hR outer ctx w u hv hfit hactive hg
  exact ⟨φ,IntegralMixedRelativeCuts.coefficientGuards_valid _ _ _ _ _ _ HC,
    IntegralMixedRelativeCuts.coefficientGuards_degree _ _ _ _ _ _ HC⟩

end LeanCanny.Encoding.IntegralMixedPhysicalCutCoefficientSemantics
