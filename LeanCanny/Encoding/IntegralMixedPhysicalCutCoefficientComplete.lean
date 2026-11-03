/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalCutCoefficientInterpretation
public import LeanCanny.Algebra.IntegralMixedRelativeCutCoefficientIff
/-! # Native coefficient guards are complete at the same full-word suffix

No native guard is assumed in the reverse direction. The actual factor degree
forces every extra coefficient queried up to the declared scalar width to zero.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalCutCoefficientComplete
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (family)
open IntegralMixedPhysicalMarkedPlan (bank tables)
open IntegralMixedPhysicalCutOpenInterval (parent Bounds)
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
private theorem choice_eq (F : IntegralMixedCutSource.Family) (key : List Bool) :
    IntegralMixedRawKindBits.choice F key=IntegralMixedRelativeCuts.choiceIndex (F.rule key) (F.kind key) :=by
  cases hk:F.kind key <;> simp only [IntegralMixedRawKindBits.choice,IntegralMixedRelativeCuts.choiceIndex,hk]
private theorem local_choice (q w : List Bool) :
    IntegralMixedPhysicalCutLocalGuards.choice hn ht ha hR outer (pair q w)=
      IntegralMixedRawKindBits.choice G (IntegralMixedVirtualTaskBits.saved P (parent hn ht ha hR outer q)) :=by
  simp only [IntegralMixedPhysicalCutLocalGuards.choice,IntegralFramedTraceCutGuards.choice,
    IntegralFramedTraceCutGuards.parent,Function.comp_apply,IntegralFramedTraceCutGuards.descriptor,
    IntegralFramedTraceCutGuards.root,IntegralMixedPhysicalCutOpenInterval.guardContext,
    parent,pairFst_pair,pairSnd_pair]
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

abbrev Tail (φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) : Prop :=
 ∀i,φ ((x).sampler.scalarPrefix.basis.generator i)=
   IntegralFramedPhysicalSuffixTest.rawTuple B q w hv (i.val+offset)^
     UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon P p)
       (2^(G).width old) ((G).birth old) i

theorem coefficient_evaluation_at (hb : Bounds hn ht ha hR outer (pair q w))
    (φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (hφ : Tail hn ht ha hR outer q w hv φ) :
    ∀e k,e≤2^(P).width (pairFst q)→k≤2^(P).width (pairFst q)→
      IntegralMixedPhysicalCutLocalGuards.sign hn ht ha hR outer
        (FiniteCoefficientSignScan.query (pair q w) e k)=InfinitesimalSign.encode
          (SignType.sign (φ ((IntegralMixedRelativeCuts.factor x hm r
            (IntegralMixedRelativeCuts.atChoice r kind k)).coeff e))) :=by
  obtain ⟨ψ,hψ,HE⟩:=IntegralMixedPhysicalCutLocalInterpretation.coefficient_evaluation hn ht ha hR outer q w hv hb
  have HX : ψ=φ :=(x).sampler.scalarPrefix.basis.algHom_ext ψ φ (fun i=>(hψ i).trans (hφ i).symm)
  simpa only [HX] using HE

theorem guards_iff (hb : Bounds hn ht ha hR outer (pair q w))
    (φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (hφ : Tail hn ht ha hR outer q w hv φ) :
    IntegralMixedPhysicalCutCoefficientOnly.Guards hn ht ha hR outer (pair q w) ↔
      IntegralMixedRelativeCuts.CoefficientGuards x hm r φ kind ((G).degree old) :=by
  constructor
  · intro hg
    obtain ⟨ψ,hψ,hgψ⟩:=IntegralMixedPhysicalCutCoefficientOnly.coefficient_guards hn ht ha hR outer q w hv hb hg
    have HX : ψ=φ :=(x).sampler.scalarPrefix.basis.algHom_ext ψ φ (fun i=>(hψ i).trans (hφ i).symm)
    simpa only [HX] using hgψ
  · intro hc
    have HE:=coefficient_evaluation_at hn ht ha hR outer q w hv hb φ hφ
    have HN:=(G).scalar_cap old
    rw [(IntegralMixedFramedHistoryFamilyBits.geometry P D H).width p,
      IntegralMixedPhysicalCutLocalInterpretation.parent_root hn ht ha hR outer q] at HN
    have HK : IntegralMixedRawKindBits.choice G old≤2^(P).width (pairFst q) :=
      (IntegralMixedRawKindBits.choice_le G old).trans HN
    have HD : (G).degree old≤2^(P).width (pairFst q):=((G).degree_bound old).trans HN
    have HZ (e k : ℕ) (he : e≤2^(P).width (pairFst q)) (hk : k≤2^(P).width (pairFst q)) :
        FiniteCoefficientSignScan.Zero (IntegralMixedPhysicalCutLocalGuards.sign hn ht ha hR outer)
          (pair q w) e k ↔ φ ((IntegralMixedRelativeCuts.factor x hm r (IntegralMixedRelativeCuts.atChoice r kind k)).coeff e)=0 :=by
      unfold FiniteCoefficientSignScan.Zero
      rw [HE e k he hk]
      exact (SquareSampleTestSign.encode_eq_iff _ _).trans sign_eq_zero_iff
    have ZA (c : IntegralMixedRelativeCuts.Kind ((G).spatial old) r) (e : ℕ)
        (he : IntegralMixedExceptionalBounds.auxiliaryCap ((G).ambient old+1) ((G).spatial old).degree<e) :
        φ ((IntegralMixedRelativeCuts.factor x hm r c).coeff e)=0 :=by
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt ((IntegralMixedRelativeCuts.factor_degree x hm r c).trans_lt he),map_zero]
    simp only [IntegralMixedPhysicalCutCoefficientOnly.Guards,FiniteCoefficientSignScan.Guards,
      Function.comp_apply,pairFst_pair,IntegralMixedPhysicalCutLocalGuards.cap]
    rw [local_choice hn ht ha hR outer q w,IntegralMixedPhysicalCutOpenInterval.degree_eq hn ht ha hR outer q]
    refine ⟨?_,?_,?_,Or.inl (by change InfinitesimalSign.encode 1≠InfinitesimalSign.encode 0;decide)⟩
    · intro k hk e he
      have hk' : k<IntegralMixedRelativeCuts.choiceIndex r kind :=by rw [←choice_eq];exact hk
      apply (HZ e k (by omega) (hk.le.trans HK)).mpr
      rw [IntegralMixedRelativeCuts.atChoice_lower r kind k hk']
      by_cases he' : e≤IntegralMixedExceptionalBounds.auxiliaryCap ((G).ambient old+1) ((G).spatial old).degree
      · exact hc.1 k hk' e he'
      · exact ZA _ e (by omega)
    · intro hz
      apply hc.2.1
      have H0:=(HZ ((G).degree old) (IntegralMixedRawKindBits.choice G old) HD HK).mp hz
      rw [choice_eq,IntegralMixedRelativeCuts.atChoice_self] at H0
      exact H0
    · intro e he hed
      apply (HZ e (IntegralMixedRawKindBits.choice G old) (by omega) HK).mpr
      rw [choice_eq,IntegralMixedRelativeCuts.atChoice_self]
      by_cases he' : e≤IntegralMixedExceptionalBounds.auxiliaryCap ((G).ambient old+1) ((G).spatial old).degree
      · exact hc.2.2 e hed he'
      · exact ZA _ e (by omega)

theorem guards_iff_valid_degree (hb : Bounds hn ht ha hR outer (pair q w))
    (φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (hφ : Tail hn ht ha hR outer q w hv φ) :
    IntegralMixedPhysicalCutCoefficientOnly.Guards hn ht ha hR outer (pair q w) ↔
      IntegralMixedRelativeCuts.Valid x hm r φ kind ∧
        ((IntegralMixedRelativeCuts.factor x hm r kind).map φ.toRingHom).natDegree=(G).degree old :=
  (guards_iff hn ht ha hR outer q w hv hb φ hφ).trans
    (IntegralMixedRelativeCuts.coefficientGuards_iff_valid_degree x hm r φ kind ((G).degree old))

end LeanCanny.Encoding.IntegralMixedPhysicalCutCoefficientComplete
