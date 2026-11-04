/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalCutValidity
public import LeanCanny.Algebra.IntegralMixedRelativeCutCoefficientIff
/-! # Constructed coefficient receipts imply the actual same-word cut guard

The old interpretation is matched to the SAME full tuple by its generator
equations. The final zero-head condition is explicit; it is discharged by
the constructed untruncated factor root and newest quotient readback.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalCutCoefficientSemantics
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedPhysicalMarkedPlan (bank tables)
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
local notation "offset"=>IntegralFramedTerminalCutTest.count P D H
  (IntegralFramedPhysicalTraceCutSource.taskKey B) p-IntegralMixedCutSource.Family.birth G old
attribute [local irreducible] bank tables IntegralMixedFramedHistoryFamilyBits.family

private theorem fullChoice_eq (F :IntegralMixedCutSource.Family) (key :List Bool) :
    IntegralMixedRawKindBits.choice F key=IntegralMixedRelativeCuts.choiceIndex (F.rule key) (F.kind key):=by
  cases hk:F.kind key <;> simp only [IntegralMixedRawKindBits.choice,IntegralMixedRelativeCuts.choiceIndex,hk]

theorem coefficient_evaluation_at
    (hfit :(G).birth old≤(G).birth ((B).key (sampleContext ctx)))
    (hactive :IntegralMixedFramedFullCutProbeBits.Active P p)
    (φ :(x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ :∀i,φ ((x).sampler.scalarPrefix.basis.generator i)=
      IntegralFramedPhysicalSuffixTest.rawTuple B (sampleContext ctx) w hv (i.val+offset)^
        UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon P p)
          (2^(G).width old) ((G).birth old) i) :
    ∀e k,e≤2^(P).width ctx→k≤2^(P).width ctx→
      IntegralMixedPhysicalTraceCutGuards.sign hn ht ha hR outer
        (FiniteCoefficientSignScan.query (stage ctx w u) e k)=InfinitesimalSign.encode
          (SignType.sign (φ ((IntegralMixedRelativeCuts.factor x bound rule
            (IntegralMixedRelativeCuts.atChoice rule kind k)).coeff e))):=by
  obtain ⟨ψ,hψ,HE⟩:=exists_coefficient_evaluation hn ht ha hR outer ctx w u hv hfit hactive
  have HX :ψ=φ :=(x).sampler.scalarPrefix.basis.algHom_ext ψ φ (fun i=>(hψ i).trans (hφ i).symm)
  intro e k he hk
  simpa only [HX,root_parent hn ht ha hR outer ctx u] using HE e k
    (by simpa only [root_parent hn ht ha hR outer ctx u] using he)
    (by simpa only [root_parent hn ht ha hR outer ctx u] using hk)

theorem guards_of_coefficient_receipt
    (hfit :(G).birth old≤(G).birth ((B).key (sampleContext ctx)))
    (hactive :IntegralMixedFramedFullCutProbeBits.Active P p)
    (φ :(x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ :∀i,φ ((x).sampler.scalarPrefix.basis.generator i)=
      IntegralFramedPhysicalSuffixTest.rawTuple B (sampleContext ctx) w hv (i.val+offset)^
        UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon P p)
          (2^(G).width old) ((G).birth old) i)
    (hc :IntegralMixedRelativeCuts.CoefficientGuards x bound rule φ kind ((G).degree old))
    (hzero :IntegralMixedPhysicalTraceCutGuards.head hn ht ha hR outer (stage ctx w u)=InfinitesimalSign.encode 0→
      φ ((IntegralMixedRelativeCuts.factor x bound rule kind).coeff 0)=0) :
    IntegralMixedPhysicalTraceCutGuards.Guards hn ht ha hR outer (stage ctx w u):=by
  have HE:=coefficient_evaluation_at hn ht ha hR outer ctx w u hv hfit hactive φ hφ
  have HN:=(G).scalar_cap old
  rw [(IntegralMixedFramedHistoryFamilyBits.geometry P D H).width p,root_parent hn ht ha hR outer ctx u] at HN
  have HK :IntegralMixedRawKindBits.choice G old≤2^(P).width ctx:=
    (IntegralMixedRawKindBits.choice_le G old).trans HN
  have HD :(G).degree old≤2^(P).width ctx:=((G).degree_bound old).trans HN
  have HZ (e k :ℕ) (he :e≤2^(P).width ctx) (hk :k≤2^(P).width ctx) :
      FiniteCoefficientSignScan.Zero (IntegralMixedPhysicalTraceCutGuards.sign hn ht ha hR outer)
        (stage ctx w u) e k ↔
      φ ((IntegralMixedRelativeCuts.factor x bound rule (IntegralMixedRelativeCuts.atChoice rule kind k)).coeff e)=0:=by
    unfold FiniteCoefficientSignScan.Zero
    rw [HE e k he hk]
    exact (SquareSampleTestSign.encode_eq_iff _ _).trans sign_eq_zero_iff
  have ZA (c :IntegralMixedRelativeCuts.Kind ((G).spatial old) rule) (e :ℕ)
      (he :IntegralMixedExceptionalBounds.auxiliaryCap ((G).ambient old+1) ((G).spatial old).degree<e) :
      φ ((IntegralMixedRelativeCuts.factor x bound rule c).coeff e)=0:=by
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt ((IntegralMixedRelativeCuts.factor_degree x bound rule c).trans_lt he),map_zero]
  simp only [IntegralMixedPhysicalTraceCutGuards.Guards,FiniteCoefficientSignScan.Guards,
    IntegralFramedTraceCutGuards.choice,IntegralFramedTraceCutGuards.degree,IntegralFramedTraceCutGuards.cap]
  simp only [parent_packet hn ht ha hR outer ctx w u]
  simp only [IntegralFramedTraceCutGuards.root,stage,pairFst_pair]
  refine ⟨?_,?_,?_,?_⟩
  · intro k hk e he
    have hk' :k<IntegralMixedRelativeCuts.choiceIndex rule kind:=by rw [←fullChoice_eq G old];exact hk
    apply (HZ e k (by omega) (hk.le.trans HK)).mpr
    rw [IntegralMixedRelativeCuts.atChoice_lower rule kind k hk']
    by_cases he' :e≤IntegralMixedExceptionalBounds.auxiliaryCap ((G).ambient old+1) ((G).spatial old).degree
    · exact hc.1 k hk' e he'
    · exact ZA _ e (by omega)
  · intro hz
    apply hc.2.1
    have HH:=(HZ ((G).degree old) (IntegralMixedRawKindBits.choice G old) HD HK).mp hz
    rw [fullChoice_eq G old,IntegralMixedRelativeCuts.atChoice_self] at HH
    exact HH
  · intro e he hed
    apply (HZ e (IntegralMixedRawKindBits.choice G old) (by omega) HK).mpr
    rw [fullChoice_eq G old,IntegralMixedRelativeCuts.atChoice_self]
    by_cases he' :e≤IntegralMixedExceptionalBounds.auxiliaryCap ((G).ambient old+1) ((G).spatial old).degree
    · exact hc.2.2 e hed he'
    · exact ZA _ e (by omega)
  · by_cases hh :IntegralMixedPhysicalTraceCutGuards.head hn ht ha hR outer (stage ctx w u)=InfinitesimalSign.encode 0
    · right
      apply (HZ 0 (IntegralMixedRawKindBits.choice G old) (Nat.zero_le _) HK).mpr
      rw [fullChoice_eq G old,IntegralMixedRelativeCuts.atChoice_self]
      exact hzero hh
    · exact Or.inl hh

theorem guards_of_valid_degree
    (hfit :(G).birth old≤(G).birth ((B).key (sampleContext ctx)))
    (hactive :IntegralMixedFramedFullCutProbeBits.Active P p)
    (φ :(x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ :∀i,φ ((x).sampler.scalarPrefix.basis.generator i)=
      IntegralFramedPhysicalSuffixTest.rawTuple B (sampleContext ctx) w hv (i.val+offset)^
        UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon P p)
          (2^(G).width old) ((G).birth old) i)
    (hvalid :IntegralMixedRelativeCuts.Valid x bound rule φ kind)
    (hdegree :((IntegralMixedRelativeCuts.factor x bound rule kind).map φ.toRingHom).natDegree=(G).degree old)
    (hzero :IntegralMixedPhysicalTraceCutGuards.head hn ht ha hR outer (stage ctx w u)=InfinitesimalSign.encode 0→
      φ ((IntegralMixedRelativeCuts.factor x bound rule kind).coeff 0)=0) :
    IntegralMixedPhysicalTraceCutGuards.Guards hn ht ha hR outer (stage ctx w u):=by
  apply guards_of_coefficient_receipt hn ht ha hR outer ctx w u hv hfit hactive φ hφ
    ((IntegralMixedRelativeCuts.coefficientGuards_iff_valid_degree x bound rule φ kind ((G).degree old)).mpr
      ⟨hvalid,hdegree⟩) hzero

end LeanCanny.Encoding.IntegralMixedPhysicalCutCoefficientSemantics
