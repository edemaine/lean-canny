/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedPhysicalCutCoefficientOnly
/-! # Coefficient-only probes validate factors without asking for a real root -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalCutCoefficientOnly
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (family)
open IntegralMixedPhysicalMarkedPlan (bank native tables represents)
open IntegralMixedPhysicalCutOpenInterval (birthWord parent Bounds count)
open IntegralMixedPhysicalCutLocalInterpretation (coefficient_evaluation fits parent_root)
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

theorem coefficient_guards (hb : Bounds hn ht ha hR outer (pair q w))
    (hg : Guards hn ht ha hR outer (pair q w)) :
    ∃φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀i,φ ((x).sampler.scalarPrefix.basis.generator i)=
        IntegralFramedPhysicalSuffixTest.rawTuple B q w hv (i.val+offset)^
          UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon P p)
            (2^(G).width old) ((G).birth old) i) ∧
      IntegralMixedRelativeCuts.CoefficientGuards x hm r φ kind ((G).degree old) :=by
  obtain ⟨φ,hφ,HE⟩:=coefficient_evaluation hn ht ha hR outer q w hv hb
  have HN:=(G).scalar_cap old
  rw [(IntegralMixedFramedHistoryFamilyBits.geometry P D H).width p,parent_root hn ht ha hR outer q] at HN
  have HK : IntegralMixedRawKindBits.choice G old≤2^(P).width (pairFst q) :=
    (IntegralMixedRawKindBits.choice_le G old).trans HN
  have HD : (G).degree old≤2^(P).width (pairFst q):=((G).degree_bound old).trans HN
  have HG:=hg
  simp only [Guards,FiniteCoefficientSignScan.Guards,
    Function.comp_apply,pairFst_pair,IntegralMixedPhysicalCutLocalGuards.cap] at HG
  rw [local_choice hn ht ha hR outer q w,IntegralMixedPhysicalCutOpenInterval.degree_eq hn ht ha hR outer q] at HG
  rcases HG with ⟨hLower,hLeading,hHigher,_⟩
  have HZ (e k : ℕ) (he : e≤2^(P).width (pairFst q)) (hk : k≤2^(P).width (pairFst q)) :
      FiniteCoefficientSignScan.Zero (IntegralMixedPhysicalCutLocalGuards.sign hn ht ha hR outer)
        (pair q w) e k ↔ φ ((IntegralMixedRelativeCuts.factor x hm r (IntegralMixedRelativeCuts.atChoice r kind k)).coeff e)=0 :=by
    unfold FiniteCoefficientSignScan.Zero
    rw [HE e k he hk]
    exact (SquareSampleTestSign.encode_eq_iff _ _).trans sign_eq_zero_iff
  refine ⟨φ,hφ,?_,?_,?_⟩
  · intro k hk e he
    have hk' : k<IntegralMixedRawKindBits.choice G old :=by rw [choice_eq];exact hk
    have H0:=(HZ e k (he.trans HN) (hk'.le.trans HK)).mp (hLower k hk' e (Nat.lt_succ_of_le (he.trans HN)))
    rw [IntegralMixedRelativeCuts.atChoice_lower _ _ _ hk] at H0
    exact H0
  · intro hz
    apply hLeading
    apply (HZ ((G).degree old) (IntegralMixedRawKindBits.choice G old) HD HK).mpr
    rw [choice_eq,IntegralMixedRelativeCuts.atChoice_self]
    exact hz
  · intro e he hcap
    have H0:=(HZ e (IntegralMixedRawKindBits.choice G old) (hcap.trans HN) HK).mp
      (hHigher e (Nat.lt_succ_of_le (hcap.trans HN)) he)
    rw [choice_eq,IntegralMixedRelativeCuts.atChoice_self] at H0
    exact H0

theorem interpreted_guards (hb : Bounds hn ht ha hR outer (pair q w))
    (hg : Guards hn ht ha hR outer (pair q w)) :
    ∃φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀i,φ ((x).sampler.scalarPrefix.basis.generator i)=
        IntegralFramedPhysicalSquare.scalarTuple P D H (B).nodes (B).factor (B).seed (B).bounds
          (B).key (B).positive q w hv (UniformIntegralPowerSchedule.embed (fits hn ht ha hR outer q w hb) i)^
          UniformIntegralPowerSchedule.weights ((P).cap (pairFst old)+1) (2^(G).width old) ((G).birth old) i) ∧
      IntegralMixedRelativeCuts.Valid x hm r φ kind ∧
      IntegralMixedFramedFullCutIntervalSelected.factor P D H (parent hn ht ha hR outer) q φ≠0 ∧
      (IntegralMixedFramedFullCutIntervalSelected.factor P D H (parent hn ht ha hR outer) q φ).natDegree=
        IntegralMixedPhysicalCutOpenInterval.degree hn ht ha hR outer q :=by
  obtain ⟨φ,hφ,hgφ⟩:=coefficient_guards hn ht ha hR outer q w hv hb hg
  have HV:=IntegralMixedRelativeCuts.coefficientGuards_valid x hm r φ kind ((G).degree old) hgφ
  refine ⟨φ,?_,HV,IntegralMixedRelativeCuts.selected_nonzero x hm r φ kind HV,?_⟩
  · intro i
    have HC : IntegralFramedTerminalCutTest.count P D H
        (IntegralFramedPhysicalTraceCutSource.taskKey B) p=(G).birth ((B).key q) :=
      IntegralFramedPhysicalTraceCutSource.count_parent B
        (IntegralMixedPhysicalTraceCutTest.key_context hn ht ha hR outer) q (birthWord q)
    have HX : IntegralFramedPhysicalSuffixTest.rawTuple B q w hv (i.val+offset)=
        IntegralFramedPhysicalSquare.scalarTuple P D H (B).nodes (B).factor (B).seed (B).bounds
          (B).key (B).positive q w hv (UniformIntegralPowerSchedule.embed (fits hn ht ha hR outer q w hb) i) :=by
      refine (congrArg (IntegralFramedPhysicalSuffixTest.rawTuple B q w hv)
        (congrArg (fun v=>i.val+(v-(G).birth old)) HC)).trans ?_
      have HI : i.val+((G).birth ((B).key q)-(G).birth old)<(G).birth ((B).key q) :=by
        have HH:=i.isLt
        have HF:=fits hn ht ha hR outer q w hb
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
  · exact (IntegralMixedRelativeCuts.coefficientGuards_degree x hm r φ kind ((G).degree old) hgφ).trans
      (IntegralMixedPhysicalCutOpenInterval.degree_eq hn ht ha hR outer q).symm

end LeanCanny.Encoding.IntegralMixedPhysicalCutCoefficientOnly
