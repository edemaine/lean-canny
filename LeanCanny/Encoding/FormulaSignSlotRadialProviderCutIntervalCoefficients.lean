/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderCutIntervalContext
public import LeanCanny.Algebra.IntegralMixedRelativeCutNativeGuards
public import LeanCanny.Encoding.IntegralFramedPhysicalTraceCutParent
/-! # Interval coefficient guards interpret the actual same-word parent algebra -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderCutInterval
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P" => IntegralFramedBankQuery.Bank.parameters FormulaSignSlotRadialProviderRecordPlan.bank
local notation "D" => IntegralFramedBankQuery.Bank.plan FormulaSignSlotRadialProviderRecordPlan.bank
local notation "H" => IntegralFramedBankQuery.Bank.data FormulaSignSlotRadialProviderRecordPlan.bank
local notation "T" => FormulaSignSlotRadialProviderRecordPlan.tables
local notation "G" => IntegralMixedFramedHistoryFamilyBits.family P D H

private theorem native_value : FormulaSignSlotRadialProviderAtomic.Cuts.value=
    IntegralFramedPhysicalTraceCutSource.value B FormulaSignSlotRadialProviderAtomic.Cuts.key_context
      FormulaSignSlotRadialProviderAtomic.Cuts.factor_positive FormulaSignSlotRadialProviderAtomic.Cuts.fallback
      T FormulaSignSlotRadialProviderAtomic.bank_represents := rfl

theorem parent_eq (q : List Bool) : parent q=IntegralFramedPhysicalTraceCutSource.parent B q (birthWord q) := rfl

private theorem guard_parent (q : List Bool) :
    IntegralFramedTraceCutGuards.parent P (guardContext q)=parent q := by
  simp only [IntegralFramedTraceCutGuards.parent,Function.comp_apply,IntegralFramedTraceCutGuards.descriptor,
    IntegralFramedTraceCutGuards.root,guardContext,parent,pairFst_pair,pairSnd_pair]

theorem interval_sign_packet (q w : List Bool) (e k : ℕ) :
    sign (FiniteCoefficientSignScan.query (pair q w) e k)=
      IntegralFramedPhysicalTraceCutSource.value B FormulaSignSlotRadialProviderAtomic.Cuts.key_context
        FormulaSignSlotRadialProviderAtomic.Cuts.factor_positive FormulaSignSlotRadialProviderAtomic.Cuts.fallback
        T FormulaSignSlotRadialProviderAtomic.bank_represents
        (pair (pair q w) (IntegralFramedPhysicalTraceCutSource.datum (birthWord q) e k)) := by
  simp only [sign,Function.comp_apply,signQuery,FiniteCoefficientSignScan.query,
    IntegralFramedPhysicalTraceCutSource.datum,pairFst_pair,pairSnd_pair,native_value]

private theorem kind_choice (F : IntegralMixedCutSource.Family) (key : List Bool) :
    IntegralMixedRawKindBits.choice F key=IntegralMixedRelativeCuts.choiceIndex (F.rule key) (F.kind key) := by
  cases hk:F.kind key <;> simp only [IntegralMixedRawKindBits.choice,IntegralMixedRelativeCuts.choiceIndex,hk]

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank IntegralMixedFramedHistoryFamilyBits.family parent sign
  IntegralFramedPhysicalSuffixTest.rawTuple

variable (q w : List Bool)
  (hw : SquareSampleCompleteVertices.Valid FormulaSignSlotRadialProviderAtomic.input q w)
local notation "old" => IntegralMixedVirtualTaskBits.saved P (parent q)
local notation "x" => IntegralMixedCutSource.Family.state G old
local notation "bound" => IntegralMixedCutSource.Family.birth_bound G old
local notation "rule" => IntegralMixedCutSource.Family.rule G old
local notation "kind" => IntegralMixedCutSource.Family.kind G old
local notation "offset" => IntegralFramedTerminalCutTest.count P D H (IntegralFramedPhysicalTraceCutSource.taskKey B) (parent q)-IntegralMixedCutSource.Family.birth G old

def IntervalGenerators (φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) : Prop :=
  ∀i,φ ((x).sampler.scalarPrefix.basis.generator i)=IntegralFramedPhysicalSuffixTest.rawTuple B q w hw (i.val+offset)^
    UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon P (parent q))
      (2^(G).width old) ((G).birth old) i

theorem interval_coefficient_evaluation (hb : Bounds (pair q w)) :
    ∃φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,IntervalGenerators q w hw φ ∧
      ∀e k,e≤2^(P).width (pairFst q)→k≤2^(P).width (pairFst q)→
        sign (FiniteCoefficientSignScan.query (pair q w) e k)=InfinitesimalSign.encode
          (SignType.sign (φ ((IntegralMixedRelativeCuts.factor x bound rule
            (IntegralMixedRelativeCuts.atChoice rule kind k)).coeff e))) := by
  have HP := IntegralFramedPhysicalTraceCutSource.exists_coefficient_evaluation B
    FormulaSignSlotRadialProviderAtomic.Cuts.key_context q w hw (birthWord q)
    FormulaSignSlotRadialProviderAtomic.Cuts.factor_positive FormulaSignSlotRadialProviderAtomic.Cuts.fallback
    T FormulaSignSlotRadialProviderAtomic.bank_represents (key_root q) (by rw [←parent_eq];exact fits q w hb)
    (by rw [←parent_eq];exact active q w hb)
  rw [←parent_eq q] at HP
  obtain ⟨φ,hφ,HE⟩ := HP
  refine ⟨φ,hφ,fun e k he hk=>?_⟩
  exact (interval_sign_packet q w e k).trans (HE e k (by rw [parent_root];exact he) (by rw [parent_root];exact hk))

theorem interval_evaluation_at (hb : Bounds (pair q w))
    (φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (hφ : IntervalGenerators q w hw φ) :
    ∀e k,e≤2^(P).width (pairFst q)→k≤2^(P).width (pairFst q)→
      sign (FiniteCoefficientSignScan.query (pair q w) e k)=InfinitesimalSign.encode
        (SignType.sign (φ ((IntegralMixedRelativeCuts.factor x bound rule
          (IntegralMixedRelativeCuts.atChoice rule kind k)).coeff e))) := by
  obtain ⟨ψ,hψ,HE⟩ := interval_coefficient_evaluation q w hw hb
  have HX : ψ=φ := (x).sampler.scalarPrefix.basis.algHom_ext ψ φ (fun i=>(hψ i).trans (hφ i).symm)
  cases HX
  exact HE

theorem interval_guards_iff_coefficients (hb : Bounds (pair q w))
    (φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (hφ : IntervalGenerators q w hw φ) :
    Guards (pair q w) ↔ IntegralMixedRelativeCuts.CoefficientGuards x bound rule φ kind ((G).degree old) := by
  have HW : (G).width old=(P).width (pairFst q) :=
    ((geometry P D H).width (parent q)).trans (congrArg (P).width (parent_root q))
  have HN := (G).scalar_cap old
  rw [HW] at HN
  have HK : IntegralMixedRelativeCuts.choiceIndex rule kind≤2^(P).width (pairFst q) :=
    (kind_choice G old).symm.trans_le ((IntegralMixedRawKindBits.choice_le G old).trans HN)
  have HD : (G).degree old≤2^(P).width (pairFst q) := ((G).degree_bound old).trans HN
  have HC : choice (pair q w)=IntegralMixedRelativeCuts.choiceIndex rule kind := by
    unfold choice
    simp only [pairFst_pair]
    unfold IntegralFramedTraceCutGuards.choice
    rw [guard_parent]
    exact kind_choice G old
  have HDe : (degree∘pairFst) (pair q w)=(G).degree old := by
    simpa only [Function.comp_apply,pairFst_pair] using degree_eq q
  have HCap : cap (pair q w)=2^(P).width (pairFst q) := by simp only [cap,pairFst_pair]
  have HE := IntegralMixedRelativeCuts.native_guards_iff x bound rule φ kind ((G).degree old)
    (2^(P).width (pairFst q)) HN HK HD sign head choice (degree∘pairFst) cap (pair q w) HC HDe HCap
    (interval_evaluation_at q w hw hb φ hφ)
  have HH : head (pair q w)≠InfinitesimalSign.encode 0 := by
    change InfinitesimalSign.encode (1 : SignType)≠InfinitesimalSign.encode 0
    decide
  constructor
  · intro hg
    exact (HE.mp hg).1
  · intro hc
    exact HE.mpr ⟨hc,Or.inl HH⟩

theorem interpreted_coefficients (hb : Bounds (pair q w)) (hg : Guards (pair q w)) :
    ∃φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,IntervalGenerators q w hw φ ∧
      IntegralMixedRelativeCuts.CoefficientGuards x bound rule φ kind ((G).degree old) := by
  obtain ⟨φ,hφ,_⟩ := interval_coefficient_evaluation q w hw hb
  exact ⟨φ,hφ,(interval_guards_iff_coefficients q w hw hb φ hφ).mp hg⟩

end LeanCanny.Encoding.FormulaSignSlotRadialProviderCutInterval
