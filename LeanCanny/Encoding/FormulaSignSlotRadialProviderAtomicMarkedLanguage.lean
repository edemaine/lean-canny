/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicMarkedPrelude
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderFieldEqualitySemantics
/-! # Constructing marked guards from an actual complete own tuple -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomic.MarkedLanguage
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR LeanCanny.Connectivity
open FormulaSignSlotRadialProviderAtomic
open FormulaSignSlotRadialExternalPrelude (number radius)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "T" => FormulaSignSlotRadialProviderRecordPlan.tables
local notation "t" => CanonicalAuxiliaryCandidateCover.equation

noncomputable def values (q : List Bool) (hw : FullValid q) : ℕ→ℝ :=
  IntegralFramedPhysicalBankTerm.env B T bank_represents (context q) (word q) hw

private theorem leaves_from_env (b : IntegralFramedBankQuery.Bank) (tab : IntegralMixedHeaderTablesBits.Tables)
    (hr : IntegralMixedFramedHeaderBits.Represents b.parameters b.plan b.data tab)
    (Q : IntegerPolynomialRootQueriesBits.Source) (N : List Bool→ℕ) (c w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input b) c w)
    (hc : N c≤(IntegralMixedFramedHistoryFamilyBits.family b.parameters b.plan b.data).birth (b.key c))
    (hroots : ∀i<N c,(Q.polynomial (pair (pairFst c) (BinaryNatCode.encode i))).eval₂ (Int.castRingHom ℝ)
      (IntegralFramedPhysicalBankTerm.env b tab hr c w hw i)=0) :
    pair c w∈IntegralFramedPhysicalIntegerLeaves.language b.parameters b.plan b.data
      b.nodes b.factor b.seed b.bounds b.key b.positive (IntegralFramedPhysicalLeafSources.source Q) N := by
  simp only [IntegralFramedPhysicalIntegerLeaves.language,Set.mem_ofPred_eq,pairFst_pair,pairSnd_pair]
  refine ⟨hw,hc,?_⟩
  apply (IntegralFramedPhysicalIntegerLeaves.holds_iff b.parameters b.plan b.data b.nodes b.factor b.seed
    b.bounds b.key b.positive (IntegralFramedPhysicalLeafSources.source Q) N c w hw).mpr
  intro i hi
  rw [MarkedPrelude.source_packet_at,←IntegralFramedPhysicalBankTerm.env_coordinate b tab hr c w hw i (hi.trans_le hc)]
  exact hroots i hi

attribute [local irreducible] FormulaSignSlotRadialProviderIntegerSource.source
  FormulaSignSlotRadialProviderRecordPlan.source CanonicalAuxiliaryCandidateCover.equation
  CanonicalAuxiliaryCandidateCover.dimension Term.finitePolynomial

private theorem leaf_count_number (q : List Bool) : Marked.leafCount (context q)=number (provider q)+8 := by
  simp only [Marked.leafCount,context,pairFst_pair,FormulaSignSlotRadialProviderRecordPlan.count,
    root_provider,FormulaSignSlotRadialProviderIntegerPlan.count]

theorem leaves_of_roots (q : List Bool) (hw : FullValid q)
    (hroots : ∀i<number (provider q)+8,(FormulaSignSlotRadialProviderIntegerPlan.source.polynomial
      (pair (provider q) (BinaryNatCode.encode i))).eval₂ (Int.castRingHom ℝ) (values q hw i)=0) :
    sampleQuery q∈Marked.leafLanguage := by
  have HC : Marked.leafCount (context q)≤FormulaSignSlotRadialProviderFieldEquality.count (context q) := by
    rw [FormulaSignSlotRadialProviderFieldEquality.count_eq]
    simp only [Marked.leafCount,context,pairFst_pair,FormulaSignSlotRadialProviderRecordPlan.fullCount]
    exact Nat.le_add_right _ _
  apply leaves_from_env B T bank_represents FormulaSignSlotRadialProviderRecordPlan.source Marked.leafCount
    (context q) (word q) hw HC
  intro i hi
  have H := hroots i (by rw [leaf_count_number] at hi; exact hi)
  have HK : pairFst (context q)=root q := pairFst_pair _ _
  rw [HK,FormulaSignSlotRadialProviderRecordPlan.source_polynomial_packet,root_provider]
  exact H

theorem mark_packet (q : List Bool) (hw : FullValid q) : Marked.markValue q=InfinitesimalSign.encode
    (SignType.sign ((BoundedMarkedParameterTerm.mark (t (FormulaSignSlotRadialExternalPrelude.original (provider q)))
      (number (provider q))).eval (values q hw))) := by
  have H := IntegralFramedPhysicalBankTerm.packet B T bank_represents (context q) (word q) hw Marked.markWord []
  rw [MarkedPrelude.mark_syntax] at H
  simpa only [Marked.markValue,Function.comp_apply,Marked.probe,sampleQuery,values] using H

theorem regular_packet (q : List Bool) (hw : FullValid q) : Marked.regularValue q=InfinitesimalSign.encode
    (SignType.sign ((BoundedMarkedParameterTerm.regular (t (FormulaSignSlotRadialExternalPrelude.original (provider q)))
      (number (provider q)) (BoundedZeroSource.powerDegree
        (t (FormulaSignSlotRadialExternalPrelude.original (provider q))).toData.size)).eval (values q hw))) := by
  have H := IntegralFramedPhysicalBankTerm.packet B T bank_represents (context q) (word q) hw Marked.regularWord []
  rw [MarkedPrelude.regular_syntax] at H
  simpa only [Marked.regularValue,Function.comp_apply,Marked.probe,sampleQuery,values] using H

theorem holds_of_equations (q : List Bool) (hw : FullValid q)
    (hroots : ∀i<number (provider q)+8,(FormulaSignSlotRadialProviderIntegerPlan.source.polynomial
      (pair (provider q) (BinaryNatCode.encode i))).eval₂ (Int.castRingHom ℝ) (values q hw i)=0)
    (hr : (BoundedRegularSource.polynomial (FormulaSignSlotRadialProviderMarkedGeometry.equation (provider q))
      (FormulaSignSlotRadialProviderMarkedGeometry.allowance (provider q))
      (FormulaSignSlotRadialProviderMarkedGeometry.allowance (provider q)) (radius (provider q))).eval₂
        (Int.castRingHom ℝ) (fun i=>values q hw i.val)=0)
    (hm : (BoundedRegularSource.markPolynomial (FormulaSignSlotRadialProviderMarkedGeometry.equation (provider q))
      (radius (provider q))).eval₂ (Int.castRingHom ℝ) (fun i=>values q hw i.val)=0) : Marked.Holds q := by
  obtain ⟨hRad,hL,hB,hK⟩ := FormulaSignSlotRadialProviderMarkedParameters.parameters (provider q) (values q hw) hroots
  have HT := CanonicalAuxiliaryCandidateCover.equation_scope (FormulaSignSlotRadialExternalPrelude.original (provider q))
  have HR := BoundedMarkedParameterSemantics.regular_eval
    (t (FormulaSignSlotRadialExternalPrelude.original (provider q))) (number (provider q))
    (t (FormulaSignSlotRadialExternalPrelude.original (provider q))).toData.size (radius (provider q)) HT
    (values q hw) hRad hL hB hK
  have HM := BoundedMarkedParameterSemantics.mark_eval
    (t (FormulaSignSlotRadialExternalPrelude.original (provider q))) (number (provider q))
    (radius (provider q)) HT (values q hw) hRad
  refine ⟨leaves_of_roots q hw hroots,?_,?_⟩
  · have HZ := HR.trans hr
    rw [regular_packet q hw,HZ]
    simp only [sign_zero]
  · have HZ := HM.trans hm
    rw [mark_packet q hw,HZ]
    simp only [sign_zero]

end LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomic.MarkedLanguage
