/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomicPoint
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRecordPrelude
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderMarkedParameters
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderMarkedGeometry
public import LeanCanny.Geometry.BoundedMarkedParameterSemantics
public import LeanCanny.Geometry.BoundedMarkedCoordinates
/-! # The native marked tests constrain the actual provider prelude fields -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomic.MarkedPrelude
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR LeanCanny.Connectivity
open FormulaSignSlotRadialProviderAtomic
open FormulaSignSlotRadialExternalPrelude (number original radius)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "T" => FormulaSignSlotRadialProviderRecordPlan.tables
local notation "n" => CanonicalAuxiliaryCandidateCover.dimension
local notation "t" => CanonicalAuxiliaryCandidateCover.equation

theorem source_packet_at (Q : IntegerPolynomialRootQueriesBits.Source) (c : List Bool) (i : ℕ) :
    (IntegralFramedPhysicalLeafSources.source Q).polynomial (pair c (BinaryNatCode.encode i))=
      Q.polynomial (pair (pairFst c) (BinaryNatCode.encode i)) := by
  simp only [IntegralFramedPhysicalLeafSources.source,IntegerPolynomialSourceChoice.reindex,
    Function.comp_apply,IntegralFramedPhysicalLeafSources.query,pairFst_pair,pairSnd_pair]

private theorem leaves_env (b : IntegralFramedBankQuery.Bank) (tab : IntegralMixedHeaderTablesBits.Tables)
    (hr : IntegralMixedFramedHeaderBits.Represents b.parameters b.plan b.data tab)
    (Q : IntegerPolynomialRootQueriesBits.Source) (N : List Bool→ℕ) (c w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input b) c w)
    (hl : pair c w∈IntegralFramedPhysicalIntegerLeaves.language b.parameters b.plan b.data
      b.nodes b.factor b.seed b.bounds b.key b.positive (IntegralFramedPhysicalLeafSources.source Q) N) :
    ∀i<N c,(Q.polynomial (pair (pairFst c) (BinaryNatCode.encode i))).eval₂ (Int.castRingHom ℝ)
      (IntegralFramedPhysicalBankTerm.env b tab hr c w hw i)=0 := by
  have hc : N c≤(IntegralMixedFramedHistoryFamilyBits.family b.parameters b.plan b.data).birth (b.key c) := by
    simpa only [pairFst_pair] using hl.2.1
  have hh := (IntegralFramedPhysicalIntegerLeaves.holds_iff b.parameters b.plan b.data b.nodes b.factor b.seed
    b.bounds b.key b.positive (IntegralFramedPhysicalLeafSources.source Q) N c w hw).mp
    (by simpa only [pairFst_pair,pairSnd_pair] using hl.2.2)
  intro i hi
  have h := hh i hi
  rw [source_packet_at] at h
  rw [←IntegralFramedPhysicalBankTerm.env_coordinate b tab hr c w hw i (hi.trans_le hc)] at h
  exact h

noncomputable def marked_of_equations {m : ℕ} (Q : MvPolynomial (Fin m) ℤ) (D H R : ℕ)
    (x : Fin (m+4)→ℝ)
    (hs : (BoundedRegularSource.polynomial Q D H R).eval₂ (Int.castRingHom ℝ) x=0)
    (hm : (BoundedRegularSource.markPolynomial Q R).eval₂ (Int.castRingHom ℝ) x=0) :
    BoundedRegularSource.Marked Q D H R := ⟨⟨x,hs⟩,hm⟩

private theorem marked_of_equations_values {m : ℕ} (Q : MvPolynomial (Fin m) ℤ) (D H R : ℕ)
    (x : Fin (m+4)→ℝ)
    (hs : (BoundedRegularSource.polynomial Q D H R).eval₂ (Int.castRingHom ℝ) x=0)
    (hm : (BoundedRegularSource.markPolynomial Q R).eval₂ (Int.castRingHom ℝ) x=0) :
    (marked_of_equations Q D H R x hs hm).val.val=x := rfl

private theorem marked_of_equations_projection {m : ℕ} (Q : MvPolynomial (Fin m) ℤ) (D H R : ℕ)
    (x : Fin (m+4)→ℝ)
    (hs : (BoundedRegularSource.polynomial Q D H R).eval₂ (Int.castRingHom ℝ) x=0)
    (hm : (BoundedRegularSource.markPolynomial Q R).eval₂ (Int.castRingHom ℝ) x=0) (i : Fin m) :
    (BoundedRegularSource.markedProjection Q D H R (marked_of_equations Q D H R x hs hm)).val i=x (i.castAdd 4) := by
  rw [BoundedRegularSource.markedProjection_apply,marked_of_equations_values]

attribute [local irreducible] FormulaSignSlotRadialProviderIntegerSource.source
  FormulaSignSlotRadialProviderRecordPlan.source CanonicalAuxiliaryCandidateCover.equation Term.finitePolynomial
  CanonicalAuxiliaryCandidateCover.dimension

theorem source_roots (q : List Bool) (hv : Valid q) :
    ∀i<number (provider q)+8,(FormulaSignSlotRadialProviderIntegerPlan.source.polynomial
      (pair (provider q) (BinaryNatCode.encode i))).eval₂ (Int.castRingHom ℝ) (field q hv i)=0 := by
  have HL := (valid_marked q hv).1
  have HR := leaves_env B T bank_represents FormulaSignSlotRadialProviderRecordPlan.source Marked.leafCount
    (context q) (word q) (full_valid q hv) HL
  have HN : Marked.leafCount (context q)=number (provider q)+8 := by
    simp only [Marked.leafCount,context,pairFst_pair,FormulaSignSlotRadialProviderRecordPlan.count,
      root_provider,FormulaSignSlotRadialProviderIntegerPlan.count]
  intro i hi
  have HE := HR i (by rw [HN]; exact hi)
  have HC : pairFst (context q)=root q := pairFst_pair _ _
  rw [HC,FormulaSignSlotRadialProviderRecordPlan.source_polynomial_packet,root_provider] at HE
  simpa only [field,bankField] using HE

theorem mark_syntax (q : List Bool) :
    (IntegralMixedFramedBankTermBits.source Marked.markWord).syntax ((B).key (context q))=
      BoundedMarkedParameterTerm.mark (t (FormulaSignSlotRadialExternalPrelude.original (provider q))) (number (provider q)) := by
  change TermView.term (Marked.markWord (pairFst ((B).key (context q))))=_
  rw [context_root]
  change TermView.term (IntegralMixedMarkedPointTest.markWord n t
    (FormulaSignSlotRadialProviderRecordPlan.providerContext (root q)))=_
  rw [root_provider]
  unfold IntegralMixedMarkedPointTest.markWord
  rw [TermView.term_toBits]
  rfl

theorem regular_syntax (q : List Bool) :
    (IntegralMixedFramedBankTermBits.source Marked.regularWord).syntax ((B).key (context q))=
      BoundedMarkedParameterTerm.regular (t (FormulaSignSlotRadialExternalPrelude.original (provider q))) (number (provider q))
        (BoundedZeroSource.powerDegree (t (FormulaSignSlotRadialExternalPrelude.original (provider q))).toData.size) := by
  change TermView.term (Marked.regularWord (pairFst ((B).key (context q))))=_
  rw [context_root]
  change TermView.term (IntegralMixedMarkedPointTest.regularWord n t
    (FormulaSignSlotRadialProviderRecordPlan.providerContext (root q)))=_
  rw [root_provider]
  unfold IntegralMixedMarkedPointTest.regularWord IntegralMixedMarkedPointTest.degree IntegralMixedMarkedPointTest.charge
  rw [TermView.term_toBits]
  rfl

private theorem field_env (q : List Bool) (hv : Valid q) : field q hv=
    IntegralFramedPhysicalBankTerm.env B T bank_represents (context q) (word q) (full_valid q hv) := rfl

theorem mark_packet (q : List Bool) (hv : Valid q) : Marked.markValue q=InfinitesimalSign.encode
    (SignType.sign ((BoundedMarkedParameterTerm.mark (t (FormulaSignSlotRadialExternalPrelude.original (provider q))) (number (provider q))).eval (field q hv))) := by
  rw [field_env]
  have H := IntegralFramedPhysicalBankTerm.packet B T bank_represents (context q) (word q) (full_valid q hv) Marked.markWord []
  rw [mark_syntax] at H
  simpa only [Marked.markValue,Function.comp_apply,Marked.probe,sampleQuery,field,bankField] using H

theorem regular_packet (q : List Bool) (hv : Valid q) : Marked.regularValue q=InfinitesimalSign.encode
    (SignType.sign ((BoundedMarkedParameterTerm.regular (t (FormulaSignSlotRadialExternalPrelude.original (provider q))) (number (provider q))
      (BoundedZeroSource.powerDegree (t (FormulaSignSlotRadialExternalPrelude.original (provider q))).toData.size)).eval (field q hv))) := by
  rw [field_env]
  have H := IntegralFramedPhysicalBankTerm.packet B T bank_represents (context q) (word q) (full_valid q hv) Marked.regularWord []
  rw [regular_syntax] at H
  simpa only [Marked.regularValue,Function.comp_apply,Marked.probe,sampleQuery,field,bankField] using H

noncomputable def preludePoint (q : List Bool) (hv : Valid q) : Fin (number (provider q)+4)→ℝ :=
  fun i=>field q hv i.val

theorem equations (q : List Bool) (hv : Valid q) :
    (BoundedRegularSource.polynomial (FormulaSignSlotRadialProviderMarkedGeometry.equation (provider q))
      (FormulaSignSlotRadialProviderMarkedGeometry.allowance (provider q))
      (FormulaSignSlotRadialProviderMarkedGeometry.allowance (provider q)) (radius (provider q))).eval₂
        (Int.castRingHom ℝ) (preludePoint q hv)=0 ∧
    (BoundedRegularSource.markPolynomial (FormulaSignSlotRadialProviderMarkedGeometry.equation (provider q))
      (radius (provider q))).eval₂ (Int.castRingHom ℝ) (preludePoint q hv)=0 := by
  obtain ⟨hRad,hL,hB,hK⟩ := FormulaSignSlotRadialProviderMarkedParameters.parameters (provider q) (field q hv) (source_roots q hv)
  have HT := CanonicalAuxiliaryCandidateCover.equation_scope (FormulaSignSlotRadialExternalPrelude.original (provider q))
  have HR := BoundedMarkedParameterSemantics.regular_eval
    (t (FormulaSignSlotRadialExternalPrelude.original (provider q))) (number (provider q))
    (t (FormulaSignSlotRadialExternalPrelude.original (provider q))).toData.size (radius (provider q)) HT
    (field q hv) hRad hL hB hK
  have HM := BoundedMarkedParameterSemantics.mark_eval
    (t (FormulaSignSlotRadialExternalPrelude.original (provider q))) (number (provider q))
    (radius (provider q)) HT (field q hv) hRad
  have HZR := (valid_marked q hv).2.1
  rw [regular_packet q hv,SquareSampleTestSign.encode_eq_iff,sign_eq_zero_iff] at HZR
  have HZM := (valid_marked q hv).2.2
  rw [mark_packet q hv,SquareSampleTestSign.encode_eq_iff,sign_eq_zero_iff] at HZM
  exact ⟨HR.symm.trans HZR,HM.symm.trans HZM⟩

attribute [local irreducible] BoundedRegularSource.polynomial BoundedRegularSource.markPolynomial

noncomputable def markedPoint (q : List Bool) (hv : Valid q) :
    BoundedRegularSource.Marked (FormulaSignSlotRadialProviderMarkedGeometry.equation (provider q))
      (FormulaSignSlotRadialProviderMarkedGeometry.allowance (provider q))
      (FormulaSignSlotRadialProviderMarkedGeometry.allowance (provider q)) (radius (provider q)) :=
  marked_of_equations (m:=number (provider q)) _ _ _ _ (preludePoint q hv)
    (equations q hv).1 (equations q hv).2

theorem markedPoint_coordinate (q : List Bool) (hv : Valid q) (i : Fin (number (provider q)+4)) :
    (markedPoint q hv).val.val i=field q hv i.val := by
  have H := marked_of_equations_values (m:=number (provider q)) _ _ _ _ (preludePoint q hv)
    (equations q hv).1 (equations q hv).2
  exact congrFun H i

theorem projection_coordinate (q : List Bool) (hv : Valid q) (i : Fin (number (provider q))) :
    (BoundedRegularSource.markedProjection _ _ _ _ (markedPoint q hv)).val i=field q hv i.val := by
  exact marked_of_equations_projection (m:=number (provider q)) _ _ _ _ (preludePoint q hv)
    (equations q hv).1 (equations q hv).2 i

end LeanCanny.Encoding.FormulaSignSlotRadialProviderAtomic.MarkedPrelude
