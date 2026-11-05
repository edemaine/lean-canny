/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderIntegerPlan
public import LeanCanny.Encoding.IntegralMixedPhysicalMarkedParameters
/-! # Actual provider leaf roots determine all four marked parameters -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderMarkedParameters
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR LeanCanny.Connectivity
open FormulaSignSlotRadialExternalPrelude (number original radius)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "n" => CanonicalAuxiliaryCandidateCover.dimension
local notation "t" => CanonicalAuxiliaryCandidateCover.equation
local notation "hn" => CanonicalAuxiliaryCandidateCover.dimension_unary
local notation "ht" => CanonicalAuxiliaryCandidateCover.equation_FP
local notation "ha" => CanonicalAuxiliaryCandidateCover.equation_scope
local notation "S" => FormulaSignSlotRadialProviderIntegerSource.source

noncomputable def Powers (c : List Bool) (v : ℕ→ℝ) : Prop :=
  v (number c+4)=(2:ℝ)^radius c ∧
  v (number c+5)=(2:ℝ)^BoundedRegularSource.regularizationExponent
    (number c) (t (original c)).toData.size (t (original c)).toData.size (radius c) ∧
  v (number c+6)=(2:ℝ)^BoundedZeroSource.perturbationExponent
    (number c) (t (original c)).toData.size (t (original c)).toData.size (radius c) ∧
  v (number c+7)=(2:ℝ)^BoundedZeroSource.penaltyExponent
    (number c) (t (original c)).toData.size (radius c)

private theorem tag_packet (c : List Bool) (i : ℕ) :
    FormulaSignSlotRadialProviderIntegerSource.tag (pair c (BinaryNatCode.encode i))=i := by
  simp only [FormulaSignSlotRadialProviderIntegerSource.tag,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits]
private theorem power_root (E : List Bool→ℕ) (q : List Bool) (v : ℝ)
    (h : ((FormulaSignSlotRadialProviderIntegerSource.power E).polynomial q).eval₂ (Int.castRingHom ℝ) v=0) :
    v=(2:ℝ)^E q := (IntegralFramedPhysicalLeafSources.positive_power_root _ _).mp h

attribute [local irreducible] FormulaSignSlotRadialProviderIntegerSource.source
  FormulaSignSlotRadialProviderIntegerSource.externalSource FormulaSignSlotRadialExternalCoordinates.source

theorem parameters (c : List Bool) (v : ℕ→ℝ)
    (h : ∀i<number c+8,((S).polynomial (pair c (BinaryNatCode.encode i))).eval₂ (Int.castRingHom ℝ) (v i)=0) :
    Powers c v := by
  unfold Powers
  by_cases he : FormulaSignSlotRadialExternalContext.external c
  · have E4 := h (number c+4) (by omega)
    have E5 := h (number c+5) (by omega)
    have E6 := h (number c+6) (by omega)
    have E7 := h (number c+7) (by omega)
    have HX (i : ℕ) : FormulaSignSlotRadialExternalContext.external (pairFst (pair c (BinaryNatCode.encode i))) := by
      simpa only [pairFst_pair] using he
    rw [FormulaSignSlotRadialProviderIntegerSource.polynomial_external _ (HX _),
      FormulaSignSlotRadialProviderIntegerSource.external_radius _ (by rw [tag_packet,pairFst_pair])] at E4
    rw [FormulaSignSlotRadialProviderIntegerSource.polynomial_external _ (HX _),
      FormulaSignSlotRadialProviderIntegerSource.external_lam _ (by rw [tag_packet,pairFst_pair])] at E5
    rw [FormulaSignSlotRadialProviderIntegerSource.polynomial_external _ (HX _),
      FormulaSignSlotRadialProviderIntegerSource.external_beta _ (by rw [tag_packet,pairFst_pair])] at E6
    rw [FormulaSignSlotRadialProviderIntegerSource.polynomial_external _ (HX _),
      FormulaSignSlotRadialProviderIntegerSource.external_kappa _ (by rw [tag_packet,pairFst_pair])] at E7
    refine ⟨?_,?_,?_,?_⟩
    · simpa only [Function.comp_apply,pairFst_pair] using power_root _ _ _ E4
    · simpa only [Function.comp_apply,FormulaSignSlotRadialProviderIntegerSource.saved,pairFst_pair,
        FormulaSignSlotRadialExternalSlackSource.Lam,FormulaSignSlotRadialExternalSlackSource.N,
        FormulaSignSlotRadialExternalSlackSource.charge,FormulaSignSlotRadialExternalSlackSource.R,
        FormulaSignSlotRadialExternalSlackSource.key_root,AuxiliaryCandidateRegularLift.allowance] using power_root _ _ _ E5
    · simpa only [Function.comp_apply,FormulaSignSlotRadialProviderIntegerSource.saved,pairFst_pair,
        FormulaSignSlotRadialExternalSlackSource.beta,FormulaSignSlotRadialExternalSlackSource.N,
        FormulaSignSlotRadialExternalSlackSource.charge,FormulaSignSlotRadialExternalSlackSource.R,
        FormulaSignSlotRadialExternalSlackSource.key_root,AuxiliaryCandidateRegularLift.allowance] using power_root _ _ _ E6
    · simpa only [Function.comp_apply,FormulaSignSlotRadialProviderIntegerSource.saved,pairFst_pair,
        FormulaSignSlotRadialExternalSlackSource.K,FormulaSignSlotRadialExternalSlackSource.N,
        FormulaSignSlotRadialExternalSlackSource.charge,FormulaSignSlotRadialExternalSlackSource.R,
        FormulaSignSlotRadialExternalSlackSource.key_root,AuxiliaryCandidateRegularLift.allowance] using power_root _ _ _ E7
  · have HM : ∀i<IntegralMixedAuxiliaryMarkedIntegerSource.number n c+8,
        ((IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha radius).polynomial
          (pair c (BinaryNatCode.encode i))).eval₂ (Int.castRingHom ℝ) (v i)=0 := by
      intro i hi
      have HE := h i hi
      rw [FormulaSignSlotRadialProviderIntegerSource.polynomial_old (pair c (BinaryNatCode.encode i)) (by simpa only [pairFst_pair] using he)] at HE
      exact HE
    exact IntegralMixedPhysicalMarkedPlan.parameters hn ht ha radius false c v HM

end LeanCanny.Encoding.FormulaSignSlotRadialProviderMarkedParameters
