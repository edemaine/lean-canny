/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordFieldRadius
/-! # Default Field query coefficients ignore both sampled words -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordFieldContext
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

attribute [local irreducible] CoefficientMarkedRecordRows.symbolic
  CoefficientMarkedRecordBankSource.polynomial CoefficientMarkedRecordBankProducts.cofactor
  CoefficientMarkedRecordBankProducts.common

private def address (z : List Bool) : (ctx : List Bool) × Fin (IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n ctx) :=
  ⟨CoefficientMarkedRecordFieldSource.root z, CoefficientMarkedRecordFieldSource.selected (n := n) z⟩

private theorem address_eq (z w : List Bool)
    (hc : CoefficientMarkedRecordFieldSource.root z = CoefficientMarkedRecordFieldSource.root w)
    (hi : (CoefficientMarkedRecordFieldSource.selected (n := n) z).val =
      (CoefficientMarkedRecordFieldSource.selected (n := n) w).val) : address (n := n) z = address (n := n) w := by
  unfold address
  apply Sigma.ext hc
  exact (Fin.heq_ext_iff (congrArg (IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n) hc)).mpr hi

private noncomputable def sourceAt (a : (ctx : List Bool) × Fin (IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n ctx)) :=
  CoefficientMarkedRecordBankSource.polynomial hn ht ha a.1 a.2

private theorem source_packet_words (cL cR wL wR vL vR : List Bool) (a b : ℕ) :
    CoefficientMarkedRecordFieldSource.polynomial hn ht ha (IntegralMixedPhysicalFieldEquality.packet cL wL cR wR a b) =
      CoefficientMarkedRecordFieldSource.polynomial hn ht ha (IntegralMixedPhysicalFieldEquality.packet cL vL cR vR a b) := by
  have hc : CoefficientMarkedRecordFieldSource.root (IntegralMixedPhysicalFieldEquality.packet cL wL cR wR a b) =
      CoefficientMarkedRecordFieldSource.root (IntegralMixedPhysicalFieldEquality.packet cL vL cR vR a b) := by
    simp only [CoefficientMarkedRecordFieldSource.root, IntegralMixedPhysicalFieldEquality.context,
      IntegralMixedPhysicalFieldEquality.sample, IntegralMixedPhysicalFieldEquality.packet,
      Bool.false_eq_true, ite_false, pairFst_pair, pairSnd_pair]
  have hi : (CoefficientMarkedRecordFieldSource.selected (n := n) (IntegralMixedPhysicalFieldEquality.packet cL wL cR wR a b)).val =
      (CoefficientMarkedRecordFieldSource.selected (n := n) (IntegralMixedPhysicalFieldEquality.packet cL vL cR vR a b)).val := by
    simp only [CoefficientMarkedRecordFieldSource.selected, IntegralMixedPhysicalFieldEquality.catalogSelected,
      IntegralMixedPhysicalFieldEquality.catalogCount, IntegralMixedPhysicalFieldEquality.context,
      IntegralMixedPhysicalFieldEquality.sample, IntegralMixedPhysicalFieldEquality.label,
      IntegralMixedPhysicalFieldEquality.labelWord, IntegralMixedPhysicalFieldEquality.packet,
      Bool.false_eq_true, ite_false, pairFst_pair, pairSnd_pair]
  exact congrArg (sourceAt hn ht ha) (address_eq _ _ hc hi)

/-- The actual default Field polynomial retains contexts and chronological
labels while erasing OWN word choices, without any ordinal invariance premise. -/
theorem polynomial_packet_words (right : Bool) (cL cR wL wR vL vR : List Bool) (a b k : ℕ) :
    CoefficientMarkedRecordFieldQuery.physical hn ht ha right
      (IntegralMixedPhysicalFieldEquality.packet cL wL cR wR a b) k =
    CoefficientMarkedRecordFieldQuery.physical hn ht ha right
      (IntegralMixedPhysicalFieldEquality.packet cL vL cR vR a b) k := by
  have hs := source_packet_words hn ht ha cL cR wL wR vL vR a b
  unfold CoefficientMarkedRecordFieldQuery.physical CoefficientMarkedRecordFieldQuery.polynomial
    CoefficientMarkedRecordFieldQuery.column CoefficientMarkedRecordFieldQuery.rightRoot
    CoefficientMarkedRecordFieldSource.root IntegralMixedPhysicalFieldEquality.catalogPower
    IntegralMixedPhysicalFieldEquality.catalogSelected
  rw [hs]
  cases right <;> simp only [IntegralMixedPhysicalFieldEquality.catalogCount,
    IntegralMixedPhysicalFieldEquality.context, IntegralMixedPhysicalFieldEquality.sample,
    IntegralMixedPhysicalFieldEquality.label, IntegralMixedPhysicalFieldEquality.labelWord,
    IntegralMixedPhysicalFieldEquality.packet, Bool.false_eq_true, ite_false, ite_true,
    pairFst_pair, pairSnd_pair]

end LeanCanny.Encoding.CoefficientMarkedRecordFieldContext
