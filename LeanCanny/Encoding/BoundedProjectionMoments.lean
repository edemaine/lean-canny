/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedProjectionDerivativeSigns
public import LeanCanny.Algebra.SparseSignSpanning
public import LeanCanny.Algebra.SignQueryMoments

/-! # Sparse moments of the actual projection-root signatures

Sparse derivative-sign monomials span every rational-valued function on the distinct
real projection roots, with support bounded by the existing polynomial label
width. Product Tarski queries compute their moments in native polynomial space.
`BoundedProjectionRankBasis` selects a basis, and
`BoundedProjectionSignatureRead` enumerates individual signatures with native
access to each derivative sign.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedProjectionMoments
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open scoped Classical
attribute [local irreducible] BoundedCriticalProjection.polynomial

abbrev Root (P : Readers) (c : List Bool) := {x // x ∈ BoundedCriticalLabels.rootSet P c}
abbrev Feature (P : Readers) (c : List Bool) := Fin (BoundedProjectionRootCount.degree P c + 1)

noncomputable def signature (P : Readers) (c : List Bool) (x : Root P c) : Feature P c → SignType :=
  ThomEncoding.signature ((BoundedCriticalProjection.polynomial P c).map (Int.castRingHom ℝ))
    (BoundedProjectionRootCount.degree P c) x.val

theorem signature_injective (P : Readers) (c : List Bool) : Function.Injective (signature P c) := by
  intro a b he
  apply Subtype.ext
  apply ThomEncoding.root_eq ((BoundedCriticalProjection.polynomial P c).map (Int.castRingHom ℝ))
    (BoundedCriticalLabels.mapped_ne_zero P c) (BoundedProjectionRootCount.degree P c)
    (Polynomial.natDegree_map_le.trans (BoundedCriticalProjection.polynomial_degree P c))
  · exact (Polynomial.mem_roots (BoundedCriticalLabels.mapped_ne_zero P c)).mp
      (Multiset.mem_toFinset.mp a.property)
  · exact (Polynomial.mem_roots (BoundedCriticalLabels.mapped_ne_zero P c)).mp
      (Multiset.mem_toFinset.mp b.property)
  · intro k hk
    exact congrFun he ⟨k, by omega⟩

noncomputable def vector (P : Readers) (c : List Bool) (d : Feature P c →₀ ℕ) : Root P c → ℚ :=
  MonomialEvaluationBasis.vector (MvPolynomial.aeval (R := ℚ) (fun i x => (signature P c x i : ℚ))) d

theorem sparse_span (P : Readers) (c : List Bool) :
    Submodule.span ℚ (vector P c '' {d | d.support.card ≤ BoundedCriticalProjection.labelWidth P c ∧
      ∀ i, d i ≤ 2}) = ⊤ := by
  apply SparseSignSpanning.signatures_span (MonomialOrder.degLex (σ := Feature P c))
    (signature P c) (signature_injective P c) (BoundedCriticalProjection.labelWidth P c)
  simpa only [Fintype.card_coe] using BoundedCriticalLabels.rootSet_card_le P c

noncomputable def family (P : Readers) (features : List Bool → ℕ) (orders : List Bool → List Bool) :
    SignPatternBits.Family := BoundedProjectionDerivativeSigns.family P features orders (fun _ _ => 0)

/-- Input `pair context ternaryExponents`; the order reader is queried on
`pair context featureIndex`. Only the selected features, not the full signature,
are supplied to the product query. -/
noncomputable def moment (P : Readers) (features : List Bool → ℕ) (orders : List Bool → List Bool)
    (q : List Bool) : ℤ := (SignPatternBits.queryFamily (family P features orders)).value q

theorem moment_eq_sum (P : Readers) (features : List Bool → ℕ) (orders : List Bool → List Bool)
    (q : List Bool) :
    moment P features orders q = ∑ x ∈ BoundedCriticalLabels.rootSet P (pairFst q),
      ∏ i ∈ Finset.range (features (pairFst q)),
        (SignType.sign (((BoundedProjectionThom.polynomial P (pairFst q)
          (Nat.fromBitsLE (orders (pair (pairFst q) (BinaryNatCode.encode i))))).map (Int.castRingHom ℝ)).eval x) : ℤ) ^
            (Ternary.exponent (features (pairFst q)) (Nat.fromBitsLE (pairSnd q)) i).val := by
  rw [moment, SignQueryBits.Family.value_eq_sum]
  simp only [SignPatternBits.queryFamily, family, BoundedProjectionDerivativeSigns.family,
    Function.comp_apply, BinaryNatCode.encode, Nat.fromBitsLE_bits, BoundedCriticalLabels.rootSet, algebraMap_int_eq]

attribute [local irreducible] BoundedProjectionThom.value BoundedProjectionRootCount.coefficient
  BoundedProjectionDerivativeSigns.query

theorem evaluator {P : Readers} {features : List Bool → ℕ} {orders : List Bool → List Bool}
    (h : P.PolyTime) (hc : UnaryFn features) (ho : orders ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun q => SignStatisticBits.integerCode (moment P features orders q)) := by
  let a := BoundedProjectionDerivativeSigns.access P features orders (fun _ _ => 0) (fun _ => []) (fun _ _ => rfl)
  have H := BoundedProjectionRootCount.coefficient_evaluator h ha
  have Q := (BoundedProjectionThom.evaluator h ha).precompose _ (BoundedProjectionDerivativeSigns.query_FP ho)
  have E := SignPatternBits.queryEvaluator a
    (BoundedProjectionDerivativeSigns.family_polyTime h hc orders (fun _ _ => 0)) H Q
  exact E

end LeanCanny.Encoding.BoundedProjectionMoments
