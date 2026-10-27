/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicFiberMomentSource

/-! # Native sparse derivative moments in algebraic fibers

The feature list is polynomially bounded, while every derivative index and
the head degree remain binary. Product coefficients, specialization signs,
and Tarski evaluation are computed from the original bivariate reader. The
result is the exact sum of the selected derivative-sign monomials over all
distinct fiber roots.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicFiberMoments
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedAlgebraicSlice
open scoped Classical BigOperators
attribute [local irreducible] BoundedProjectionRootCount.count BoundedProjectionOrderedRoot.root

noncomputable def productFamily (F : Family) (features : List Bool → ℕ) (orders : List Bool → List Bool) : Family :=
  ofIndexedProduct (BoundedAlgebraicFiberMomentSource.family F features orders)

noncomputable def moment (P : Readers) (F : Family) (features : List Bool → ℕ) (orders : List Bool → List Bool)
    (q : List Bool) : ℤ := RootSignQueries.tarskiQuery
  (specialized (P.comp pairFst) (F.comp pairFst) (signQuery q))
  (specialized (P.comp pairFst) (productFamily F features orders) (signQuery q))

noncomputable def value (P : Readers) (F : Family) (features : List Bool → ℕ) (orders : List Bool → List Bool)
    (q : List Bool) : List Bool := SignStatisticBits.integerCode (moment P F features orders q)

theorem evaluator {P : Readers} (h : P.PolyTime) {F : Family} (A : F.Access)
    {features : List Bool → ℕ} {orders : List Bool → List Bool} (hc : UnaryFn features) (ho : orders ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (value P F features orders) := by
  have E := (Tarski.evaluator (h.comp pairFst_mem_FP) (A.comp pairFst pairFst_mem_FP)
    (ofIndexedProductAccess (BoundedAlgebraicFiberMomentSource.access A features orders hc ho))
    (fun c => ha (pairFst c))).precompose signQuery signQuery_FP
  exact E.congr (funext fun q => by simp only [value, moment, Tarski.value, productFamily, Function.comp_apply])

theorem moment_packet (P : Readers) (F : Family) (features : List Bool → ℕ) (orders : List Bool → List Bool)
    (c : List Bool) (r : Fin (BoundedProjectionRootCount.count P c)) (record : List Bool) :
    moment P F features orders (pair (pair c (BinaryNatCode.encode r.val)) record) =
      RootSignQueries.tarskiQuery (F.slice c (BoundedProjectionOrderedRoot.root P c r).val)
        (RootSignQueries.queryPolynomial
          (fun i : Fin (features c) =>
            (Polynomial.derivative^[Nat.fromBitsLE (orders (pair c (BinaryNatCode.encode i.val)))])
              (F.slice c (BoundedProjectionOrderedRoot.root P c r).val))
          (fun i => Ternary.exponent (features c) (Nat.fromBitsLE record) i.val)) := by
  rw [moment, specialized_attach, specialized_attach, Family.slice_comp, pairFst_pair]
  unfold productFamily
  have H := BoundedAlgebraicFiberMomentSource.product_slice F features orders (pair c record)
    (BoundedProjectionOrderedRoot.root P c r).val
  rw [pairFst_pair, pairSnd_pair] at H
  exact congrArg (RootSignQueries.tarskiQuery (F.slice c (BoundedProjectionOrderedRoot.root P c r).val)) H

theorem moment_eq_sum (P : Readers) (F : Family) (features : List Bool → ℕ) (orders : List Bool → List Bool)
    (c : List Bool) (r : Fin (BoundedProjectionRootCount.count P c)) (record : List Bool) :
    moment P F features orders (pair (pair c (BinaryNatCode.encode r.val)) record) =
      ∑ x ∈ (F.slice c (BoundedProjectionOrderedRoot.root P c r).val).roots.toFinset,
        ∏ i : Fin (features c),
          (SignType.sign (((Polynomial.derivative^[Nat.fromBitsLE (orders (pair c (BinaryNatCode.encode i.val)))])
            (F.slice c (BoundedProjectionOrderedRoot.root P c r).val)).eval x) : ℤ) ^
              (Ternary.exponent (features c) (Nat.fromBitsLE record) i.val).val := by
  rw [moment_packet, RootSignQueries.tarskiQuery, RootSignQueries.signSum]
  apply Finset.sum_congr rfl
  intro x _
  exact RootSignQueries.sign_eval_queryPolynomial _ _ x

theorem moment_bound (P : Readers) (F : Family) (features : List Bool → ℕ) (orders : List Bool → List Bool)
    (q : List Bool) : (moment P F features orders q).natAbs ≤ F.degree (pairFst (pairFst q)) := by
  have hD : (specialized (P.comp pairFst) (F.comp pairFst) (signQuery q)).natDegree ≤
      F.degree (pairFst (pairFst q)) := by
    simpa only [Family.comp, signQuery, pairFst_pair] using
      specialized_degree (P.comp pairFst) (F.comp pairFst) (signQuery q)
  have H := RootSignQueries.tarskiQuery_bounds
    (specialized (P.comp pairFst) (F.comp pairFst) (signQuery q))
    (specialized (P.comp pairFst) (productFamily F features orders) (signQuery q))
  change -((specialized (P.comp pairFst) (F.comp pairFst) (signQuery q)).natDegree : ℤ) ≤ moment P F features orders q ∧
    moment P F features orders q ≤ ((specialized (P.comp pairFst) (F.comp pairFst) (signQuery q)).natDegree : ℤ) at H
  omega

theorem invalid_base (P : Readers) (F : Family) (features : List Bool → ℕ) (orders : List Bool → List Bool)
    (u record : List Bool) (hu : u ∉ valid P) : moment P F features orders (pair u record) = 0 := by
  have hv : signQuery (pair u record) ∉ valid (P.comp pairFst) := by
    simpa only [valid, Set.mem_ofPred_eq, signQuery, pairFst_pair, pairSnd_pair,
      BoundedProjectionRootCount.count_comp, BinaryNat.normalize_eq_bits, Nat.fromBitsLE_bits] using hu
  have hz : specialized (P.comp pairFst) (F.comp pairFst) (signQuery (pair u record)) = 0 := by
    rw [specialized, ite_eq_right hv]
  rw [moment, hz]
  simp only [RootSignQueries.tarskiQuery, RootSignQueries.signSum, Polynomial.roots_zero,
    Multiset.toFinset_zero, Finset.sum_empty]

end LeanCanny.Encoding.BoundedAlgebraicFiberMoments
