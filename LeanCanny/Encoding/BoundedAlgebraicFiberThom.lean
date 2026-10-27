/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicSliceDerivatives
public import LeanCanny.Encoding.BoundedAlgebraicFiberRoot
public import LeanCanny.Algebra.SparseSignSpanning
public import LeanCanny.Algebra.ThomEncoding

/-! # Derivative signatures of roots in algebraic fibers

All distinct roots have different derivative-sign signatures. Sparse
monomials using at most the binary degree width span every rational-valued
root function. Native moment and single-sign counts are provided for any
binary derivative index; no whole signature is stored.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicFiberThom
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedAlgebraicSlice
open scoped Classical BigOperators
attribute [local irreducible] BoundedProjectionRootCount.count BoundedProjectionOrderedRoot.root

abbrev Root (P : Readers) (F : Family) (u : List Bool) := {x // x ∈ RootCount.roots P F u}
abbrev Feature (F : Family) (u : List Bool) := Fin (F.degree (pairFst u) + 1)

noncomputable def signature (P : Readers) (F : Family) (u : List Bool) (x : Root P F u) : Feature F u → SignType :=
  ThomEncoding.signature (specialized P F u) (F.degree (pairFst u)) x.val

theorem signature_injective (P : Readers) (F : Family) (u : List Bool) : Function.Injective (signature P F u) := by
  intro x y he
  have hx : x.val ∈ (specialized P F u).roots := Multiset.mem_toFinset.mp x.property
  have hy : y.val ∈ (specialized P F u).roots := Multiset.mem_toFinset.mp y.property
  apply Subtype.ext
  apply ThomEncoding.root_eq (specialized P F u) (Polynomial.ne_zero_of_mem_roots hx)
    (F.degree (pairFst u)) (specialized_degree P F u)
  · exact Polynomial.isRoot_of_mem_roots hx
  · exact Polynomial.isRoot_of_mem_roots hy
  · intro k hk
    exact congrFun he ⟨k, by omega⟩

noncomputable def vector (P : Readers) (F : Family) (u : List Bool) (d : Feature F u →₀ ℕ) : Root P F u → ℚ :=
  MonomialEvaluationBasis.vector (MvPolynomial.aeval (R := ℚ) (fun i x => (signature P F u x i : ℚ))) d

theorem sparse_span (P : Readers) (F : Family) (u : List Bool) :
    Submodule.span ℚ (vector P F u '' {d | d.support.card ≤ (F.degree (pairFst u)).size ∧ ∀ i, d i ≤ 2}) = ⊤ := by
  apply SparseSignSpanning.signatures_span (MonomialOrder.degLex (σ := Feature F u))
    (signature P F u) (signature_injective P F u) (F.degree (pairFst u)).size
  simpa only [Fintype.card_coe, RootCount.count] using (BoundedAlgebraicFiberRoot.count_le_degree P F u).trans
    (Nat.lt_size_self (F.degree (pairFst u))).le

noncomputable def derivativeFamily (F : Family) : Family := iterateDerivative (F.comp pairFst) pairSnd

noncomputable def derivativeAccess {F : Family} (A : F.Access) : (derivativeFamily F).Access :=
  iterateDerivativeAccess (A.comp pairFst pairFst_mem_FP) pairSnd pairSnd_mem_FP

/-- Input: a base-root query paired with a binary derivative order. -/
noncomputable def count (P : Readers) (F : Family) (s : SignType) (q : List Bool) : List Bool :=
  BinaryNatCode.encode (RootCount.signCount (P.comp pairFst) (F.comp pairFst) (derivativeFamily F) s (signQuery q))

theorem count_evaluator {P : Readers} (h : P.PolyTime) {F : Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (s : SignType) : SpaceFunction (count P F s) :=
  (RootCount.signCount_evaluator (h.comp pairFst_mem_FP) (A.comp pairFst pairFst_mem_FP) (derivativeAccess A)
    (fun c => ha (pairFst c)) s).precompose signQuery signQuery_FP

theorem count_packet (P : Readers) (F : Family) (s : SignType) (c : List Bool)
    (r : Fin (BoundedProjectionRootCount.count P c)) (j : ℕ) :
    count P F s (pair (pair c (BinaryNatCode.encode r.val)) (BinaryNatCode.encode j)) = BinaryNatCode.encode
      (RootSignQueries.singleSignCount (F.slice c (BoundedProjectionOrderedRoot.root P c r).val)
        ((Polynomial.derivative^[j]) (F.slice c (BoundedProjectionOrderedRoot.root P c r).val)) s) := by
  simp only [count, RootCount.signCount, specialized_attach, derivativeFamily, iterateDerivative_slice,
    Family.slice_comp, pairFst_pair, pairSnd_pair]
  rw [show Nat.fromBitsLE (BinaryNatCode.encode j) = j from Nat.fromBitsLE_bits j]

noncomputable def moment (P : Readers) (F : Family) (q : List Bool) : List Bool :=
  Tarski.value (P.comp pairFst) (F.comp pairFst) (derivativeFamily F) (signQuery q)

theorem moment_evaluator {P : Readers} (h : P.PolyTime) {F : Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (moment P F) :=
  (Tarski.evaluator (h.comp pairFst_mem_FP) (A.comp pairFst pairFst_mem_FP) (derivativeAccess A)
    (fun c => ha (pairFst c))).precompose signQuery signQuery_FP

theorem moment_packet (P : Readers) (F : Family) (c : List Bool)
    (r : Fin (BoundedProjectionRootCount.count P c)) (j : ℕ) :
    moment P F (pair (pair c (BinaryNatCode.encode r.val)) (BinaryNatCode.encode j)) = SignStatisticBits.integerCode
      (RootSignQueries.tarskiQuery (F.slice c (BoundedProjectionOrderedRoot.root P c r).val)
        ((Polynomial.derivative^[j]) (F.slice c (BoundedProjectionOrderedRoot.root P c r).val))) := by
  simp only [moment, Tarski.value, specialized_attach, derivativeFamily, iterateDerivative_slice,
    Family.slice_comp, pairFst_pair, pairSnd_pair]
  rw [show Nat.fromBitsLE (BinaryNatCode.encode j) = j from Nat.fromBitsLE_bits j]

end LeanCanny.Encoding.BoundedAlgebraicFiberThom
