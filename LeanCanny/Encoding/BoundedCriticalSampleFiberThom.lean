/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleFiberRoot
public import LeanCanny.Encoding.BoundedAlgebraicSliceDerivatives
public import LeanCanny.Algebra.SparseSignSpanning
public import LeanCanny.Algebra.ThomEncoding

/-! # Separating child-root features at actual critical samples

Derivative signs separate distinct fiber roots, including multiple roots and
degree drops. Short sparse monomials span every rational-valued root function.
Native individual moments keep the actual sample fixed when orders are attached.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleFiberThom
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedAlgebraicSlice (Family iterateDerivative iterateDerivativeAccess iterateDerivative_slice)
open BoundedCriticalSampleSlice
open scoped Classical BigOperators

abbrev Root (P : Readers) (F : Family) (u : List Bool) := BoundedCriticalSampleFiberRoot.Root P F u
abbrev Feature (F : Family) (u : List Bool) := Fin (F.degree (context u) + 1)

noncomputable def signature (P : Readers) (F : Family) (u : List Bool) (x : Root P F u) : Feature F u → SignType :=
  ThomEncoding.signature (specialized P F u) (F.degree (context u)) x.val

theorem signature_injective (P : Readers) (F : Family) (u : List Bool) : Function.Injective (signature P F u) := by
  intro x y he
  have hx : x.val ∈ (specialized P F u).roots := Multiset.mem_toFinset.mp x.property
  have hy : y.val ∈ (specialized P F u).roots := Multiset.mem_toFinset.mp y.property
  apply Subtype.ext
  apply ThomEncoding.root_eq (specialized P F u) (Polynomial.ne_zero_of_mem_roots hx)
    (F.degree (context u)) (specialized_degree P F u)
  · exact Polynomial.isRoot_of_mem_roots hx
  · exact Polynomial.isRoot_of_mem_roots hy
  · intro k hk
    exact congrFun he ⟨k, by omega⟩

noncomputable def vector (P : Readers) (F : Family) (u : List Bool) (d : Feature F u →₀ ℕ) : Root P F u → ℚ :=
  MonomialEvaluationBasis.vector (MvPolynomial.aeval (R := ℚ) (fun i x => (signature P F u x i : ℚ))) d

theorem sparse_span (P : Readers) (F : Family) (u : List Bool) :
    Submodule.span ℚ (vector P F u '' {d | d.support.card ≤ (F.degree (context u)).size ∧ ∀ i, d i ≤ 2}) = ⊤ := by
  apply SparseSignSpanning.signatures_span (MonomialOrder.degLex (σ := Feature F u))
    (signature P F u) (signature_injective P F u) (F.degree (context u)).size
  simpa only [Fintype.card_coe, RootCount.count] using (BoundedCriticalSampleFiberRoot.count_le_degree P F u).trans
    (Nat.lt_size_self (F.degree (context u))).le

def orderWord (v : List Bool) : List Bool := pairSnd (pairSnd v)
theorem orderWord_FP : orderWord ∈ FP := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
def query (q : List Bool) : List Bool := attach (pairFst q) (pairSnd q)
theorem query_FP : query ∈ FP := by polytime [query, attach]

noncomputable def derivativeFamily (F : Family) : Family := iterateDerivative (F.comp dropRecord) orderWord
noncomputable def derivativeAccess {F : Family} (A : F.Access) : (derivativeFamily F).Access :=
  iterateDerivativeAccess (A.comp dropRecord dropRecord_FP) orderWord orderWord_FP

theorem derivative_specialized (P : Readers) (F : Family) (u j : List Bool) :
    specialized P (derivativeFamily F) (attach u j) =
      (Polynomial.derivative^[Nat.fromBitsLE j]) (specialized P F u) := by
  by_cases hu : u ∈ valid P
  · have hv := (attach_valid P u j).mpr hu
    rw [specialized, ite_eq_left hv, derivativeFamily, iterateDerivative_slice, Family.slice_comp]
    rw [specialized, ite_eq_left hu]
    simp only [context, attach, dropRecord, orderWord, pairFst_pair, pairSnd_pair]
  · have hv := mt (attach_valid P u j).mp hu
    simp only [specialized, ite_eq_right hv, ite_eq_right hu, Polynomial.iterate_derivative_zero]

noncomputable def moment (P : Readers) (F : Family) : List Bool → List Bool :=
  Tarski.value P (F.comp dropRecord) (derivativeFamily F) ∘ query
theorem moment_evaluator {P : Readers} (h : P.PolyTime) {F : Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (moment P F) :=
  (Tarski.evaluator h (A.comp dropRecord dropRecord_FP) (derivativeAccess A) ha).precompose query query_FP

theorem moment_packet (P : Readers) (F : Family) (u : List Bool) (j : ℕ) :
    moment P F (pair u (BinaryNatCode.encode j)) = SignStatisticBits.integerCode
      (RootSignQueries.tarskiQuery (specialized P F u)
        ((Polynomial.derivative^[j]) (specialized P F u))) := by
  simp only [moment, Function.comp_apply, query, pairFst_pair, pairSnd_pair, Tarski.value,
    specialized_attach, derivative_specialized, BinaryNatCode.encode, Nat.fromBitsLE_bits]

noncomputable def count (P : Readers) (F : Family) (s : SignType) (q : List Bool) : ℕ :=
  RootCount.signCount P (F.comp dropRecord) (derivativeFamily F) s (query q)
theorem count_evaluator {P : Readers} (h : P.PolyTime) {F : Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (s : SignType) :
    SpaceFunction (fun q => BinaryNatCode.encode (count P F s q)) :=
  (RootCount.signCount_evaluator h (A.comp dropRecord dropRecord_FP) (derivativeAccess A) ha s).precompose query query_FP

theorem count_packet (P : Readers) (F : Family) (s : SignType) (u : List Bool) (j : ℕ) :
    count P F s (pair u (BinaryNatCode.encode j)) = RootSignQueries.singleSignCount
      (specialized P F u) ((Polynomial.derivative^[j]) (specialized P F u)) s := by
  simp only [count, query, pairFst_pair, pairSnd_pair, RootCount.signCount,
    specialized_attach, derivative_specialized, BinaryNatCode.encode, Nat.fromBitsLE_bits]

end LeanCanny.Encoding.BoundedCriticalSampleFiberThom
