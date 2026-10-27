/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicFiberRecords
public import Mathlib.LinearAlgebra.Matrix.Rank

/-! # Sparse records span the algebraic-fiber root-function space

Every sparse Thom-sign monomial has a record of the constructed polynomial
length. The matrix of all records, and its Gram matrix, therefore have rank
exactly the number of distinct fiber roots. Empty root sets are permitted.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicFiberRecordSpan
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter BoundedAlgebraicSlice Submodule
open BoundedAlgebraicFiberRecords
open scoped Classical BigOperators

abbrev Root (P : Readers) (F : Family) (u : List Bool) := BoundedAlgebraicFiberThom.Root P F u
abbrev Feature (F : Family) (u : List Bool) := BoundedAlgebraicFiberThom.Feature F u
abbrev Index (F : Family) (u : List Bool) := Fin (2 ^ length F (pairFst u))

noncomputable def row (P : Readers) (F : Family) (u r : List Bool) : Root P F u → ℚ :=
  SparseFeatureRecords.value (Nat.succ_pos _) (slots F (pairFst u)) (width F (pairFst u))
    (fun i : Feature F u => fun x => (BoundedAlgebraicFiberThom.signature P F u x i : ℚ)) r

theorem row_apply (P : Readers) (F : Family) (u r : List Bool) (x : Root P F u) :
    row P F u r x = SparseFeatureRecords.value (Nat.succ_pos _) (slots F (pairFst u)) (width F (pairFst u))
      (fun i : Feature F u => (BoundedAlgebraicFiberThom.signature P F u x i : ℚ)) r := by
  simp only [row, SparseFeatureRecords.value, Finset.prod_apply, SparseFeatureRecords.factor, ite_apply, Pi.one_apply]

theorem monomial_has_record (P : Readers) (F : Family) (u : List Bool) (d : Feature F u →₀ ℕ)
    (hs : d.support.card ≤ (F.degree (pairFst u)).size) (he : ∀ i, d i ≤ 2) :
    ∃ r, r.length = length F (pairFst u) ∧ row P F u r = BoundedAlgebraicFiberThom.vector P F u d := by
  have ht := SparseFeatureRecords.total_exponent_le d _ hs he
  obtain ⟨r, hr, hv⟩ := SparseFeatureRecords.exists_record (M := Root P F u → ℚ)
    (Nat.succ_pos (F.degree (pairFst u))) (slots F (pairFst u)) (width F (pairFst u))
    (feature_fits F (pairFst u)) d ht
  refine ⟨r, hr, ?_⟩
  unfold row
  rw [hv]
  simp only [BoundedAlgebraicFiberThom.vector, MonomialEvaluationBasis.vector, MvPolynomial.aeval_monomial, map_one, one_mul]

theorem span_rows (P : Readers) (F : Family) (u : List Bool) :
    Submodule.span ℚ (row P F u '' {r | r.length = length F (pairFst u)}) = ⊤ := by
  apply top_unique
  rw [← BoundedAlgebraicFiberThom.sparse_span P F u]
  apply Submodule.span_le.mpr
  rintro _ ⟨d, hd, rfl⟩
  obtain ⟨r, hr, hv⟩ := monomial_has_record P F u d hd.1 hd.2
  rw [← hv]
  exact Submodule.subset_span ⟨r, hr, rfl⟩

noncomputable def matrix (P : Readers) (F : Family) (u : List Bool) : Matrix (Index F u) (Root P F u) ℚ :=
  fun i => row P F u (ImplicitGraph.word (length F (pairFst u)) i.val)

theorem span_matrix_rows (P : Readers) (F : Family) (u : List Bool) :
    Submodule.span ℚ (Set.range (matrix P F u).row) = ⊤ := by
  apply top_unique
  rw [← span_rows P F u]
  apply Submodule.span_le.mpr
  rintro _ ⟨r, hr, rfl⟩
  have hi : Nat.fromBitsLE r < 2 ^ length F (pairFst u) := by rw [← hr]; exact Nat.fromBitsLE_lt_pow_length r
  apply Submodule.subset_span
  refine ⟨⟨Nat.fromBitsLE r, hi⟩, ?_⟩
  change row P F u (ImplicitGraph.word (length F (pairFst u)) (Nat.fromBitsLE r)) = row P F u r
  rw [← hr, ImplicitGraph.word_fromBitsLE]

theorem rank_matrix (P : Readers) (F : Family) (u : List Bool) : (matrix P F u).rank = RootCount.count P F u := by
  rw [Matrix.rank_eq_finrank_span_row, span_matrix_rows, finrank_top, Module.finrank_fintype_fun_eq_card]
  exact Fintype.card_coe _

noncomputable def gram (P : Readers) (F : Family) (u : List Bool) : Matrix (Index F u) (Index F u) ℚ :=
  matrix P F u * (matrix P F u).transpose

theorem rank_gram (P : Readers) (F : Family) (u : List Bool) : (gram P F u).rank = RootCount.count P F u := by
  rw [gram, Matrix.rank_self_mul_transpose, rank_matrix]

theorem dimension_binary {F : Family} (A : F.Access) : BinaryFn (fun u => 2 ^ length F (pairFst u)) :=
  Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_two_pow.comp ((length_unary A).comp pairFst_mem_FP)

end LeanCanny.Encoding.BoundedAlgebraicFiberRecordSpan
