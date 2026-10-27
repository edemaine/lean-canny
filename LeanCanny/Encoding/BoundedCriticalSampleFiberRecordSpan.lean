/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleFiberThom
public import LeanCanny.Encoding.BoundedAlgebraicFiberRecords
public import Mathlib.LinearAlgebra.Matrix.Rank

/-! # Short records span child-root functions at actual samples

The existing sparse-record encoding is reused at the unchanged source and
record context. Its rows and Gram matrix have rank equal to the number of
distinct child roots, including empty fibers and invalid base descriptors.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleFiberRecordSpan
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Submodule
open BoundedAlgebraicSlice (Family)
open BoundedCriticalSampleSlice BoundedAlgebraicFiberRecords
open scoped Classical BigOperators

abbrev Root (P : Readers) (F : Family) (u : List Bool) := BoundedCriticalSampleFiberThom.Root P F u
abbrev Feature (F : Family) (u : List Bool) := BoundedCriticalSampleFiberThom.Feature F u
abbrev Index (F : Family) (u : List Bool) := Fin (2 ^ length F (context u))

noncomputable def row (P : Readers) (F : Family) (u r : List Bool) : Root P F u → ℚ :=
  SparseFeatureRecords.value (Nat.succ_pos _) (slots F (context u)) (width F (context u))
    (fun i : Feature F u => fun x => (BoundedCriticalSampleFiberThom.signature P F u x i : ℚ)) r

theorem row_apply (P : Readers) (F : Family) (u r : List Bool) (x : Root P F u) :
    row P F u r x = SparseFeatureRecords.value (Nat.succ_pos _) (slots F (context u)) (width F (context u))
      (fun i : Feature F u => (BoundedCriticalSampleFiberThom.signature P F u x i : ℚ)) r := by
  simp only [row, SparseFeatureRecords.value, Finset.prod_apply, SparseFeatureRecords.factor, ite_apply, Pi.one_apply]

theorem monomial_has_record (P : Readers) (F : Family) (u : List Bool) (d : Feature F u →₀ ℕ)
    (hs : d.support.card ≤ (F.degree (context u)).size) (he : ∀ i, d i ≤ 2) :
    ∃ r, r.length = length F (context u) ∧ row P F u r = BoundedCriticalSampleFiberThom.vector P F u d := by
  have ht := SparseFeatureRecords.total_exponent_le d _ hs he
  obtain ⟨r, hr, hv⟩ := SparseFeatureRecords.exists_record (M := Root P F u → ℚ)
    (Nat.succ_pos (F.degree (context u))) (slots F (context u)) (width F (context u))
    (feature_fits F (context u)) d ht
  refine ⟨r, hr, ?_⟩
  unfold row
  rw [hv]
  simp only [BoundedCriticalSampleFiberThom.vector, MonomialEvaluationBasis.vector,
    MvPolynomial.aeval_monomial, map_one, one_mul]

theorem span_rows (P : Readers) (F : Family) (u : List Bool) :
    Submodule.span ℚ (row P F u '' {r | r.length = length F (context u)}) = ⊤ := by
  apply top_unique
  rw [← BoundedCriticalSampleFiberThom.sparse_span P F u]
  apply Submodule.span_le.mpr
  rintro _ ⟨d, hd, rfl⟩
  obtain ⟨r, hr, hv⟩ := monomial_has_record P F u d hd.1 hd.2
  rw [← hv]
  exact Submodule.subset_span ⟨r, hr, rfl⟩

noncomputable def matrix (P : Readers) (F : Family) (u : List Bool) : Matrix (Index F u) (Root P F u) ℚ :=
  fun i => row P F u (ImplicitGraph.word (length F (context u)) i.val)

theorem span_matrix_rows (P : Readers) (F : Family) (u : List Bool) :
    Submodule.span ℚ (Set.range (matrix P F u).row) = ⊤ := by
  apply top_unique
  rw [← span_rows P F u]
  apply Submodule.span_le.mpr
  rintro _ ⟨r, hr, rfl⟩
  have hi : Nat.fromBitsLE r < 2 ^ length F (context u) := by rw [← hr]; exact Nat.fromBitsLE_lt_pow_length r
  apply Submodule.subset_span
  refine ⟨⟨Nat.fromBitsLE r, hi⟩, ?_⟩
  change row P F u (ImplicitGraph.word (length F (context u)) (Nat.fromBitsLE r)) = row P F u r
  rw [← hr, ImplicitGraph.word_fromBitsLE]

theorem rank_matrix (P : Readers) (F : Family) (u : List Bool) : (matrix P F u).rank = RootCount.count P F u := by
  rw [Matrix.rank_eq_finrank_span_row, span_matrix_rows, finrank_top, Module.finrank_fintype_fun_eq_card]
  exact Fintype.card_coe _

noncomputable def gram (P : Readers) (F : Family) (u : List Bool) : Matrix (Index F u) (Index F u) ℚ :=
  matrix P F u * (matrix P F u).transpose

theorem rank_gram (P : Readers) (F : Family) (u : List Bool) : (gram P F u).rank = RootCount.count P F u := by
  rw [gram, Matrix.rank_self_mul_transpose, rank_matrix]

theorem dimension_binary {F : Family} (A : F.Access) : BinaryFn (fun u => 2 ^ length F (context u)) :=
  Turing.MultiTapeTM.ComputableTidilyInPolyTime.binary_two_pow.comp ((length_unary A).comp context_FP)

end LeanCanny.Encoding.BoundedCriticalSampleFiberRecordSpan
