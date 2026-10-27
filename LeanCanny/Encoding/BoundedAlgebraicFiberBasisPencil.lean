/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicFiberBasisGram
public import LeanCanny.Algebra.FunctionBasisPencil
public import LeanCanny.Encoding.BoundedAlgebraicFiberRootHash

/-! # A distinct-root test for functions on the fiber roots

The selected basis is square after a purely mathematical reindexing of its
root columns. Its weighted Gram pencil has one root per distinct value of
the supplied root function. In particular, having the full distinct-root
count is equivalent to separation. This bridge uses neither an inverse
matrix nor a root enumeration in any claimed native computation.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicFiberBasisPencil
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open BoundedAlgebraicSlice BoundedAlgebraicFiberRankBasis Polynomial
open scoped Classical BigOperators

noncomputable def rootEquiv (P : Readers) (F : Family) (c : List Bool) :
    Fin (RootCount.count P F c) ≃ BoundedAlgebraicFiberRecordSpan.Root P F c :=
  Fintype.equivOfCardEq (by rw [Fintype.card_fin]; exact (Fintype.card_coe _).symm)

noncomputable def square (P : Readers) (F : Family) (c : List Bool) :
    Matrix (Fin (RootCount.count P F c)) (Fin (RootCount.count P F c)) ℚ :=
  fun i j => selected P F c i (rootEquiv P F c j)

theorem gram_eq (P : Readers) (F : Family) (c : List Bool) :
    FunctionBasisPencil.gram (square P F c) = BoundedAlgebraicFiberBasisGram.gram P F c := by
  apply Matrix.ext
  intro i j
  change (∑ k, selected P F c i (rootEquiv P F c k) * selected P F c j (rootEquiv P F c k)) =
    ∑ x, selected P F c i x * selected P F c j x
  exact (rootEquiv P F c).sum_comp (fun x => selected P F c i x * selected P F c j x)

theorem square_det_ne_zero (P : Readers) (F : Family) (c : List Bool) : (square P F c).det ≠ 0 := by
  have hr : (FunctionBasisPencil.gram (square P F c)).rank =
      Fintype.card (Fin (RootCount.count P F c)) := by
    rw [gram_eq, BoundedAlgebraicFiberBasisGram.rank_gram, Fintype.card_fin]
  have hs := Matrix.mulVec_surjective_iff_rank_eq_card.mpr hr
  have hu := Matrix.mulVec_surjective_iff_isUnit.mp hs
  have hd : (FunctionBasisPencil.gram (square P F c)).det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hu)
  rw [FunctionBasisPencil.gram, Matrix.det_mul, Matrix.det_transpose] at hd
  exact (mul_ne_zero_iff.mp hd).1

noncomputable def weighted (P : Readers) (F : Family) (c : List Bool) (v : BoundedAlgebraicFiberRecordSpan.Root P F c → ℚ) :
    Matrix (Fin (RootCount.count P F c)) (Fin (RootCount.count P F c)) ℚ :=
  fun i j => ∑ x, selected P F c i x * v x * selected P F c j x

theorem weighted_eq (P : Readers) (F : Family) (c : List Bool) (v : BoundedAlgebraicFiberRecordSpan.Root P F c → ℚ) :
    FunctionBasisPencil.weighted (square P F c) (v ∘ rootEquiv P F c) = weighted P F c v := by
  apply Matrix.ext
  intro i j
  unfold FunctionBasisPencil.weighted
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  exact (rootEquiv P F c).sum_comp (fun x => selected P F c i x * v x * selected P F c j x)

noncomputable def pencil (P : Readers) (F : Family) (c : List Bool) (v : BoundedAlgebraicFiberRecordSpan.Root P F c → ℚ) :
    Matrix (Fin (RootCount.count P F c)) (Fin (RootCount.count P F c)) ℚ[X] :=
  fun i j => C (BoundedAlgebraicFiberBasisGram.gram P F c i j) * X - C (weighted P F c v i j)

theorem pencil_eq (P : Readers) (F : Family) (c : List Bool) (v : BoundedAlgebraicFiberRecordSpan.Root P F c → ℚ) :
    pencil P F c v = FunctionBasisPencil.pencil (square P F c) (v ∘ rootEquiv P F c) := by
  unfold pencil FunctionBasisPencil.pencil
  rw [gram_eq, weighted_eq]

theorem rootCount_eq_count_iff (P : Readers) (F : Family) (c : List Bool)
    (v : BoundedAlgebraicFiberRecordSpan.Root P F c → ℚ) :
    (pencil P F c v).det.roots.toFinset.card = RootCount.count P F c ↔ Function.Injective v := by
  rw [pencil_eq]
  have he := FunctionBasisPencil.rootCount_eq_card_iff (square P F c) (v ∘ rootEquiv P F c) (square_det_ne_zero P F c)
  refine Iff.trans (Iff.intro (fun h => he.mp (h.trans (Fintype.card_fin _).symm))
    (fun h => (he.mpr h).trans (Fintype.card_fin _))) ?_
  constructor
  · intro h x y he
    obtain ⟨i, rfl⟩ := (rootEquiv P F c).surjective x
    obtain ⟨j, rfl⟩ := (rootEquiv P F c).surjective y
    exact congrArg (rootEquiv P F c) (h he)
  · intro h
    exact h.comp (rootEquiv P F c).injective

theorem exists_hash_parameters (P : Readers) (F : Family) (c : List Bool) :
    ∃ p t : ℕ, p.Prime ∧ p < 2 ^ BoundedAlgebraicFiberRootHash.bitWidth F c ∧ t < p ∧
      (pencil P F c (fun x => (BoundedAlgebraicFiberRootHash.integerValue P F c p t x : ℚ))).det.roots.toFinset.card =
        RootCount.count P F c := by
  obtain ⟨p, t, hp, hs, ht, hi⟩ := BoundedAlgebraicFiberRootHash.exists_short_labels P F c
  refine ⟨p, t, hp, hs, ht, (rootCount_eq_count_iff P F c _).mpr ?_⟩
  intro x y he
  apply BoundedAlgebraicFiberRootHash.integerValue_injective P F c p t hi
  exact Int.cast_injective he

end LeanCanny.Encoding.BoundedAlgebraicFiberBasisPencil
