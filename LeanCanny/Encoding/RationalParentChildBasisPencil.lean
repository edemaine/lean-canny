/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.RationalParentChildBasisGram
public import LeanCanny.Algebra.FunctionBasisPencil
public import LeanCanny.Encoding.RationalParentChildRootHash

/-! # A distinct-root test for functions on the regular child roots

The selected basis is square after a purely mathematical reindexing of its
root columns. Its weighted Gram pencil has one root per distinct value of
the supplied root function. In particular, having the full distinct-root
count is equivalent to separation. This bridge uses neither an inverse
matrix nor a root enumeration in any claimed native computation.
-/

@[expose] public section
namespace LeanCanny.Encoding.RationalParentChildBasisPencil
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open RationalParentChildRankBasis Polynomial
open RationalParentChildSource (Inputs)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] RationalParentChildRecords.length RationalParentChildThom.labelWidth
  RationalParentChildCoordinates.parameterDegree RationalParentChildCoordinates.baseHeight
  RationalParentChildQueries.roots RationalParentChildRegularCount.count

noncomputable def rootEquiv (P : Inputs) (c : List Bool) :
    Fin (RationalParentChildRegularCount.count P c) ≃ RationalParentChildRecordSpan.Root P c :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, Fintype.card_coe]
    exact (RationalParentChildQueries.roots_card P c).symm)

noncomputable def square (P : Inputs) (c : List Bool) :
    Matrix (Fin (RationalParentChildRegularCount.count P c)) (Fin (RationalParentChildRegularCount.count P c)) ℚ :=
  fun i j => selected P c i (rootEquiv P c j)

theorem gram_eq (P : Inputs) (c : List Bool) :
    FunctionBasisPencil.gram (square P c) = RationalParentChildBasisGram.gram P c := by
  apply Matrix.ext
  intro i j
  change (∑ k, selected P c i (rootEquiv P c k) * selected P c j (rootEquiv P c k)) =
    ∑ x, selected P c i x * selected P c j x
  exact (rootEquiv P c).sum_comp (fun x => selected P c i x * selected P c j x)

theorem square_det_ne_zero (P : Inputs) (c : List Bool) : (square P c).det ≠ 0 := by
  have hr : (FunctionBasisPencil.gram (square P c)).rank =
      Fintype.card (Fin (RationalParentChildRegularCount.count P c)) := by
    rw [gram_eq, RationalParentChildBasisGram.rank_gram, Fintype.card_fin]
  have hs := Matrix.mulVec_surjective_iff_rank_eq_card.mpr hr
  have hu := Matrix.mulVec_surjective_iff_isUnit.mp hs
  have hd : (FunctionBasisPencil.gram (square P c)).det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hu)
  rw [FunctionBasisPencil.gram, Matrix.det_mul, Matrix.det_transpose] at hd
  exact (mul_ne_zero_iff.mp hd).1

noncomputable def weighted (P : Inputs) (c : List Bool) (v : RationalParentChildRecordSpan.Root P c → ℚ) :
    Matrix (Fin (RationalParentChildRegularCount.count P c)) (Fin (RationalParentChildRegularCount.count P c)) ℚ :=
  fun i j => ∑ x, selected P c i x * v x * selected P c j x

theorem weighted_eq (P : Inputs) (c : List Bool) (v : RationalParentChildRecordSpan.Root P c → ℚ) :
    FunctionBasisPencil.weighted (square P c) (v ∘ rootEquiv P c) = weighted P c v := by
  apply Matrix.ext
  intro i j
  unfold FunctionBasisPencil.weighted
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  exact (rootEquiv P c).sum_comp (fun x => selected P c i x * v x * selected P c j x)

noncomputable def pencil (P : Inputs) (c : List Bool) (v : RationalParentChildRecordSpan.Root P c → ℚ) :
    Matrix (Fin (RationalParentChildRegularCount.count P c)) (Fin (RationalParentChildRegularCount.count P c)) ℚ[X] :=
  fun i j => C (RationalParentChildBasisGram.gram P c i j) * X - C (weighted P c v i j)

theorem pencil_eq (P : Inputs) (c : List Bool) (v : RationalParentChildRecordSpan.Root P c → ℚ) :
    pencil P c v = FunctionBasisPencil.pencil (square P c) (v ∘ rootEquiv P c) := by
  unfold pencil FunctionBasisPencil.pencil
  rw [gram_eq, weighted_eq]

theorem rootCount_eq_count_iff (P : Inputs) (c : List Bool)
    (v : RationalParentChildRecordSpan.Root P c → ℚ) :
    (pencil P c v).det.roots.toFinset.card = RationalParentChildRegularCount.count P c ↔ Function.Injective v := by
  rw [pencil_eq]
  have he := FunctionBasisPencil.rootCount_eq_card_iff (square P c) (v ∘ rootEquiv P c) (square_det_ne_zero P c)
  refine Iff.trans (Iff.intro (fun h => he.mp (h.trans (Fintype.card_fin _).symm))
    (fun h => (he.mpr h).trans (Fintype.card_fin _))) ?_
  constructor
  · intro h x y he
    obtain ⟨i, rfl⟩ := (rootEquiv P c).surjective x
    obtain ⟨j, rfl⟩ := (rootEquiv P c).surjective y
    exact congrArg (rootEquiv P c) (h he)
  · intro h
    exact h.comp (rootEquiv P c).injective

theorem exists_hash_parameters (P : Inputs) (c : List Bool) :
    ∃ p t : ℕ, p.Prime ∧ p < 2 ^ RationalParentChildRootHash.bitWidth P c ∧ t < p ∧
      (pencil P c (fun x => (RationalParentChildRootHash.integerValue P c p t x : ℚ))).det.roots.toFinset.card =
        RationalParentChildRegularCount.count P c := by
  obtain ⟨p, t, hp, hs, ht, hi⟩ := RationalParentChildRootHash.exists_short_labels P c
  refine ⟨p, t, hp, hs, ht, (rootCount_eq_count_iff P c _).mpr ?_⟩
  intro x y he
  apply RationalParentChildRootHash.integerValue_injective P c p t hi
  exact Int.cast_injective he

end LeanCanny.Encoding.RationalParentChildBasisPencil
