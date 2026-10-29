/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatFullSourceSampleBasisGram
public import LeanCanny.Algebra.FunctionBasisPencil
public import LeanCanny.Encoding.FlatFullSourceSampleRootHash

/-! # A distinct-root test for functions on the regular flat roots

The selected basis is square after a purely mathematical reindexing of its
root columns. Its weighted Gram pencil has one root per distinct value of
the supplied root function. In particular, having the full distinct-root
count is equivalent to separation. This bridge uses neither an inverse
matrix nor a root enumeration in any claimed native computation.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatFullSourceSampleBasisPencil
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open FlatFullSourceSampleRankBasis Polynomial
open FlatFullSourceTower (Inputs)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FlatFullSourceSampleRecords.length FlatFullSourceSampleThom.labelWidth
  FlatFullSourceSampleCoordinates.parameterDegree FlatFullSourceSampleCoordinates.baseHeight
  FlatFullSourceSampleQueries.roots FlatFullSourceSampleRegularCount.count

noncomputable def rootEquiv (P : Inputs) (c : List Bool) :
    Fin (FlatFullSourceSampleRegularCount.count P c) ≃ FlatFullSourceSampleRecordSpan.Root P c :=
  Fintype.equivOfCardEq (by
    rw [Fintype.card_fin, Fintype.card_coe]
    exact (FlatFullSourceSampleQueries.roots_card P c).symm)

noncomputable def square (P : Inputs) (c : List Bool) :
    Matrix (Fin (FlatFullSourceSampleRegularCount.count P c)) (Fin (FlatFullSourceSampleRegularCount.count P c)) ℚ :=
  fun i j => selected P c i (rootEquiv P c j)

theorem gram_eq (P : Inputs) (c : List Bool) :
    FunctionBasisPencil.gram (square P c) = FlatFullSourceSampleBasisGram.gram P c := by
  apply Matrix.ext
  intro i j
  change (∑ k, selected P c i (rootEquiv P c k) * selected P c j (rootEquiv P c k)) =
    ∑ x, selected P c i x * selected P c j x
  exact (rootEquiv P c).sum_comp (fun x => selected P c i x * selected P c j x)

theorem square_det_ne_zero (P : Inputs) (c : List Bool) : (square P c).det ≠ 0 := by
  have hr : (FunctionBasisPencil.gram (square P c)).rank =
      Fintype.card (Fin (FlatFullSourceSampleRegularCount.count P c)) := by
    rw [gram_eq, FlatFullSourceSampleBasisGram.rank_gram, Fintype.card_fin]
  have hs := Matrix.mulVec_surjective_iff_rank_eq_card.mpr hr
  have hu := Matrix.mulVec_surjective_iff_isUnit.mp hs
  have hd : (FunctionBasisPencil.gram (square P c)).det ≠ 0 :=
    isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hu)
  rw [FunctionBasisPencil.gram, Matrix.det_mul, Matrix.det_transpose] at hd
  exact (mul_ne_zero_iff.mp hd).1

noncomputable def weighted (P : Inputs) (c : List Bool) (v : FlatFullSourceSampleRecordSpan.Root P c → ℚ) :
    Matrix (Fin (FlatFullSourceSampleRegularCount.count P c)) (Fin (FlatFullSourceSampleRegularCount.count P c)) ℚ :=
  fun i j => ∑ x, selected P c i x * v x * selected P c j x

theorem weighted_eq (P : Inputs) (c : List Bool) (v : FlatFullSourceSampleRecordSpan.Root P c → ℚ) :
    FunctionBasisPencil.weighted (square P c) (v ∘ rootEquiv P c) = weighted P c v := by
  apply Matrix.ext
  intro i j
  unfold FunctionBasisPencil.weighted
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]
  exact (rootEquiv P c).sum_comp (fun x => selected P c i x * v x * selected P c j x)

noncomputable def pencil (P : Inputs) (c : List Bool) (v : FlatFullSourceSampleRecordSpan.Root P c → ℚ) :
    Matrix (Fin (FlatFullSourceSampleRegularCount.count P c)) (Fin (FlatFullSourceSampleRegularCount.count P c)) ℚ[X] :=
  fun i j => C (FlatFullSourceSampleBasisGram.gram P c i j) * X - C (weighted P c v i j)

theorem pencil_eq (P : Inputs) (c : List Bool) (v : FlatFullSourceSampleRecordSpan.Root P c → ℚ) :
    pencil P c v = FunctionBasisPencil.pencil (square P c) (v ∘ rootEquiv P c) := by
  unfold pencil FunctionBasisPencil.pencil
  rw [gram_eq, weighted_eq]

theorem rootCount_eq_count_iff (P : Inputs) (c : List Bool)
    (v : FlatFullSourceSampleRecordSpan.Root P c → ℚ) :
    (pencil P c v).det.roots.toFinset.card = FlatFullSourceSampleRegularCount.count P c ↔ Function.Injective v := by
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
    ∃ p t : ℕ, p.Prime ∧ p < 2 ^ FlatFullSourceSampleRootHash.bitWidth P c ∧ t < p ∧
      (pencil P c (fun x => (FlatFullSourceSampleRootHash.integerValue P c p t x : ℚ))).det.roots.toFinset.card =
        FlatFullSourceSampleRegularCount.count P c := by
  obtain ⟨p, t, hp, hs, ht, hi⟩ := FlatFullSourceSampleRootHash.exists_short_labels P c
  refine ⟨p, t, hp, hs, ht, (rootCount_eq_count_iff P c _).mpr ?_⟩
  intro x y he
  apply FlatFullSourceSampleRootHash.integerValue_injective P c p t hi
  exact Int.cast_injective he

end LeanCanny.Encoding.FlatFullSourceSampleBasisPencil
