/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedFullSampleChildPencilBounds
public import LeanCanny.Algebra.FunctionBasisPencilMap

/-! # Identifying the native integer determinant with the root-function pencil

When the context's binary count is the actual regular-child count, the
native polynomial matrix maps to the selected basis pencil. The index cast
changes no determinant. This connects the modular coefficient evaluator to
the separation criterion, including a context with no regular child roots.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedFullSampleChildPencilSource
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedFullSampleChildWeightedMoments BoundedFullSampleChildPencilEntries
open BoundedFullSampleChildSource (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedFullSampleChildRecords.length BoundedFullSampleChildThom.labelWidth
  BoundedFullSampleChildCoordinates.parameterDegree BoundedFullSampleChildCoordinates.baseHeight
  BoundedFullSampleChildQueries.roots BoundedFullSampleChildRegularCount.count

theorem dimension_context (c : List Bool) (n : ℕ) (m : List Bool) (t : ℕ) :
    dimension (context c n m t) = n := by
  simp only [dimension, context, count, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

noncomputable def indexEquiv (P : Inputs) (c m : List Bool) (t : ℕ) :
    Fin (BoundedFullSampleChildRegularCount.count P c) ≃
      Fin (dimension (context c (BoundedFullSampleChildRegularCount.count P c) m t)) :=
  finCongr (dimension_context c (BoundedFullSampleChildRegularCount.count P c) m t).symm

theorem indexEquiv_val (P : Inputs) (c m : List Bool) (t : ℕ) (i : Fin (BoundedFullSampleChildRegularCount.count P c)) :
    (indexEquiv P c m t i).val = i.val := rfl

attribute [local irreducible] BoundedFullSampleChildWeightedMoments.entry BoundedFullSampleChildPencilEntries.gram

theorem matrix_packet (P : Inputs) (c m : List Bool) (t : ℕ) :
    ((matrix P (context c (BoundedFullSampleChildRegularCount.count P c) m t)).submatrix
      (indexEquiv P c m t) (indexEquiv P c m t)).map (Polynomial.mapRingHom (Int.castRingHom ℚ)) =
      BoundedFullSampleChildBasisPencil.pencil P c
        (fun x => (BoundedFullSampleChildRootHash.integerValue P c (Nat.fromBitsLE m + 1) t x : ℚ)) := by
  apply Matrix.ext
  intro i j
  let b := context c (BoundedFullSampleChildRegularCount.count P c) m t
  let q := pair b (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))
  have hg : (gram P q : ℚ) = BoundedFullSampleChildBasisGram.gram P c i j := by
    have hq : gramQuery q = pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)) := by
      simp only [gramQuery, q, b, context, BoundedFullSampleChildWeightedMoments.original, pairFst_pair, pairSnd_pair]
    rw [gram, hq]
    exact BoundedFullSampleChildBasisGram.entry_packet P c i j
  have hw := BoundedFullSampleChildWeightedMoments.entry_packet P c m t i j
  simp only [Matrix.map_apply, Matrix.submatrix_apply, matrix, indexEquiv_val,
    Polynomial.coe_mapRingHom, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, Int.coe_castRingHom]
  change C (gram P q : ℚ) * X - C (entry P q : ℚ) = _
  rw [hg, hw]
  rfl

theorem determinant_packet (P : Inputs) (c m : List Bool) (t : ℕ) :
    (matrix P (context c (BoundedFullSampleChildRegularCount.count P c) m t)).det.map (Int.castRingHom ℚ) =
      (BoundedFullSampleChildBasisPencil.pencil P c
        (fun x => (BoundedFullSampleChildRootHash.integerValue P c (Nat.fromBitsLE m + 1) t x : ℚ))).det := by
  let A := matrix P (context c (BoundedFullSampleChildRegularCount.count P c) m t)
  let e := indexEquiv P c m t
  have hm : ((A.submatrix e e).map (Polynomial.mapRingHom (Int.castRingHom ℚ))).det =
      (A.submatrix e e).det.map (Int.castRingHom ℚ) :=
    ((Polynomial.mapRingHom (Int.castRingHom ℚ)).map_det _).symm
  have hd := congrArg Matrix.det (matrix_packet P c m t)
  change ((A.submatrix e e).map (Polynomial.mapRingHom (Int.castRingHom ℚ))).det = _ at hd
  rw [hm, Matrix.det_submatrix_equiv_self] at hd
  exact hd

theorem real_rootCount_eq_count_iff (P : Inputs) (c m : List Bool) (t : ℕ) :
    (((matrix P (context c (BoundedFullSampleChildRegularCount.count P c) m t)).det.map (Int.castRingHom ℝ)).roots.toFinset).card =
      BoundedFullSampleChildRegularCount.count P c ↔
        Function.Injective (BoundedFullSampleChildRootHash.integerValue P c (Nat.fromBitsLE m + 1) t) := by
  have hcomp : (Rat.castHom ℝ).comp (Int.castRingHom ℚ) = Int.castRingHom ℝ := by
    ext z
    simp
  have hm := congrArg (fun p : ℚ[X] => p.map (Rat.castHom ℝ)) (determinant_packet P c m t)
  rw [Polynomial.map_map, hcomp, BoundedFullSampleChildBasisPencil.pencil_eq] at hm
  rw [hm]
  have he := FunctionBasisPencil.mapped_rootCount_eq_card_iff (Rat.castHom ℝ) (Rat.castHom ℝ).injective
    (BoundedFullSampleChildBasisPencil.square P c)
    ((fun x => (BoundedFullSampleChildRootHash.integerValue P c (Nat.fromBitsLE m + 1) t x : ℚ)) ∘
      BoundedFullSampleChildBasisPencil.rootEquiv P c) (BoundedFullSampleChildBasisPencil.square_det_ne_zero P c)
  refine Iff.trans (Iff.intro (fun h => he.mp (h.trans (Fintype.card_fin _).symm))
    (fun h => (he.mpr h).trans (Fintype.card_fin _))) ?_
  constructor
  · intro h x y hxy
    obtain ⟨i, rfl⟩ := (BoundedFullSampleChildBasisPencil.rootEquiv P c).surjective x
    obtain ⟨j, rfl⟩ := (BoundedFullSampleChildBasisPencil.rootEquiv P c).surjective y
    exact congrArg (BoundedFullSampleChildBasisPencil.rootEquiv P c) (h (congrArg (Int.castRingHom ℚ) hxy))
  · intro h i j hij
    exact (BoundedFullSampleChildBasisPencil.rootEquiv P c).injective (h (Int.cast_injective hij))

end LeanCanny.Encoding.BoundedFullSampleChildPencilSource
