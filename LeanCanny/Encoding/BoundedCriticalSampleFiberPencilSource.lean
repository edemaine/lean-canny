/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleFiberPencilBounds
public import LeanCanny.Algebra.FunctionBasisPencilMap

/-! # Identifying the native integer determinant with the root-function pencil

When the context's binary count is the actual fiber-root count, the
native polynomial matrix maps to the selected basis pencil. The index cast
changes no determinant. This connects the modular coefficient evaluator to
the separation criterion, including a context with no fiber roots.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleFiberPencilSource
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedCriticalSampleFiberWeightedMoments BoundedCriticalSampleFiberPencilEntries
open scoped Classical

theorem dimension_context (c : List Bool) (n : ℕ) (m : List Bool) (t : ℕ) :
    dimension (context c n m t) = n := by
  simp only [dimension, context, count, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

noncomputable def indexEquiv (P : Readers) (F : BoundedAlgebraicSlice.Family) (c m : List Bool) (t : ℕ) :
    Fin (BoundedCriticalSampleSlice.RootCount.count P F c) ≃
      Fin (dimension (context c (BoundedCriticalSampleSlice.RootCount.count P F c) m t)) :=
  finCongr (dimension_context c (BoundedCriticalSampleSlice.RootCount.count P F c) m t).symm

theorem indexEquiv_val (P : Readers) (F : BoundedAlgebraicSlice.Family) (c m : List Bool) (t : ℕ) (i : Fin (BoundedCriticalSampleSlice.RootCount.count P F c)) :
    (indexEquiv P F c m t i).val = i.val := rfl

attribute [local irreducible] BoundedCriticalSampleFiberWeightedMoments.entry BoundedCriticalSampleFiberPencilEntries.gram

theorem matrix_packet (P : Readers) (F : BoundedAlgebraicSlice.Family) (c m : List Bool) (t : ℕ) :
    ((matrix P F (context c (BoundedCriticalSampleSlice.RootCount.count P F c) m t)).submatrix
      (indexEquiv P F c m t) (indexEquiv P F c m t)).map (Polynomial.mapRingHom (Int.castRingHom ℚ)) =
      BoundedCriticalSampleFiberBasisPencil.pencil P F c
        (fun x => (BoundedCriticalSampleFiberRootHash.integerValue P F c (Nat.fromBitsLE m + 1) t x : ℚ)) := by
  apply Matrix.ext
  intro i j
  let b := context c (BoundedCriticalSampleSlice.RootCount.count P F c) m t
  let q := pair b (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))
  have hg : (gram P F q : ℚ) = BoundedCriticalSampleFiberBasisGram.gram P F c i j := by
    have hq : gramQuery q = pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)) := by
      simp only [gramQuery, q, b, context, BoundedCriticalSampleFiberWeightedMoments.original, pairFst_pair, pairSnd_pair]
    rw [gram, hq]
    exact BoundedCriticalSampleFiberBasisGram.entry_packet P F c i j
  have hw := BoundedCriticalSampleFiberWeightedMoments.entry_packet P F c m t i j
  simp only [Matrix.map_apply, Matrix.submatrix_apply, matrix, indexEquiv_val,
    Polynomial.coe_mapRingHom, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_X, Int.coe_castRingHom]
  change C (gram P F q : ℚ) * X - C (entry P F q : ℚ) = _
  rw [hg, hw]
  rfl

theorem determinant_packet (P : Readers) (F : BoundedAlgebraicSlice.Family) (c m : List Bool) (t : ℕ) :
    (matrix P F (context c (BoundedCriticalSampleSlice.RootCount.count P F c) m t)).det.map (Int.castRingHom ℚ) =
      (BoundedCriticalSampleFiberBasisPencil.pencil P F c
        (fun x => (BoundedCriticalSampleFiberRootHash.integerValue P F c (Nat.fromBitsLE m + 1) t x : ℚ))).det := by
  let A := matrix P F (context c (BoundedCriticalSampleSlice.RootCount.count P F c) m t)
  let e := indexEquiv P F c m t
  have hm : ((A.submatrix e e).map (Polynomial.mapRingHom (Int.castRingHom ℚ))).det =
      (A.submatrix e e).det.map (Int.castRingHom ℚ) :=
    ((Polynomial.mapRingHom (Int.castRingHom ℚ)).map_det _).symm
  have hd := congrArg Matrix.det (matrix_packet P F c m t)
  change ((A.submatrix e e).map (Polynomial.mapRingHom (Int.castRingHom ℚ))).det = _ at hd
  rw [hm, Matrix.det_submatrix_equiv_self] at hd
  exact hd

theorem real_rootCount_eq_count_iff (P : Readers) (F : BoundedAlgebraicSlice.Family) (c m : List Bool) (t : ℕ) :
    (((matrix P F (context c (BoundedCriticalSampleSlice.RootCount.count P F c) m t)).det.map (Int.castRingHom ℝ)).roots.toFinset).card =
      BoundedCriticalSampleSlice.RootCount.count P F c ↔
        Function.Injective (BoundedCriticalSampleFiberRootHash.integerValue P F c (Nat.fromBitsLE m + 1) t) := by
  have hcomp : (Rat.castHom ℝ).comp (Int.castRingHom ℚ) = Int.castRingHom ℝ := by
    ext z
    simp
  have hm := congrArg (fun p : ℚ[X] => p.map (Rat.castHom ℝ)) (determinant_packet P F c m t)
  rw [Polynomial.map_map, hcomp, BoundedCriticalSampleFiberBasisPencil.pencil_eq] at hm
  rw [hm]
  have he := FunctionBasisPencil.mapped_rootCount_eq_card_iff (Rat.castHom ℝ) (Rat.castHom ℝ).injective
    (BoundedCriticalSampleFiberBasisPencil.square P F c)
    ((fun x => (BoundedCriticalSampleFiberRootHash.integerValue P F c (Nat.fromBitsLE m + 1) t x : ℚ)) ∘
      BoundedCriticalSampleFiberBasisPencil.rootEquiv P F c) (BoundedCriticalSampleFiberBasisPencil.square_det_ne_zero P F c)
  refine Iff.trans (Iff.intro (fun h => he.mp (h.trans (Fintype.card_fin _).symm))
    (fun h => (he.mpr h).trans (Fintype.card_fin _))) ?_
  constructor
  · intro h x y hxy
    obtain ⟨i, rfl⟩ := (BoundedCriticalSampleFiberBasisPencil.rootEquiv P F c).surjective x
    obtain ⟨j, rfl⟩ := (BoundedCriticalSampleFiberBasisPencil.rootEquiv P F c).surjective y
    exact congrArg (BoundedCriticalSampleFiberBasisPencil.rootEquiv P F c) (h (congrArg (Int.castRingHom ℚ) hxy))
  · intro h i j hij
    exact (BoundedCriticalSampleFiberBasisPencil.rootEquiv P F c).injective (h (Int.cast_injective hij))

end LeanCanny.Encoding.BoundedCriticalSampleFiberPencilSource
