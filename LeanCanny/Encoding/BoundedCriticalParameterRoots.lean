/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalRationalCoordinates

/-! # Denominators and injectivity on the native critical parameter roots

Every parameter root decodes to a tuple of coordinate-equation roots. Its
rational denominators are nonzero, and the complete coordinate tuple uniquely
determines the parameter. These facts permit exact filtering by the source.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalParameterRoots
open LeanCanny.ETR LeanCanny.Algebra BoundedFullWriter
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FiniteLeafCoordinateBits.coordinate
  BoundedCriticalRationalCoordinates.coordinate

theorem prepared_count (P : Readers) (c : List Bool) :
    BoundedCriticalRationalCoordinates.count P (BoundedCriticalLeafSource.prepare P c) = P.dim c + 4 := by
  simp only [BoundedCriticalRationalCoordinates.count, BoundedCriticalLeafSource.prepare_source, BoundedCriticalLeafSource.count]

noncomputable def preparedIndex (P : Readers) (c : List Bool) (i : Fin (P.dim c + 4)) :
    Fin (BoundedCriticalRationalCoordinates.count P (BoundedCriticalLeafSource.prepare P c)) := ⟨i.val, by rw [prepared_count]; exact i.isLt⟩

variable {K : Type*} [Field K] [CharZero K]

noncomputable def treeDecode (P : Readers) (c : List Bool) (theta : K) :
    Fin (BoundedCriticalRationalCoordinates.count P (BoundedCriticalLeafSource.prepare P c)) → K :=
  FiniteAnnihilatorTree.decode
    (fun j => (BoundedCriticalLeafSource.family P).polynomial
      (pair (BoundedCriticalLeafSource.prepare P c) (BinaryNatCode.encode j)))
    (BoundedCriticalRationalCoordinates.count P (BoundedCriticalLeafSource.prepare P c)) (BoundedCriticalRationalCoordinates.nonzero P (BoundedCriticalLeafSource.prepare P c)) theta

noncomputable def decode (P : Readers) (c : List Bool) (theta : K) : Fin (P.dim c + 4) → K :=
  fun i => (BoundedCriticalRationalCoordinates.coordinate P (pair c (BinaryNatCode.encode i.val))).eval theta

theorem coordinate_spec (P : Readers) (c : List Bool) (theta : K)
    (ht : (BoundedCriticalRationalCoordinates.parameter P c).eval₂ (Int.castRingHom K) theta = 0) (i : Fin (P.dim c + 4)) :
    (BoundedCriticalRationalCoordinates.coordinate P (pair c (BinaryNatCode.encode i.val))).denominator.eval₂ (Int.castRingHom K) theta ≠ 0 ∧
      decode P c theta i = treeDecode P c theta (preparedIndex P c i) := by
  have H := FiniteLeafCoordinateBits.finite_decode_spec (BoundedCriticalLeafSource.family P)
    (BoundedCriticalRationalCoordinates.count P) (BoundedCriticalRationalCoordinates.degreeBound P) (BoundedCriticalRationalCoordinates.height P) (BoundedCriticalRationalCoordinates.nonzero P) (BoundedCriticalRationalCoordinates.degree_le P) (BoundedCriticalRationalCoordinates.height_le P)
    (BoundedCriticalLeafSource.prepare P c) (preparedIndex P c i) theta ht
  simpa only [BoundedCriticalRationalCoordinates.coordinate, Function.comp_apply, BoundedCriticalRationalCoordinates.prepareCoordinate, pairFst_pair, pairSnd_pair,
    BoundedCriticalRationalCoordinates.rawCoordinate, preparedIndex, decode, treeDecode] using H

theorem denominator_ne_zero (P : Readers) (c : List Bool) (theta : K)
    (ht : (BoundedCriticalRationalCoordinates.parameter P c).eval₂ (Int.castRingHom K) theta = 0) (i : Fin (P.dim c + 4)) :
    (BoundedCriticalRationalCoordinates.coordinate P (pair c (BinaryNatCode.encode i.val))).denominator.eval₂ (Int.castRingHom K) theta ≠ 0 :=
  (coordinate_spec P c theta ht i).1

theorem decode_injective (P : Readers) (c : List Bool) (theta eta : K)
    (ht : (BoundedCriticalRationalCoordinates.parameter P c).eval₂ (Int.castRingHom K) theta = 0)
    (he : (BoundedCriticalRationalCoordinates.parameter P c).eval₂ (Int.castRingHom K) eta = 0)
    (hd : decode P c theta = decode P c eta) : theta = eta := by
  have htree : treeDecode P c theta = treeDecode P c eta := by
    funext j
    let i : Fin (P.dim c + 4) := ⟨j.val, by rw [← prepared_count P c]; exact j.isLt⟩
    have hj : preparedIndex P c i = j := Fin.ext rfl
    rw [← hj, ← (coordinate_spec P c theta ht i).2, ← (coordinate_spec P c eta he i).2]
    exact congrFun hd i
  let p := fun j => (BoundedCriticalLeafSource.family P).polynomial
    (pair (BoundedCriticalLeafSource.prepare P c) (BinaryNatCode.encode j))
  let n := BoundedCriticalRationalCoordinates.count P (BoundedCriticalLeafSource.prepare P c)
  let hp := BoundedCriticalRationalCoordinates.nonzero P (BoundedCriticalLeafSource.prepare P c)
  calc
    theta = FiniteAnnihilatorTree.encode p n hp (treeDecode P c theta) :=
      (FiniteAnnihilatorTree.encode_decode p n hp theta ht).symm
    _ = FiniteAnnihilatorTree.encode p n hp (treeDecode P c eta) := congrArg _ htree
    _ = eta := FiniteAnnihilatorTree.encode_decode p n hp eta he

end LeanCanny.Encoding.BoundedCriticalParameterRoots
