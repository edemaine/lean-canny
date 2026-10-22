/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ValidatedPolynomialDegree
public import LeanCanny.Computation.PolyTimeBinaryNat

/-! # Reusable readers for polynomials with space-computed degrees

A checked context turns native space coefficient and degree computations into
the exact FP metadata interface used by subsequent algebraic routines. The
height bound is inherited from the original input, including invalid contexts.
-/

@[expose] public section

namespace LeanCanny.Algebra.ValidatedDegreeBits
open Polynomial
open LeanCanny.Encoding LeanCanny.Computation
open SeparableBits (Family Readers)
attribute [local irreducible] BinaryNat.normalize

noncomputable def family (F : Family) : Family where
  polynomial := checked F.polynomial
  height c := F.height (pairFst c)
  coefficient_bound := checked_bound F.polynomial F.height F.coefficient_bound

noncomputable def readers (F : Family) (H : BinaryFn F.height)
    (E : SpaceFunction (coefficient F.polynomial))
    (D : SpaceFunction (fun c => BinaryNatCode.encode (F.polynomial c).natDegree)) : Readers (family F) where
  degree c := BinaryNat.normalize (pairSnd c)
  height c := BinaryNatCode.encode (F.height (pairFst c))
  coefficient := coefficient (checked F.polynomial)
  degreeFP := mem_FP_comp pairSnd_mem_FP BinaryNat.normalize_mem_FP
  heightFP := mem_FP_comp pairFst_mem_FP H.bits_mem_FP
  degree_eq c := by
    simp only [family, checked_degree, BinaryNat.normalize_eq_bits]
    rfl
  height_eq _ := rfl
  coefficient_eq q k := by
    simp only [coefficient, context, modulus, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    rfl
  evaluator := evaluator F.polynomial E D

theorem family_packet (F : Family) (c : List Bool) :
    (family F).polynomial (pair c (BinaryNatCode.encode (F.polynomial c).natDegree)) = F.polynomial c :=
  checked_packet F.polynomial c

theorem family_separable {L : Type*} [Field L] [CharZero L] (F : Family)
    (hp : ∀ c, ((F.polynomial c).map (Int.castRingHom L)).Separable) (c : List Bool) :
    (((family F).polynomial c).map (Int.castRingHom L)).Separable := checked_separable F.polynomial hp c

theorem family_ne_zero (F : Family) (hp : ∀ c, F.polynomial c ≠ 0) (c : List Bool) :
    (family F).polynomial c ≠ 0 := by
  change checked F.polynomial c ≠ 0
  by_cases h : valid F.polynomial c
  · rw [checked, ite_eq_left h]
    exact hp _
  · rw [checked, ite_eq_right h]
    exact (Polynomial.map_ne_zero_iff (show Function.Injective (Int.castRingHom ℚ) from Int.cast_injective)).mp
      (fallback_separable (L := ℚ) _).ne_zero

end LeanCanny.Algebra.ValidatedDegreeBits
