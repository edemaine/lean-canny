/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PrimitivePairConstruction
public import LeanCanny.Algebra.ScaledSquarefree

/-! # Integer annihilants closed under the canonical primitive-pair operation -/

@[expose] public section

namespace LeanCanny.Algebra
open Polynomial

structure SeparableIntegerPolynomial where
  polynomial : ℤ[X]
  separable : (polynomial.map (Int.castRingHom ℚ)).Separable

namespace SeparableIntegerPolynomial

theorem separable_in_field {L : Type*} [Field L] [CharZero L] (p : SeparableIntegerPolynomial) :
    (p.polynomial.map (Int.castRingHom L)).Separable := by
  have h := (Polynomial.separable_map (Rat.castHom L)).mpr p.separable
  have hc : (Rat.castHom L).comp (Int.castRingHom ℚ) = Int.castRingHom L := by ext z; simp
  simpa only [Polynomial.map_map, hc] using h

theorem ne_zero (p : SeparableIntegerPolynomial) : p.polynomial ≠ 0 :=
  (Polynomial.map_ne_zero_iff (show Function.Injective (Int.castRingHom ℚ) from Int.cast_injective)).mp p.separable.ne_zero

noncomputable def squarefree (p : ℤ[X]) (hp : p ≠ 0) : SeparableIntegerPolynomial :=
  ⟨ScaledSquarefree.polynomial p, ScaledSquarefree.separable p hp⟩

noncomputable def combine (p q : SeparableIntegerPolynomial) : SeparableIntegerPolynomial where
  polynomial := cannyResultant p.polynomial q.polynomial (PrimitivePair.select p.polynomial q.polynomial)
  separable := (PrimitivePair.integer_separable_iff_separating p.polynomial q.polynomial _
    (p.separable_in_field (L := AlgebraicClosure ℚ)) (q.separable_in_field (L := AlgebraicClosure ℚ))
    (IsAlgClosed.splits _) (IsAlgClosed.splits _)).mpr
      (PrimitivePair.select_spec p.polynomial q.polynomial
        (p.separable_in_field (L := AlgebraicClosure ℚ)) (q.separable_in_field (L := AlgebraicClosure ℚ))
        (IsAlgClosed.splits _) (IsAlgClosed.splits _)).2

theorem combine_degree (p q : SeparableIntegerPolynomial) :
    (combine p q).polynomial.natDegree = p.polynomial.natDegree * q.polynomial.natDegree :=
  PrimitivePair.resultant_natDegree _ _ _
    (p.separable_in_field (L := AlgebraicClosure ℚ)) (q.separable_in_field (L := AlgebraicClosure ℚ))
    (IsAlgClosed.splits _) (IsAlgClosed.splits _)

variable {L : Type*} [Field L] [CharZero L] [IsAlgClosed L]

noncomputable def decode (p q : SeparableIntegerPolynomial) (theta : L) : L × L :=
  PrimitivePair.decodeInteger p.polynomial q.polynomial (PrimitivePair.select p.polynomial q.polynomial) theta

noncomputable def encode (p q : SeparableIntegerPolynomial) (a b : L) : L :=
  shear (PrimitivePair.select p.polynomial q.polynomial) (a, b)

theorem decode_root (p q : SeparableIntegerPolynomial) (theta : L)
    (ht : (combine p q).polynomial.eval₂ (Int.castRingHom L) theta = 0) :
    p.polynomial.eval₂ (Int.castRingHom L) (decode p q theta).1 = 0 ∧
    q.polynomial.eval₂ (Int.castRingHom L) (decode p q theta).2 = 0 ∧
    encode p q (decode p q theta).1 (decode p q theta).2 = theta := by
  have h := PrimitivePair.decodeInteger_root p.polynomial q.polynomial _ theta p.ne_zero q.separable_in_field
    (IsAlgClosed.splits _) (PrimitivePair.select_spec p.polynomial q.polynomial
      p.separable_in_field q.separable_in_field (IsAlgClosed.splits _) (IsAlgClosed.splits _)).2 ht
  exact ⟨h.1, h.2.1, h.2.2.1⟩

theorem encode_root (p q : SeparableIntegerPolynomial) (a b : L)
    (ha : p.polynomial.eval₂ (Int.castRingHom L) a = 0) (hb : q.polynomial.eval₂ (Int.castRingHom L) b = 0) :
    (combine p q).polynomial.eval₂ (Int.castRingHom L) (encode p q a b) = 0 :=
  PrimitivePair.integer_shear_root _ _ _ a b q.separable_in_field (IsAlgClosed.splits _) ha hb

theorem decode_encode (p q : SeparableIntegerPolynomial) (a b : L)
    (ha : p.polynomial.eval₂ (Int.castRingHom L) a = 0) (hb : q.polynomial.eval₂ (Int.castRingHom L) b = 0) :
    decode p q (encode p q a b) = (a, b) :=
  PrimitivePair.decodeInteger_shear _ _ _ a b p.ne_zero q.separable_in_field (IsAlgClosed.splits _)
    (PrimitivePair.select_spec p.polynomial q.polynomial p.separable_in_field q.separable_in_field
      (IsAlgClosed.splits _) (IsAlgClosed.splits _)).2 ha hb

end SeparableIntegerPolynomial
end LeanCanny.Algebra
