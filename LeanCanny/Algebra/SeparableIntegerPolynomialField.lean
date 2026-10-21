/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SeparableIntegerPolynomial

/-! # Primitive-pair recovery in arbitrary characteristic-zero fields

Embedding into an algebraic closure supplies splitting. Integer polynomial
evaluation and the explicit rational formulas commute with that embedding,
so soundness and completeness descend to the original field, including ℝ.
-/

@[expose] public section

namespace LeanCanny.Algebra.SeparableIntegerPolynomial
open Polynomial

theorem map_integer_eval₂ {L M : Type*} [Field L] [Field M] (f : L →+* M) (p : ℤ[X]) (x : L) :
    f (p.eval₂ (Int.castRingHom L) x) = p.eval₂ (Int.castRingHom M) (f x) := by
  rw [Polynomial.hom_eval₂]
  congr 1
  ext z
  simp

theorem map_decode {L M : Type*} [Field L] [Field M] (f : L →+* M) (p q : SeparableIntegerPolynomial) (theta : L) :
    (f (decode p q theta).1, f (decode p q theta).2) = decode p q (f theta) := by
  simp only [decode, PrimitivePair.decodeInteger, map_div₀, map_integer_eval₂]

theorem map_encode {L M : Type*} [Field L] [Field M] (f : L →+* M) (p q : SeparableIntegerPolynomial) (a b : L) :
    f (encode p q a b) = encode p q (f a) (f b) := by
  simp only [encode, shear, map_add, map_mul, map_natCast]

variable {L : Type*} [Field L] [CharZero L]

theorem denominator_ne_zero_over (p q : SeparableIntegerPolynomial) (theta : L)
    (ht : (combine p q).polynomial.eval₂ (Int.castRingHom L) theta = 0) :
    (PrimitivePair.denominator p.polynomial q.polynomial (PrimitivePair.select p.polynomial q.polynomial)).eval₂
      (Int.castRingHom L) theta ≠ 0 := by
  let f : L →+* AlgebraicClosure L := algebraMap L (AlgebraicClosure L)
  have ht' : (combine p q).polynomial.eval₂ (Int.castRingHom (AlgebraicClosure L)) (f theta) = 0 := by
    rw [← map_integer_eval₂, ht, map_zero]
  have hr := PrimitivePair.decodeInteger_root p.polynomial q.polynomial _ (f theta) p.ne_zero
    q.separable_in_field (IsAlgClosed.splits _) (PrimitivePair.select_spec p.polynomial q.polynomial
      p.separable_in_field q.separable_in_field (IsAlgClosed.splits _) (IsAlgClosed.splits _)).2 ht'
  intro hz
  apply hr.2.2.2
  rw [← map_integer_eval₂ f, hz, map_zero]

theorem decode_root_over (p q : SeparableIntegerPolynomial) (theta : L)
    (ht : (combine p q).polynomial.eval₂ (Int.castRingHom L) theta = 0) :
    p.polynomial.eval₂ (Int.castRingHom L) (decode p q theta).1 = 0 ∧
    q.polynomial.eval₂ (Int.castRingHom L) (decode p q theta).2 = 0 ∧
    encode p q (decode p q theta).1 (decode p q theta).2 = theta := by
  let f : L →+* AlgebraicClosure L := algebraMap L (AlgebraicClosure L)
  have ht' : (combine p q).polynomial.eval₂ (Int.castRingHom (AlgebraicClosure L)) (f theta) = 0 := by
    rw [← map_integer_eval₂, ht, map_zero]
  have hr := decode_root p q (f theta) ht'
  rw [← map_decode f p q theta] at hr
  refine ⟨?_, ?_, ?_⟩
  · apply f.injective
    rw [map_integer_eval₂, map_zero]
    exact hr.1
  · apply f.injective
    rw [map_integer_eval₂, map_zero]
    exact hr.2.1
  · apply f.injective
    rw [map_encode]
    exact hr.2.2

theorem encode_root_over (p q : SeparableIntegerPolynomial) (a b : L)
    (ha : p.polynomial.eval₂ (Int.castRingHom L) a = 0) (hb : q.polynomial.eval₂ (Int.castRingHom L) b = 0) :
    (combine p q).polynomial.eval₂ (Int.castRingHom L) (encode p q a b) = 0 := by
  let f : L →+* AlgebraicClosure L := algebraMap L (AlgebraicClosure L)
  apply f.injective
  rw [map_integer_eval₂, map_encode, map_zero]
  apply encode_root p q
  · rw [← map_integer_eval₂, ha, map_zero]
  · rw [← map_integer_eval₂, hb, map_zero]

theorem decode_encode_over (p q : SeparableIntegerPolynomial) (a b : L)
    (ha : p.polynomial.eval₂ (Int.castRingHom L) a = 0) (hb : q.polynomial.eval₂ (Int.castRingHom L) b = 0) :
    decode p q (encode p q a b) = (a, b) := by
  let f : L →+* AlgebraicClosure L := algebraMap L (AlgebraicClosure L)
  have ha' : p.polynomial.eval₂ (Int.castRingHom (AlgebraicClosure L)) (f a) = 0 := by
    rw [← map_integer_eval₂, ha, map_zero]
  have hb' : q.polynomial.eval₂ (Int.castRingHom (AlgebraicClosure L)) (f b) = 0 := by
    rw [← map_integer_eval₂, hb, map_zero]
  have hm := map_decode f p q (encode p q a b)
  rw [map_encode, decode_encode p q (f a) (f b) ha' hb'] at hm
  exact Prod.ext (f.injective (congrArg Prod.fst hm)) (f.injective (congrArg Prod.snd hm))

end LeanCanny.Algebra.SeparableIntegerPolynomial
