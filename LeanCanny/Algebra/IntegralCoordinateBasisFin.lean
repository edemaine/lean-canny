/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCoordinateBasis

/-! # Fixed-width indices for bounded scalar-prefix representatives

For a power-of-two common scalar degree, the monomial basis is exactly the
fixed-width exponent box. Reading a canonical coefficient asks the original
integer regular-representation matrix for column zero.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCoordinateBasis
open scoped Classical BigOperators
open LeanCanny.Encoding FixedWidthPolynomial
set_option backward.isDefEq.respectTransparency false
variable {A : Type*} [CommRing A] {m B : ℕ}

theorem index_card (m N : ℕ) : Fintype.card (Fin m → Fin N) = N ^ m := by simp

def zeroFin (m B : ℕ) : Fin (count m B) := ⟨0, pow_pos (Nat.two_pow_pos B) m⟩

def boxEquiv (m B : ℕ) : (Fin m → Fin (2 ^ B)) ≃ Fin (count m B) :=
  finFunctionFinEquiv.trans (finCongr (rfl : (2 ^ B) ^ m = count m B))

theorem zero_rank : boxEquiv m B (zeroIndex m (2 ^ B) (Nat.two_pow_pos B)) = zeroFin m B := by
  apply Fin.ext
  change (finFunctionFinEquiv (zeroIndex m (2 ^ B) (Nat.two_pow_pos B)) : ℕ) = 0
  exact (finFunctionFinEquiv_apply (zeroIndex m (2 ^ B) (Nat.two_pow_pos B))).trans (by simp [zeroIndex])

noncomputable def finBasis (b : IntegralCoordinateBasis A m (2 ^ B)) :
    Module.Basis (Fin (count m B)) ℤ A := b.basis.reindex (boxEquiv m B)

theorem finBasis_zero (b : IntegralCoordinateBasis A m (2 ^ B)) : b.finBasis (zeroFin m B) = 1 := by
  rw [finBasis, Module.Basis.reindex_apply, ← zero_rank, Equiv.symm_apply_apply]
  exact b.basis_zero (Nat.two_pow_pos B)

theorem coefficient_finMatrix (b : IntegralCoordinateBasis A m (2 ^ B)) (a : A) (r : Fin (count m B)) :
    (b.representative a).coeff (vector m B r) = Algebra.leftMulMatrix b.finBasis a r (zeroFin m B) := by
  have HV : vector m B r = exponent ((boxEquiv m B).symm r) := rfl
  rw [HV, representative_coefficient, Algebra.leftMulMatrix_eq_repr_mul, finBasis_zero, mul_one]
  rfl

end LeanCanny.Algebra.IntegralCoordinateBasis
