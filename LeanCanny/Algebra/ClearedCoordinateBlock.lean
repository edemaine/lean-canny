/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CommonDenominatorSpecialization
public import LeanCanny.Algebra.CoordinateBlockSpecialization

/-! # Integral frozen coordinate blocks with a common denominator

Free coordinates have numerator q*X; frozen coordinates have numerator H.
Clearing the original total-degree allowance preserves the free spatial
degree. A Fermat-leading source retains pure free powers with coefficient
a*q^D; frozen pure powers enter only the lower constant part.
-/

@[expose] public section
namespace LeanCanny.Algebra.ClearedCoordinateBlock
open MvPolynomial CommonDenominatorSpecialization
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {n dim : ℕ} {R : Type*} [CommRing R]

noncomputable def coordinate (q : R) (H : ℕ → R) (offset dim i : ℕ) : MvPolynomial (Fin dim) R :=
  if hi : offset ≤ i ∧ i < offset + dim then C q * X ⟨i - offset, by omega⟩ else C (H i)

noncomputable def specialize (D : ℕ) (q : R) (H : ℕ → R) (offset dim : ℕ) :
    MvPolynomial (Fin n) R →+ MvPolynomial (Fin dim) R :=
  clear D q (fun i => coordinate q H offset dim i.val)

attribute [local irreducible] CommonDenominatorSpecialization.clear

theorem coordinate_degree (q : R) (H : ℕ → R) (offset dim i : ℕ) :
    (coordinate q H offset dim i).totalDegree ≤ 1 := by
  unfold coordinate
  split_ifs
  · apply (totalDegree_mul _ _).trans
    rw [totalDegree_C, Nat.zero_add]
    simpa [MvPolynomial.X] using totalDegree_monomial_le (Finsupp.single (⟨i - offset, by omega⟩ : Fin dim) 1) (1 : R)
  · simp

theorem degree (D : ℕ) (q : R) (H : ℕ → R) (offset dim : ℕ) (p : MvPolynomial (Fin n) R) :
    (specialize D q H offset dim p).totalDegree ≤ p.totalDegree := by
  change (clear D q (fun i : Fin n => coordinate q H offset dim i.val) p).totalDegree ≤ p.totalDegree
  exact CommonDenominatorSpecialization.degree D q (fun i : Fin n => coordinate q H offset dim i.val)
    (fun i => coordinate_degree q H offset dim i.val) p

theorem sum_powers (q : R) (H : ℕ → R) (offset dim D : ℕ) (hfit : offset + dim ≤ n) :
    (∑ i : Fin n, coordinate q H offset dim i.val ^ D) =
      C (q ^ D) * ∑ j : Fin dim, X j ^ D +
        C (CoordinateBlockSpecialization.frozenPower (n := n) H offset dim D) := by
  have HV (i : Fin n) : coordinate q H offset dim i.val ^ D =
      C (q ^ D) * (if hi : offset ≤ i.val ∧ i.val < offset + dim then
        (X ⟨i.val - offset, by omega⟩ : MvPolynomial (Fin dim) R) ^ D else 0) +
      C (if offset ≤ i.val ∧ i.val < offset + dim then 0 else H i.val ^ D) := by
    unfold coordinate
    split_ifs <;> simp [mul_pow]
  simp only [HV, Finset.sum_add_distrib, ← Finset.mul_sum, ← map_sum]
  rw [CoordinateBlockSpecialization.sum_free offset dim D hfit]
  rfl

noncomputable def lower (D : ℕ) (q : R) (H : ℕ → R) (offset dim : ℕ)
    (low : MvPolynomial (Fin n) R) (a : R) : MvPolynomial (Fin dim) R :=
  specialize D q H offset dim low + C (a * CoordinateBlockSpecialization.frozenPower (n := n) H offset dim D)

theorem source {k : ℕ} (D : ℕ) (q : R) (H : ℕ → R) (offset : ℕ)
    (low : MvPolynomial (Fin (n + 1)) R) (a : R) (hfit : offset + (k + 1) ≤ n + 1) :
    specialize D q H offset (k + 1) (FermatCriticalHomogenization.polynomial low a D) =
      FermatCriticalHomogenization.polynomial (lower D q H offset (k + 1) low a) (a * q ^ D) D := by
  change clear D q _ _ = _
  rw [FermatCriticalHomogenization.polynomial, map_add, CommonDenominatorSpecialization.C_mul, map_sum]
  simp only [CommonDenominatorSpecialization.X_pow, Nat.sub_self, pow_zero, map_one, one_mul]
  rw [sum_powers q H offset (k + 1) D hfit]
  simp only [FermatCriticalHomogenization.polynomial, lower, specialize, map_mul]
  ring

theorem lower_degree (D : ℕ) (q : R) (H : ℕ → R) (offset dim : ℕ)
    (low : MvPolynomial (Fin n) R) (a : R) (hlow : low.totalDegree < D) :
    (lower D q H offset dim low a).totalDegree < D := by
  apply (totalDegree_add _ _).trans_lt
  apply max_lt ((degree D q H offset dim low).trans_lt hlow)
  rw [totalDegree_C]
  omega

noncomputable def point {K : Type*} [Field K] (φ : R →+* K) (q : R) (H : ℕ → R)
    (offset : ℕ) (x : Fin dim → K) (i : Fin n) : K :=
  if hi : offset ≤ i.val ∧ i.val < offset + dim then x ⟨i.val - offset, by omega⟩ else φ (H i.val) / φ q

theorem eval {K : Type*} [Field K] (φ : R →+* K) (D : ℕ) (q : R) (H : ℕ → R)
    (offset : ℕ) (p : MvPolynomial (Fin n) R) (hp : p.totalDegree ≤ D) (hq : φ q ≠ 0)
    (x : Fin dim → K) :
    (specialize D q H offset dim p).eval₂ φ x = φ q ^ D * p.eval₂ φ (point φ q H offset x) := by
  rw [specialize, CommonDenominatorSpecialization.eval φ D q _ p hp hq x]
  congr 2
  funext i
  unfold coordinate point
  split_ifs <;> simp [hq]

end LeanCanny.Algebra.ClearedCoordinateBlock
