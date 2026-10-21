/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FiniteAnnihilatorEquiv
public import LeanCanny.Algebra.BalancedPrimitivePolynomials

/-! # Flattened integer coordinates for finite annihilator root products -/

@[expose] public section

namespace LeanCanny.Algebra.FiniteAnnihilatorTree
open Polynomial BalancedPrimitiveTree
open UnivariateRational

variable (p : ℕ → ℤ[X]) (n : ℕ) (hp : ∀ i < n, p i ≠ 0)

noncomputable def rationalCoordinate (i : Fin n) : Coordinate := flat (leaf p n hp) n.size 0 i.val
noncomputable def numerator (i : Fin n) : ℤ[X] := (rationalCoordinate p n hp i).numerator
noncomputable def denominator (i : Fin n) : ℤ[X] := (rationalCoordinate p n hp i).denominator

theorem coordinate_degree (D : ℕ) (h1 : 1 ≤ D) (hD : ∀ i < n, (p i).natDegree ≤ D) (i : Fin n) :
    (rationalCoordinate p n hp i).degree ≤ (D + 2) ^ (4 * (n + 1)) := by
  have hleaf (j : ℕ) : (leaf p n hp j).polynomial.natDegree ≤ D := by
    by_cases hj : j < n
    · rw [leaf_degree p n hp j hj]
      exact (ScaledSquarefree.polynomial_natDegree_le (p j) (hp j hj)).trans (hD j hj)
    · rw [padding_degree p n hp j (by omega)]
      exact h1
  have he : 2 ^ (n.size + 1) ≤ 4 * (n + 1) := by
    rw [pow_succ]
    have h := width_bound n
    omega
  exact (flat_degree (leaf p n hp) n.size 0 i.val).trans
    ((degreeBudget_le (leaf p n hp) D hleaf n.size 0).trans (Nat.pow_le_pow_right (by omega) he))

variable {K : Type*} [Field K] [CharZero K]

theorem coordinate_spec (theta : K) (ht : (parameter p n hp).polynomial.eval₂ (Int.castRingHom K) theta = 0) (i : Fin n) :
    (denominator p n hp i).eval₂ (Int.castRingHom K) theta ≠ 0 ∧
      (numerator p n hp i).eval₂ (Int.castRingHom K) theta / (denominator p n hp i).eval₂ (Int.castRingHom K) theta =
        decode p n hp theta i := flat_spec (leaf p n hp) n.size 0 i.val theta ht

theorem coordinate_at_solution (x : Fin n → K) (hx : ∀ i, (p i.val).eval₂ (Int.castRingHom K) (x i) = 0) (i : Fin n) :
    (denominator p n hp i).eval₂ (Int.castRingHom K) (encode p n hp x) ≠ 0 ∧
      (numerator p n hp i).eval₂ (Int.castRingHom K) (encode p n hp x) /
        (denominator p n hp i).eval₂ (Int.castRingHom K) (encode p n hp x) = x i := by
  have h := coordinate_spec p n hp (encode p n hp x) (encode_root p n hp x hx) i
  exact ⟨h.1, h.2.trans (congrFun (decode_encode p n hp x hx) i)⟩

noncomputable def rationalDecode (theta : K) : Fin n → K := fun i => (rationalCoordinate p n hp i).eval theta

theorem rationalDecode_eq (theta : K) (ht : (parameter p n hp).polynomial.eval₂ (Int.castRingHom K) theta = 0) :
    rationalDecode p n hp theta = decode p n hp theta :=
  funext fun i => (coordinate_spec p n hp theta ht i).2

end LeanCanny.Algebra.FiniteAnnihilatorTree
