/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayUniversalDenominators

/-! # Specializing the universal numerator and denominator

Positive input degrees are at most the Macaulay level. The usual exponent
width therefore suffices to reconstruct any homogeneous system and to
specialize both universal determinants to the actual Macaulay determinants.
Universal polynomial divisibility can then be specialized even when actual
denominators acquire new common factors.
-/

@[expose] public section

namespace LeanCanny.Algebra.MacaulayUniversal
open scoped BigOperators Classical
variable {n : ℕ} {R : Type*} [CommRing R]

theorem degree_le_level (d : Fin n → ℕ) (hd : ∀ i, 0 < d i) (i : Fin n) : d i ≤ Macaulay.level d := by
  have hsum : d i - 1 ≤ ∑ j, (d j - 1) :=
    Finset.single_le_sum (f := fun j => d j - 1) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hi := hd i
  unfold Macaulay.level
  omega

theorem degree_lt_width (d : Fin n → ℕ) (W : ℕ) (hd : ∀ i, 0 < d i) (hW : Macaulay.level d < 2 ^ W) :
    ∀ i, d i < 2 ^ W := fun i => (degree_le_level d hd i).trans_lt hW

theorem specialize_system_of_level (d : Fin n → ℕ) (W : ℕ) (p : Fin n → MvPolynomial (Fin n) R)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i) (hW : Macaulay.level d < 2 ^ W) (i : Fin n) :
    (system (R := R) d W (Equiv.refl _) i).map (MvPolynomial.eval (fun v => (p v.1).coeff v.2)) = p i := by
  apply specialize_system d W p hp
  intro j m hm k
  exact ((Finsupp.le_degree k m).trans ((MvPolynomial.le_totalDegree hm).trans (hp j).totalDegree_le)).trans_lt
    (degree_lt_width d W hd hW j)

theorem specialize_denominator (d : Fin n → ℕ) (W : ℕ) (p : Fin n → MvPolynomial (Fin n) R)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i) (hW : Macaulay.level d < 2 ^ W) :
    MvPolynomial.eval (fun v => (p v.1).coeff v.2) (denominator (R := R) d W (Equiv.refl _)) =
      (Macaulay.extraneousMinor p d W).det := by
  rw [denominator, Macaulay.det_extraneousMinor_map]
  have hs : (fun i => (system (R := R) d W (Equiv.refl _) i).map
      (MvPolynomial.eval (fun v => (p v.1).coeff v.2))) = p := by
    funext i
    exact specialize_system_of_level d W p hp hd hW i
  rw [hs]
  rfl

theorem specialize_numerator (d : Fin n → ℕ) (W : ℕ) (p : Fin n → MvPolynomial (Fin n) R)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i) (hW : Macaulay.level d < 2 ^ W) :
    MvPolynomial.eval (fun v => (p v.1).coeff v.2) (numerator (R := R) d W (Equiv.refl _)) =
      (Macaulay.activeMinor p d W).det := by
  rw [numerator, Macaulay.det_activeMinor_map]
  have hs : (fun i => (system (R := R) d W (Equiv.refl _) i).map
      (MvPolynomial.eval (fun v => (p v.1).coeff v.2))) = p := by
    funext i
    exact specialize_system_of_level d W p hp hd hW i
  rw [hs]
  rfl

theorem specialize_divisibility (d : Fin n → ℕ) (W : ℕ) (p : Fin n → MvPolynomial (Fin n) R)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i) (hW : Macaulay.level d < 2 ^ W)
    (hdiv : denominator (R := R) d W (Equiv.refl _) ∣ numerator (R := R) d W (Equiv.refl _)) :
    (Macaulay.extraneousMinor p d W).det ∣ (Macaulay.activeMinor p d W).det := by
  obtain ⟨q, hq⟩ := hdiv
  refine ⟨MvPolynomial.eval (fun v => (p v.1).coeff v.2) q, ?_⟩
  have h := congrArg (MvPolynomial.eval (fun v => (p v.1).coeff v.2)) hq
  rw [specialize_numerator d W p hp hd hW, map_mul, specialize_denominator d W p hp hd hW] at h
  exact h

end LeanCanny.Algebra.MacaulayUniversal
