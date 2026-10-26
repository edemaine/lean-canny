/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.EffectiveSublevelComponents

/-! # Positive perturbations inside the explicit component gap

Any set between the original zeros and their safe sublevel has the same
component relation on those zeros. A dyadic perturbation coefficient keeps
a bounded nonnegative penalty within half that gap, uniformly for every
chosen level in the upper half of the interval.
-/

@[expose] public section
namespace LeanCanny.Geometry.BoundedPositivePerturbation
open MvPolynomial Set LeanCanny.Algebra
open scoped BigOperators

variable {n : ℕ}

def exponent (n D b r : ℕ) : ℕ := GeneralCriticalValueBounds.exponent n D b + r + 1

noncomputable def coefficient (n D b r : ℕ) : ℝ := InfinitesimalSign.dyadic (exponent n D b r)

theorem coefficient_pos (n D b r : ℕ) : 0 < coefficient n D b r := by
  unfold coefficient InfinitesimalSign.dyadic
  positivity

theorem coefficient_mul_pow (n D b r : ℕ) :
    coefficient n D b r * 2 ^ r = GeneralCriticalValueBounds.level n D b / 2 := by
  simp only [coefficient, exponent, GeneralCriticalValueBounds.level, InfinitesimalSign.dyadic,
    pow_add, pow_succ]
  field_simp

theorem component_iff_between (p : MvPolynomial (Fin n) ℤ) (D b : ℕ) (hD : p.totalDegree ≤ D)
    (hpos : 0 < D) (hp : MvMass.mass p ≤ 2 ^ b)
    (hnonneg : ∀ x : Fin n → ℝ, 0 ≤ p.eval₂ (Int.castRingHom ℝ) x)
    (hsublevel : ∀ e : ℝ, IsCompact {x : Fin n → ℝ | p.eval₂ (Int.castRingHom ℝ) x ≤ e})
    (A : Set (Fin n → ℝ)) (hzero : {z | p.eval₂ (Int.castRingHom ℝ) z = 0} ⊆ A)
    (hupper : A ⊆ {z | p.eval₂ (Int.castRingHom ℝ) z ≤ GeneralCriticalValueBounds.level n D b})
    (x y : Fin n → ℝ) (hx : p.eval₂ (Int.castRingHom ℝ) x = 0)
    (hy : p.eval₂ (Int.castRingHom ℝ) y = 0) :
    y ∈ connectedComponentIn {z | p.eval₂ (Int.castRingHom ℝ) z = 0} x ↔ y ∈ connectedComponentIn A x := by
  constructor
  · exact fun h => connectedComponentIn_mono x hzero h
  · intro h
    apply (EffectiveSublevelComponents.zero_component_iff p D b hD hpos hp hnonneg hsublevel x y hx hy).mpr
    exact connectedComponentIn_mono x hupper h

theorem component_iff_perturbed (p : MvPolynomial (Fin n) ℤ) (D b r : ℕ) (hD : p.totalDegree ≤ D)
    (hpos : 0 < D) (hp : MvMass.mass p ≤ 2 ^ b)
    (hnonneg : ∀ x : Fin n → ℝ, 0 ≤ p.eval₂ (Int.castRingHom ℝ) x)
    (hsublevel : ∀ e : ℝ, IsCompact {x : Fin n → ℝ | p.eval₂ (Int.castRingHom ℝ) x ≤ e})
    (h : (Fin n → ℝ) → ℝ) (hh : ∀ x, 0 ≤ h x)
    (hbound : ∀ x : Fin n → ℝ, p.eval₂ (Int.castRingHom ℝ) x = 0 → h x ≤ 2 ^ r)
    (a : ℝ) (ha : GeneralCriticalValueBounds.level n D b / 2 ≤ a)
    (haδ : a ≤ GeneralCriticalValueBounds.level n D b)
    (x y : Fin n → ℝ) (hx : p.eval₂ (Int.castRingHom ℝ) x = 0)
    (hy : p.eval₂ (Int.castRingHom ℝ) y = 0) :
    y ∈ connectedComponentIn {z | p.eval₂ (Int.castRingHom ℝ) z = 0} x ↔
      y ∈ connectedComponentIn {z | p.eval₂ (Int.castRingHom ℝ) z + coefficient n D b r * h z ≤ a} x := by
  apply component_iff_between p D b hD hpos hp hnonneg hsublevel
    {z | p.eval₂ (Int.castRingHom ℝ) z + coefficient n D b r * h z ≤ a} ?_ ?_ x y hx hy
  · intro z hz
    change p.eval₂ (Int.castRingHom ℝ) z + coefficient n D b r * h z ≤ a
    rw [show p.eval₂ (Int.castRingHom ℝ) z = 0 from hz, zero_add]
    exact ((mul_le_mul_of_nonneg_left (hbound z hz) (coefficient_pos n D b r).le).trans_eq
      (coefficient_mul_pow n D b r)).trans ha
  · intro z hz
    exact (le_add_of_nonneg_right (mul_nonneg (coefficient_pos n D b r).le (hh z))).trans (hz.trans haδ)

theorem penalty_bound (N R : ℕ) (x : Fin n → ℝ) (hx : ∀ i, |x i| ≤ 2 ^ R) :
    (∑ i : Fin n, x i ^ N) ≤ 2 ^ (R * N + n.size) := by
  calc
    _ ≤ ∑ _i : Fin n, (2 ^ R : ℝ) ^ N := Finset.sum_le_sum fun i _ =>
      ((le_abs_self _).trans_eq (abs_pow _ _)).trans (pow_le_pow_left₀ (abs_nonneg _) (hx i) _)
    _ = (n : ℝ) * 2 ^ (R * N) := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, ← pow_mul]
    _ ≤ 2 ^ n.size * 2 ^ (R * N) := mul_le_mul_of_nonneg_right (by exact_mod_cast (Nat.lt_size_self n).le) (by positivity)
    _ = _ := by rw [← pow_add, Nat.add_comm]

theorem component_iff_power_perturbed (p : MvPolynomial (Fin n) ℤ) (D b N R : ℕ)
    (hD : p.totalDegree ≤ D) (hpos : 0 < D) (hp : MvMass.mass p ≤ 2 ^ b)
    (hnonneg : ∀ x : Fin n → ℝ, 0 ≤ p.eval₂ (Int.castRingHom ℝ) x)
    (hsublevel : ∀ e : ℝ, IsCompact {x : Fin n → ℝ | p.eval₂ (Int.castRingHom ℝ) x ≤ e})
    (hN : Even N) (hbound : ∀ x : Fin n → ℝ, p.eval₂ (Int.castRingHom ℝ) x = 0 → ∀ i, |x i| ≤ 2 ^ R)
    (a : ℝ) (ha : GeneralCriticalValueBounds.level n D b / 2 ≤ a)
    (haδ : a ≤ GeneralCriticalValueBounds.level n D b)
    (x y : Fin n → ℝ) (hx : p.eval₂ (Int.castRingHom ℝ) x = 0)
    (hy : p.eval₂ (Int.castRingHom ℝ) y = 0) :
    y ∈ connectedComponentIn {z | p.eval₂ (Int.castRingHom ℝ) z = 0} x ↔
      y ∈ connectedComponentIn {z | p.eval₂ (Int.castRingHom ℝ) z +
        coefficient n D b (R * N + n.size) * ∑ i : Fin n, z i ^ N ≤ a} x :=
  component_iff_perturbed p D b (R * N + n.size) hD hpos hp hnonneg hsublevel
    (fun z => ∑ i : Fin n, z i ^ N) (fun z => Finset.sum_nonneg (fun i _ => hN.pow_nonneg (z i)))
    (fun z hz => penalty_bound N R z (hbound z hz)) a ha haδ x y hx hy

end LeanCanny.Geometry.BoundedPositivePerturbation
