/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.UniformAffineCoordinates
public import LeanCanny.Geometry.RootBranchCount

/-! # Uniform degree budgets count regular affine fibers

The constructed coordinate polynomials bound the actual roots by a product
of degrees. This makes the uniform finite-fiber count quantitative. The
separate hypotheses ensuring regularity still need effective certificates.
-/

@[expose] public section

namespace LeanCanny.Geometry.RegularCoordinateRootCount
open LeanCanny.Algebra
open scoped Classical BigOperators

variable {n : ℕ}

def labelWidth (d : Fin n → ℕ) : ℕ := n * (n + 1) * UniformAffineCoordinates.width d

theorem count_eq_two_pow (d : Fin n → ℕ) :
    UniformAffineCoordinates.count d ^ n = 2 ^ labelWidth d := by
  unfold UniformAffineCoordinates.count FixedWidthPolynomial.count labelWidth
  rw [← pow_mul, ← pow_mul]
  congr 1
  ring

abbrev Fiber (q : Fin n → MvPolynomial (Fin n) (Polynomial ℤ)) (t : ℝ) :=
  {x : Fin n → ℝ | ∀ j, (q j).eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℝ) t) x = 0}

theorem exists_bound (q : Fin n → MvPolynomial (Fin n) (Polynomial ℤ)) (d : Fin n → ℕ)
    (hD : ∀ j, (q j).totalDegree ≤ d j) (hd : ∀ j, 0 < d j) (E b : ℕ)
    (hdegree : ∀ j e, ((q j).coeff e).natDegree ≤ E)
    (hmass : ∀ j e, coefficientMass ((q j).coeff e) ≤ 2 ^ b) :
    ∃ r : Polynomial ℤ, r ≠ 0 ∧ r.natDegree ≤ n * (UniformAffineCoordinates.count d * E) ∧
      ∀ t : ℝ, r.eval₂ (Int.castRingHom ℝ) t ≠ 0 →
        (∀ x : Fiber q t, (fderiv ℝ (fun y => fun j =>
          (q j).eval₂ (Polynomial.eval₂RingHom (Int.castRingHom ℝ) t) y) x.val).IsInvertible) →
        Finite (Fiber q t) ∧ Nat.card (Fiber q t) ≤ UniformAffineCoordinates.count d ^ n := by
  obtain ⟨P, r, hr, hdeg, _, hP, h⟩ :=
    UniformAffineCoordinates.exists_bounded q d hD hd E b hdegree hmass
  refine ⟨r, hr, hdeg, ?_⟩
  intro t ht hregular
  let φ := Polynomial.eval₂RingHom (Int.castRingHom ℝ) t
  have hs := h t ht
  have hbound := RootBranchCount.finite_card_le (fun x : Fiber q t => x.val) Subtype.val_injective
    (fun i => (P i).map φ) hs.1 (fun x i => hs.2 x.val x.property (hregular x) i)
  refine ⟨hbound.1, hbound.2.trans ?_⟩
  calc
    ∏ i, ((P i).map φ).natDegree ≤ ∏ _i : Fin n, UniformAffineCoordinates.count d :=
      Finset.prod_le_prod (fun i _ => Polynomial.natDegree_map_le.trans (hP i).2.1)
    _ = UniformAffineCoordinates.count d ^ n := by simp

/-- Finiteness over an algebraically closed extension suffices for the same
binary label allowance, including fibers with singular real roots. -/
theorem exists_finite_extension_bound {L : Type*} [Field L] [IsAlgClosed L] [Algebra ℝ L]
    (q : Fin n → MvPolynomial (Fin n) (Polynomial ℤ)) (d : Fin n → ℕ)
    (hD : ∀ j, (q j).totalDegree ≤ d j) (hd : ∀ j, 0 < d j) (E b : ℕ)
    (hdegree : ∀ j e, ((q j).coeff e).natDegree ≤ E)
    (hmass : ∀ j e, coefficientMass ((q j).coeff e) ≤ 2 ^ b) :
    ∃ r : Polynomial ℤ, r ≠ 0 ∧ r.natDegree ≤ n * (UniformAffineCoordinates.count d * E) ∧
      ∀ t : ℝ, r.eval₂ (Int.castRingHom ℝ) t ≠ 0 →
        {x : Fin n → L | ∀ j, (q j).eval₂ ((algebraMap ℝ L).comp
          (Polynomial.eval₂RingHom (Int.castRingHom ℝ) t)) x = 0}.Finite →
        Finite (Fiber q t) ∧ Nat.card (Fiber q t) ≤ 2 ^ labelWidth d := by
  obtain ⟨P, r, hr, hdeg, _, hP, h⟩ :=
    UniformAffineCoordinates.exists_bounded_of_finite_extension (L := L) q d hD hd E b hdegree hmass
  refine ⟨r, hr, hdeg, ?_⟩
  intro t ht hfinite
  let φ := Polynomial.eval₂RingHom (Int.castRingHom ℝ) t
  have hs := h t ht
  have hbound := RootBranchCount.finite_card_le (fun x : Fiber q t => x.val) Subtype.val_injective
    (fun i => (P i).map φ) hs.1 (fun x i => hs.2 hfinite x.val x.property i)
  refine ⟨hbound.1, hbound.2.trans ?_⟩
  rw [← count_eq_two_pow]
  calc
    ∏ i, ((P i).map φ).natDegree ≤ ∏ _i : Fin n, UniformAffineCoordinates.count d :=
      Finset.prod_le_prod (fun i _ => Polynomial.natDegree_map_le.trans (hP i).2.1)
    _ = UniformAffineCoordinates.count d ^ n := by simp

end LeanCanny.Geometry.RegularCoordinateRootCount
