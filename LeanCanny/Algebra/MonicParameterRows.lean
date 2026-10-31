/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CoordinatePowerSubstitution
public import LeanCanny.Algebra.FixedDegreeIntegralNormalization
public import LeanCanny.Algebra.HomogenizationAtInfinity

/-! # Monic scalar parameter rows with pure-power leading terms

Old scalar powers stay fixed. A sufficiently large power for the newly
introduced scalar makes every normalized lower term strictly lower degree.
At infinity the row is consequently just a power of the new coordinate,
even when the specialized selected leading coefficient vanishes.
-/

@[expose] public section
namespace LeanCanny.Algebra.MonicParameterRows
open MvPolynomial CoordinatePowerSubstitution
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

variable {ι R : Type*} [CommRing R]

noncomputable def coefficient (p : Polynomial (MvPolynomial ι R)) (d k : ℕ) : MvPolynomial ι R :=
  p.coeff k * p.coeff d ^ (d - 1 - k)

noncomputable def lower (p : Polynomial (MvPolynomial ι R)) (d : ℕ) (w : ι → ℕ) (W : ℕ) :
    MvPolynomial (ι ⊕ Unit) R :=
  ∑ k ∈ Finset.range d, rename Sum.inl (substitute w (coefficient p d k)) * X (Sum.inr ()) ^ (k * W)

noncomputable def row (p : Polynomial (MvPolynomial ι R)) (d : ℕ) (w : ι → ℕ) (W : ℕ) :
    MvPolynomial (ι ⊕ Unit) R := X (Sum.inr ()) ^ (d * W) + lower p d w W

theorem coefficient_degree (p : Polynomial (MvPolynomial ι R)) (d k B : ℕ) (w : ι → ℕ)
    (hk : k < d) (hp : ∀ j, (substitute w (p.coeff j)).totalDegree ≤ B) :
    (substitute w (coefficient p d k)).totalDegree ≤ d * B := by
  rw [coefficient, map_mul, map_pow]
  calc
    _ ≤ (substitute w (p.coeff k)).totalDegree +
        (substitute w (p.coeff d) ^ (d - 1 - k)).totalDegree := totalDegree_mul _ _
    _ ≤ B + (d - 1 - k) * B := Nat.add_le_add (hp k)
      ((totalDegree_pow _ _).trans (Nat.mul_le_mul_left _ (hp d)))
    _ = (d - 1 - k + 1) * B := by ring
    _ ≤ d * B := Nat.mul_le_mul_right B (by omega)

theorem lower_degree (p : Polynomial (MvPolynomial ι R)) (d B : ℕ) (w : ι → ℕ) (W : ℕ)
    (hd : 0 < d) (hW : d * B < W) (hp : ∀ j, (substitute w (p.coeff j)).totalDegree ≤ B) :
    (lower p d w W).totalDegree < d * W := by
  have hpos : 0 < d * W := Nat.mul_pos hd (by omega)
  apply (totalDegree_finsetSum _ _).trans_lt
  apply (Finset.sup_lt_iff hpos).mpr
  intro k hk
  have hkd : k < d := Finset.mem_range.mp hk
  have HC := (totalDegree_rename_le (Sum.inl : ι → ι ⊕ Unit) (substitute w (coefficient p d k))).trans
    (coefficient_degree p d k B w hkd hp)
  have HX : ((X (Sum.inr ()) : MvPolynomial (ι ⊕ Unit) R) ^ (k * W)).totalDegree ≤ k * W := by
    simpa only [mul_one] using (totalDegree_pow (X (Sum.inr ()) : MvPolynomial (ι ⊕ Unit) R) (k * W)).trans
      (Nat.mul_le_mul_left (k * W) (isHomogeneous_X (R := R) (Sum.inr () : ι ⊕ Unit)).totalDegree_le)
  have HT := (totalDegree_mul (rename Sum.inl (substitute w (coefficient p d k)))
    (X (Sum.inr ()) ^ (k * W))).trans (Nat.add_le_add HC HX)
  have HI : (k + 1) * W ≤ d * W := Nat.mul_le_mul_right W (by omega)
  apply HT.trans_lt
  exact (Nat.add_lt_add_right hW (k * W)).trans_le (by simpa only [Nat.add_mul, Nat.one_mul, Nat.add_comm] using HI)

theorem eval_row {K : Type*} [CommRing K] (φ : R →+* K)
    (p : Polynomial (MvPolynomial ι R)) (d : ℕ) (w : ι → ℕ) (W : ℕ) (z : (ι ⊕ Unit) → K) :
    (row p d w W).eval₂ φ z =
      (FixedDegreeIntegralNormalization.polynomial p d).eval₂
        (MvPolynomial.eval₂Hom φ (fun i => z (Sum.inl i) ^ w i)) (z (Sum.inr ()) ^ W) := by
  have HS (s : Finset ℕ) (a : ℕ → Polynomial (MvPolynomial ι R)) :
      (∑ i ∈ s, a i).eval₂ (MvPolynomial.eval₂Hom φ (fun i => z (Sum.inl i) ^ w i)) (z (Sum.inr ()) ^ W) =
        ∑ i ∈ s, (a i).eval₂ (MvPolynomial.eval₂Hom φ (fun i => z (Sum.inl i) ^ w i)) (z (Sum.inr ()) ^ W) :=
    map_sum (Polynomial.eval₂RingHom (MvPolynomial.eval₂Hom φ (fun i => z (Sum.inl i) ^ w i))
      (z (Sum.inr ()) ^ W)) a s
  simp only [row, lower, eval₂_add, eval₂_pow, eval₂_X, eval₂_sum, eval₂_mul, eval₂_rename,
    eval_substitute, FixedDegreeIntegralNormalization.polynomial,
    Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X, HS,
    Polynomial.eval₂_monomial, coe_eval₂Hom, coefficient, eval₂_mul, eval₂_pow,
    Function.comp_apply, ← pow_mul, Nat.mul_comm]

variable [Fintype ι]

theorem eval_infinity {K : Type*} [Field K] (φ : R →+* K)
    (p : Polynomial (MvPolynomial ι R)) (d B : ℕ) (w : ι → ℕ) (W : ℕ)
    (hd : 0 < d) (hW : d * B < W) (hp : ∀ j, (substitute w (p.coeff j)).totalDegree ≤ B)
    (y : Option (ι ⊕ Unit) → K) (hy : y none = 0) :
    (WeightedHomogenization.homogenize (fun _ => 1) (d * W) (row p d w W)).eval₂ φ y =
      y (some (Sum.inr ())) ^ (d * W) := by
  have HH : (X (Sum.inr ()) ^ (d * W) : MvPolynomial (ι ⊕ Unit) R).IsHomogeneous (d * W) := by
    simpa only [Nat.one_mul] using (isHomogeneous_X (R := R) (Sum.inr () : ι ⊕ Unit)).pow (d * W)
  rw [row, HomogenizationAtInfinity.eval_leading φ _ _ _ (lower_degree p d B w W hd hW hp) HH y hy]
  simp only [eval₂_pow, eval₂_X, Function.comp_apply]

theorem new_coordinate_zero {K : Type*} [Field K] (φ : R →+* K)
    (p : Polynomial (MvPolynomial ι R)) (d B : ℕ) (w : ι → ℕ) (W : ℕ)
    (hd : 0 < d) (hW : d * B < W) (hp : ∀ j, (substitute w (p.coeff j)).totalDegree ≤ B)
    (y : Option (ι ⊕ Unit) → K) (hy : y none = 0)
    (hz : (WeightedHomogenization.homogenize (fun _ => 1) (d * W) (row p d w W)).eval₂ φ y = 0) :
    y (some (Sum.inr ())) = 0 := by
  rw [eval_infinity φ p d B w W hd hW hp y hy] at hz
  exact (pow_eq_zero_iff (Nat.ne_of_gt (Nat.mul_pos hd (by omega)))).mp hz

end LeanCanny.Algebra.MonicParameterRows
