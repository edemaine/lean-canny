/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.RelativeProjectiveValueGram
public import LeanCanny.Algebra.DiagonalPolynomialParameterSpace
public import LeanCanny.Geometry.UnivariateRootFamily

/-! # Relative value equations for actual affine coordinate grids

Coordinate equations and a polynomial test build the full reciprocal Gram
value certificate over the original coefficient algebra. Nonzero selected
coordinate leadings prove selected-component nonvanishing; repeated roots
are allowed. Homogenization preserves sweep-parameter coefficient bounds.
-/

@[expose] public section
namespace LeanCanny.Algebra.RelativeAffineGridValueGram
open MvPolynomial WeightedHomogenization
open AffineFiniteCoordinates (point point_zero)
open scoped Classical
variable {n : ℕ} {R : Type*} [CommRing R]

noncomputable def rows (p : Fin n → Polynomial (Polynomial R)) :
    Fin n → MvPolynomial (Fin n) (Polynomial R) := fun i => (p i).toMvPolynomial i

noncomputable def test (q : MvPolynomial (Fin n) (Polynomial R)) (e : ℕ) :
    MvPolynomial (Fin (n + 1)) (Polynomial R) :=
  rename (AffineFiniteCoordinates.layout n) (homogenize (fun _ => 1) e q)

def width (d : Fin n → ℕ) (e : ℕ) := (Macaulay.level (RelativeProjectiveValueGram.degrees d e)).size

noncomputable def annihilator (p : Fin n → Polynomial (Polynomial R))
    (q : MvPolynomial (Fin n) (Polynomial R)) (d : Fin n → ℕ) (e : ℕ) :=
  RelativeProjectiveValueGram.annihilator (AffineRingCoordinates.homogeneousRows (rows p) d)
    (test q e) d e (width d e)

theorem test_homogeneous (q : MvPolynomial (Fin n) (Polynomial R)) (e : ℕ) :
    (test q e).IsHomogeneous e := by
  have HW : weights (fun _ : Fin n => 1) = 1 := by funext j; cases j <;> rfl
  apply IsHomogeneous.rename_isHomogeneous
  simpa only [IsHomogeneous, HW] using WeightedHomogenization.homogeneous (fun _ : Fin n => 1) e q

theorem test_eval {K : Type*} [CommRing K] (ρ : Polynomial R →+* K)
    (q : MvPolynomial (Fin n) (Polynomial R)) (e : ℕ) (hq : q.totalDegree ≤ e) (z : Fin n → K) :
    (test q e).eval₂ ρ (point z) = q.eval₂ ρ z := by
  rw [test, eval₂_rename]
  have HE : point z ∘ AffineFiniteCoordinates.layout n = fun j => j.elim 1 z := by
    funext j
    simp [point]
  rw [HE]
  apply WeightedHomogenization.eval_chart
  intro v hv
  exact (weight_le_degree _ (by simp) v).trans ((le_totalDegree hv).trans hq)

theorem root {K : Type*} [Field K] (p : Fin n → Polynomial (Polynomial R))
    (q : MvPolynomial (Fin n) (Polynomial R)) (d : Fin n → ℕ) (e : ℕ)
    (hd : ∀ i, (p i).natDegree ≤ d i) (hq : q.totalDegree ≤ e)
    (ρ : Polynomial R →+* K) (z : Fin n → K)
    (hz : ∀ i, (p i).eval₂ ρ (z i) = 0) :
    (annihilator p q d e).eval₂ ρ (q.eval₂ ρ z) = 0 := by
  have H := RelativeProjectiveValueGram.root (AffineRingCoordinates.homogeneousRows (rows p) d)
    (test q e) d e (width d e) (Nat.lt_size_self _)
    (AffineRingCoordinates.homogeneous (rows p) d) (test_homogeneous q e) ρ (point z) (point_zero z) (fun i => ?_)
  · rw [test_eval ρ q e hq z] at H
    exact H
  · rw [AffineRingCoordinates.eval_rows ρ (rows p) d (fun i => (UnivariateInfinity.degree_le (p i) i).trans (hd i))]
    exact (LeanCanny.Geometry.UnivariateRootFamily.eval (p i) i ρ z).trans (hz i)

theorem selected_ne_zero (p : Fin n → Polynomial (Polynomial R))
    (q : MvPolynomial (Fin n) (Polynomial R)) (d : Fin n → ℕ) (e : ℕ)
    (hd : ∀ i, (p i).natDegree = d i) (hpos : ∀ i, 0 < d i) (he : 0 < e)
    (φ : R →+* ℝ) (t₀ : ℝ)
    (hl : ∀ i, (Complex.ofRealHom.comp (Polynomial.eval₂RingHom φ t₀)) (p i).leadingCoeff ≠ 0) :
    (annihilator p q d e).map (Polynomial.mapRingHom φ) ≠ 0 := by
  apply RelativeProjectiveValueGram.selected_ne_zero (AffineRingCoordinates.homogeneousRows (rows p) d)
    (test q e) d e (width d e) (Nat.lt_size_self _)
    (AffineRingCoordinates.homogeneous (rows p) d) (test_homogeneous q e) hpos he φ t₀
  apply AffineRingCoordinates.noInfinity_layout
  have H := UnivariateInfinity.noInfinity p (fun i => (hd i).symm ▸ hpos i)
    (Complex.ofRealHom.comp (Polynomial.eval₂RingHom φ t₀)) hl
  have HE : (fun i => (p i).natDegree) = d := funext hd
  rw [HE] at H
  exact H

theorem homogenized_inner_degree (q : MvPolynomial (Fin n) (Polynomial R)) (e E : ℕ)
    (hq : ∀ v, (q.coeff v).natDegree ≤ E) (v : Fin (n + 1) →₀ ℕ) :
    ((test q e).coeff v).natDegree ≤ E := by
  by_cases HZ : (test q e).coeff v = 0
  · simp only [HZ, Polynomial.natDegree_zero, Nat.zero_le]
  · obtain ⟨w, hw, _⟩ := coeff_rename_ne_zero (AffineFiniteCoordinates.layout n) _ v HZ
    rw [← hw, test, coeff_rename_mapDomain _ (AffineFiniteCoordinates.layout n).injective,
      WeightedHomogenization.coefficient]
    split_ifs
    · exact hq _
    · simp

theorem inner_degree (p : Fin n → Polynomial (Polynomial R))
    (q : MvPolynomial (Fin n) (Polynomial R)) (d : Fin n → ℕ) (e E : ℕ)
    (hp : ∀ i k, ((p i).coeff k).natDegree ≤ E) (hq : ∀ v, (q.coeff v).natDegree ≤ E) (k : ℕ) :
    ((annihilator p q d e).coeff k).natDegree ≤ RelativeProjectiveValueGram.dimension n (width d e) * E := by
  apply RelativeProjectiveValueGram.annihilator_inner_degree
  · intro i v
    apply homogenized_inner_degree (rows p i) (d i) E
    intro w
    rw [rows, DiagonalParameterBits.coefficient]
    split_ifs
    · exact hp i _
    · simp
  · exact homogenized_inner_degree q e E hq

theorem degree_le (p : Fin n → Polynomial (Polynomial R))
    (q : MvPolynomial (Fin n) (Polynomial R)) (d : Fin n → ℕ) (e : ℕ) :
    (annihilator p q d e).natDegree ≤ RelativeProjectiveValueGram.dimension n (width d e) + 1 :=
  RelativeProjectiveValueGram.annihilator_degree _ _ _ _ _

end LeanCanny.Algebra.RelativeAffineGridValueGram
