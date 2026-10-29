/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.AffineRingGramEliminant
public import LeanCanny.Algebra.AffineFiniteCoordinates

/-! # Complete affine coordinate certificates over parameter rings

The homogeneous reciprocal Gram construction gives bounded coordinate
relations over the original coefficient ring. Their leading coefficients
remain positive under real specializations with no roots at infinity.
-/

@[expose] public section
namespace LeanCanny.Algebra.AffineRingCoordinates
open MvPolynomial WeightedHomogenization
open AffineFiniteCoordinates (point point_zero point_succ)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {R : Type*} [CommRing R]
noncomputable def homogeneousRows (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ)
    (i : Fin n) : MvPolynomial (Fin (n + 1)) R :=
  rename (AffineFiniteCoordinates.layout n) (homogenize (fun _ => 1) (d i) (p i))

def width (d : Fin n → ℕ) : ℕ := (Macaulay.level (AffineRingGramEliminant.degrees d)).size

lemma level_lt (d : Fin n → ℕ) : Macaulay.level (AffineRingGramEliminant.degrees d) < 2 ^ width d :=
  Nat.lt_size_self _

noncomputable def annihilator (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ)
    (coordinate : Fin n) : Polynomial R :=
  AffineRingGramEliminant.annihilator (homogeneousRows p d) d (width d) coordinate.succ

def dimension (d : Fin n → ℕ) : ℕ := AffineRingGramEliminant.dimension n (width d)

def NoInfinity (rho : R →+* ℂ) (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) : Prop :=
  ∀ y : Option (Fin n) → ℂ, y none = 0 →
    (∀ i, (homogenize (fun _ => 1) (d i) (p i)).eval₂ rho y = 0) → y = 0

lemma homogeneous (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (i : Fin n) :
    (homogeneousRows p d i).IsHomogeneous (d i) := by
  have hw : weights (fun _ : Fin n => 1) = 1 := by funext j; cases j <;> rfl
  apply IsHomogeneous.rename_isHomogeneous
  simpa only [IsHomogeneous, hw] using WeightedHomogenization.homogeneous (fun _ : Fin n => 1) (d i) (p i)

lemma noInfinity_layout (rho : R →+* ℂ) (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ)
    (h : NoInfinity rho p d) (x : Fin (n + 1) → ℂ) (hx : x 0 = 0)
    (hp : ∀ i, (homogeneousRows p d i).eval₂ rho x = 0) : x = 0 := by
  have he : x ∘ AffineFiniteCoordinates.layout n = 0 := by
    apply h
    · simpa only [Function.comp_apply, AffineFiniteCoordinates.layout_none] using hx
    · intro i
      simpa only [homogeneousRows, eval₂_rename] using hp i
  funext j
  simpa only [Function.comp_apply, Equiv.apply_symm_apply, Pi.zero_apply] using congrFun he ((AffineFiniteCoordinates.layout n).symm j)

lemma eval_rows {K : Type*} [CommRing K]
    (rho : R →+* K) (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ)
    (hp : ∀ i, (p i).totalDegree ≤ d i) (x : Fin n → K) (i : Fin n) :
    (homogeneousRows p d i).eval₂ rho (point x) = (p i).eval₂ rho x := by
  rw [homogeneousRows, eval₂_rename]
  have he : point x ∘ AffineFiniteCoordinates.layout n = fun j => j.elim 1 x := by
    funext j
    simp [point]
  rw [he]
  apply WeightedHomogenization.eval_chart
  intro e he
  exact (weight_le_degree _ (by simp) e).trans ((le_totalDegree he).trans (hp i))


theorem degree_le (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (coordinate : Fin n) :
    (annihilator p d coordinate).natDegree ≤ dimension d + 1 :=
  AffineRingGramEliminant.annihilator_degree_le (homogeneousRows p d) d (width d) coordinate.succ

/-- Every original root is retained, including singular and repeated roots. -/
theorem eval_eq_zero {K : Type*} [Field K] (rho : R →+* K)
    (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ)
    (hp : ∀ i, (p i).totalDegree ≤ d i) (x : Fin n → K)
    (hx : ∀ i, (p i).eval₂ rho x = 0) (coordinate : Fin n) :
    (annihilator p d coordinate).eval₂ rho (x coordinate) = 0 := by
  have h := AffineRingGramEliminant.annihilator_eval_eq_zero rho
    (homogeneousRows p d) d (width d) (level_lt d) (homogeneous p d) coordinate.succ
    (point x) (point_zero x) (fun i => (eval_rows rho p d hp x i).trans (hx i))
  simpa only [point_succ, annihilator] using h

theorem exact_degree_and_positive_leading (rho : R →+* ℝ)
    (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ)
    (hd : ∀ i, 0 < d i) (hinfinity : NoInfinity (Complex.ofRealHom.comp rho) p d)
    (coordinate : Fin n) :
    (annihilator p d coordinate).natDegree = dimension d + 1 ∧
      0 < rho (annihilator p d coordinate).leadingCoeff :=
  AffineRingGramEliminant.exact_degree_and_positive_leading rho
    (homogeneousRows p d) d (width d) (level_lt d) (homogeneous p d) hd
    (noInfinity_layout _ p d hinfinity) coordinate.succ

lemma integer_annihilator_eq (p : Fin n → MvPolynomial (Fin n) ℤ)
    (d : Fin n → ℕ) (coordinate : Fin n) :
    annihilator p d coordinate = AffineFiniteCoordinates.annihilator p d coordinate := rfl

end LeanCanny.Algebra.AffineRingCoordinates
