/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.AffineBoxGramEliminant
public import LeanCanny.Algebra.HomogenizationLayout

/-! # Complete finite coordinates for affine systems without infinity roots

Homogenization and the reciprocal Gram construction give a canonical bounded
integer annihilator for every coordinate of every affine root. Singular roots
are retained. Exclusion at infinity is checked over the complex numbers once;
the integer annihilators then work over every characteristic-zero field.
-/

@[expose] public section
namespace LeanCanny.Algebra.AffineFiniteCoordinates
open MvPolynomial WeightedHomogenization
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def layout (n : ℕ) : Option (Fin n) ≃ Fin (n + 1) :=
  HomogenizationLayout.variableEquiv (Equiv.refl _)

@[simp] lemma layout_none : layout n none = 0 := by
  apply Fin.ext
  exact HomogenizationLayout.variableEquiv_none _

@[simp] lemma layout_some (i : Fin n) : layout n (some i) = i.succ := by
  apply Fin.ext
  exact HomogenizationLayout.variableEquiv_some _ i

noncomputable def homogeneousRows (p : Fin n → MvPolynomial (Fin n) ℤ) (d : Fin n → ℕ)
    (i : Fin n) : MvPolynomial (Fin (n + 1)) ℤ :=
  rename (layout n) (homogenize (fun _ => 1) (d i) (p i))

def width (d : Fin n → ℕ) : ℕ := (Macaulay.level (AffineBoxGramEliminant.degrees d)).size

lemma level_lt (d : Fin n → ℕ) : Macaulay.level (AffineBoxGramEliminant.degrees d) < 2 ^ width d :=
  Nat.lt_size_self _

noncomputable def annihilator (p : Fin n → MvPolynomial (Fin n) ℤ) (d : Fin n → ℕ)
    (coordinate : Fin n) : Polynomial ℤ :=
  AffineBoxGramEliminant.annihilator (homogeneousRows p d) d (width d) coordinate.succ

def dimension (d : Fin n → ℕ) : ℕ := AffineBoxGramEliminant.dimension n (width d)

def NoInfinity (p : Fin n → MvPolynomial (Fin n) ℤ) (d : Fin n → ℕ) : Prop :=
  ∀ y : Option (Fin n) → ℂ, y none = 0 →
    (∀ i, (homogenize (fun _ => 1) (d i) (p i)).eval₂ (Int.castRingHom ℂ) y = 0) → y = 0

lemma homogeneous (p : Fin n → MvPolynomial (Fin n) ℤ) (d : Fin n → ℕ) (i : Fin n) :
    (homogeneousRows p d i).IsHomogeneous (d i) := by
  have hw : weights (fun _ : Fin n => 1) = 1 := by funext j; cases j <;> rfl
  apply IsHomogeneous.rename_isHomogeneous
  simpa only [IsHomogeneous, hw] using WeightedHomogenization.homogeneous (fun _ : Fin n => 1) (d i) (p i)

lemma noInfinity_layout (p : Fin n → MvPolynomial (Fin n) ℤ) (d : Fin n → ℕ)
    (h : NoInfinity p d) (x : Fin (n + 1) → ℂ) (hx : x 0 = 0)
    (hp : ∀ i, (homogeneousRows p d i).eval₂ (Int.castRingHom ℂ) x = 0) : x = 0 := by
  have he : x ∘ layout n = 0 := by
    apply h
    · simpa only [Function.comp_apply, layout_none] using hx
    · intro i
      simpa only [homogeneousRows, eval₂_rename] using hp i
  funext j
  simpa only [Function.comp_apply, Equiv.apply_symm_apply, Pi.zero_apply] using congrFun he ((layout n).symm j)

def point {K : Type*} [One K] (x : Fin n → K) : Fin (n + 1) → K :=
  fun j => ((layout n).symm j).elim 1 x

@[simp] lemma point_zero {K : Type*} [One K] (x : Fin n → K) : point x 0 = 1 := by
  change ((layout n).symm 0).elim 1 x = 1
  rw [← layout_none, Equiv.symm_apply_apply]
  rfl

@[simp] lemma point_succ {K : Type*} [One K] (x : Fin n → K) (i : Fin n) : point x i.succ = x i := by
  change ((layout n).symm i.succ).elim 1 x = x i
  rw [← layout_some i, Equiv.symm_apply_apply]
  rfl

lemma point_injective {K : Type*} [One K] : Function.Injective (point (K := K) (n := n)) := by
  intro x y h
  funext i
  simpa only [point_succ] using congrFun h i.succ

lemma eval_rows {K : Type*} [CommRing K]
    (p : Fin n → MvPolynomial (Fin n) ℤ) (d : Fin n → ℕ)
    (hp : ∀ i, (p i).totalDegree ≤ d i) (x : Fin n → K) (i : Fin n) :
    (homogeneousRows p d i).eval₂ (Int.castRingHom K) (point x) = (p i).eval₂ (Int.castRingHom K) x := by
  rw [homogeneousRows, eval₂_rename]
  have he : point x ∘ layout n = fun j => j.elim 1 x := by
    funext j
    simp [point]
  rw [he]
  apply WeightedHomogenization.eval_chart
  intro e he
  exact (weight_le_degree _ (by simp) e).trans ((le_totalDegree he).trans (hp i))

theorem ne_zero (p : Fin n → MvPolynomial (Fin n) ℤ) (d : Fin n → ℕ)
    (hd : ∀ i, 0 < d i) (hinfinity : NoInfinity p d) (coordinate : Fin n) :
    annihilator p d coordinate ≠ 0 :=
  AffineBoxGramEliminant.annihilator_ne_zero (homogeneousRows p d) d (width d) (level_lt d)
    (homogeneous p d) hd (noInfinity_layout p d hinfinity) coordinate.succ

theorem degree_le (p : Fin n → MvPolynomial (Fin n) ℤ) (d : Fin n → ℕ) (coordinate : Fin n) :
    (annihilator p d coordinate).natDegree ≤ dimension d + 1 :=
  AffineBoxGramEliminant.annihilator_degree_le (homogeneousRows p d) d (width d) coordinate.succ

theorem eval_eq_zero {K : Type*} [Field K]
    (p : Fin n → MvPolynomial (Fin n) ℤ) (d : Fin n → ℕ)
    (hp : ∀ i, (p i).totalDegree ≤ d i) (x : Fin n → K)
    (hx : ∀ i, (p i).eval₂ (Int.castRingHom K) x = 0) (coordinate : Fin n) :
    (annihilator p d coordinate).eval₂ (Int.castRingHom K) (x coordinate) = 0 := by
  have h := AffineBoxGramEliminant.annihilator_eval_eq_zero (homogeneousRows p d) d (width d) (level_lt d)
    (homogeneous p d) coordinate.succ (point x) (point_zero x) (fun i => (eval_rows p d hp x i).trans (hx i))
  simpa only [point_succ, annihilator] using h

theorem finite_roots {K : Type*} [Field K] [CharZero K]
    (p : Fin n → MvPolynomial (Fin n) ℤ) (d : Fin n → ℕ)
    (hp : ∀ i, (p i).totalDegree ≤ d i) (hd : ∀ i, 0 < d i) (hinfinity : NoInfinity p d) :
    {x : Fin n → K | ∀ i, (p i).eval₂ (Int.castRingHom K) x = 0}.Finite := by
  have hf := AffineBoxGramEliminant.finite_chart (K := K) (homogeneousRows p d) d (width d) (level_lt d)
    (homogeneous p d) hd (noInfinity_layout p d hinfinity)
  apply (hf.preimage point_injective.injOn).subset
  intro x hx
  exact ⟨point_zero x, fun i => (eval_rows p d hp x i).trans (hx i)⟩

lemma homogeneous_coefficient_bound (p : Fin n → MvPolynomial (Fin n) ℤ) (d : Fin n → ℕ)
    (M : ℕ) (hp : ∀ i e, ((p i).coeff e).natAbs ≤ M) (i : Fin n) (e : Fin (n + 1) →₀ ℕ) :
    ((homogeneousRows p d i).coeff e).natAbs ≤ M := by
  by_cases hz : (homogeneousRows p d i).coeff e = 0
  · simp [hz]
  · obtain ⟨u, hu, _⟩ := coeff_rename_ne_zero (layout n) _ e hz
    rw [homogeneousRows, ← hu, coeff_rename_mapDomain _ (layout n).injective,
      WeightedHomogenization.coefficient]
    split_ifs
    · exact hp i u.some
    · simp

theorem mass_le (p : Fin n → MvPolynomial (Fin n) ℤ) (d : Fin n → ℕ)
    (M : ℕ) (hM : 2 ≤ M) (hp : ∀ i e, ((p i).coeff e).natAbs ≤ M) (coordinate : Fin n) :
    coefficientMass (annihilator p d coordinate) ≤ (dimension d).factorial * M ^ dimension d :=
  AffineBoxGramEliminant.annihilator_mass_le (homogeneousRows p d) d (width d) M hM
    (homogeneous_coefficient_bound p d M hp) coordinate.succ

end LeanCanny.Algebra.AffineFiniteCoordinates
