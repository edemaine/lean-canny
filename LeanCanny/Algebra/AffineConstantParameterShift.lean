/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.AffineFiniteCoordinates
public import LeanCanny.Algebra.HomogenizationAtInfinity

/-! # Polynomial parameter shifts preserve affine infinity exclusion

Replacing selected row constants by polynomials in an external parameter
leaves every positive-degree leading equation unchanged. Thus a complete
critical tower can vary a height without requiring regular finite roots.
-/

@[expose] public section
namespace LeanCanny.Algebra.AffineConstantParameterShift
open MvPolynomial WeightedHomogenization
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

noncomputable def system (p : Fin n → MvPolynomial (Fin n) ℤ) (c : Fin n → Polynomial ℤ)
    (i : Fin n) : MvPolynomial (Fin n) (Polynomial ℤ) :=
  (p i).map Polynomial.C - C (c i)

lemma coefficient (p : Fin n → MvPolynomial (Fin n) ℤ) (c : Fin n → Polynomial ℤ)
    (i : Fin n) (e : Fin n →₀ ℕ) :
    (system p c i).coeff e = Polynomial.C ((p i).coeff e) - if e = 0 then c i else 0 := by
  simp only [system, coeff_sub, coeff_map, coeff_C, eq_comm (a := (0 : Fin n →₀ ℕ))]

lemma parameter_degree_le (p : Fin n → MvPolynomial (Fin n) ℤ) (c : Fin n → Polynomial ℤ)
    (i : Fin n) (e : Fin n →₀ ℕ) : ((system p c i).coeff e).natDegree ≤ (c i).natDegree := by
  rw [coefficient]
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · simp
  · split_ifs <;> simp

lemma at_zero (p : Fin n → MvPolynomial (Fin n) ℤ) (c : Fin n → Polynomial ℤ)
    (hc : ∀ i, (c i).eval 0 = 0) (i : Fin n) :
    (system p c i).map (Polynomial.evalRingHom (0 : ℤ)) = p i := by
  ext e
  rw [MvPolynomial.coeff_map, coefficient]
  simp [hc i, apply_ite]

lemma degree_le (p : Fin n → MvPolynomial (Fin n) ℤ) (c : Fin n → Polynomial ℤ)
    (d : Fin n → ℕ) (hd : ∀ i, (p i).totalDegree ≤ d i) (i : Fin n) :
    (system p c i).totalDegree ≤ d i := by
  apply (totalDegree_sub _ _).trans
  apply max_le
  · exact (PolynomialMapDegree.degree_le Polynomial.C (p i)).trans (hd i)
  · simp

lemma eval {K : Type*} [CommRing K] (p : Fin n → MvPolynomial (Fin n) ℤ)
    (c : Fin n → Polynomial ℤ) (phi : Polynomial ℤ →+* K) (x : Fin n → K) (i : Fin n) :
    (system p c i).eval₂ phi x = (p i).eval₂ (Int.castRingHom K) x - phi (c i) := by
  rw [system, eval₂_sub, eval₂_map, eval₂_C]
  have hphi : phi.comp Polynomial.C = Int.castRingHom K := Subsingleton.elim _ _
  rw [hphi]

lemma roots_iff {K : Type*} [CommRing K] (p : Fin n → MvPolynomial (Fin n) ℤ)
    (c : Fin n → Polynomial ℤ) (phi : Polynomial ℤ →+* K) (x : Fin n → K) :
    (∀ i, (system p c i).eval₂ phi x = 0) ↔
      ∀ i, (p i).eval₂ (Int.castRingHom K) x = phi (c i) := by
  simp only [eval, sub_eq_zero]

/-- All complex parameter specializations retain exclusion at infinity.
The shifted coefficients need not be integer values at that parameter. -/
theorem noInfinity (p : Fin n → MvPolynomial (Fin n) ℤ) (c : Fin n → Polynomial ℤ)
    (d : Fin n → ℕ) (hd : ∀ i, 0 < d i) (hp : AffineFiniteCoordinates.NoInfinity p d)
    (phi : Polynomial ℤ →+* ℂ) (y : Option (Fin n) → ℂ) (hy : y none = 0)
    (hz : ∀ i, (homogenize (fun _ => 1) (d i) (system p c i)).eval₂ phi y = 0) : y = 0 := by
  apply hp y hy
  intro i
  have hc : (homogenize (fun _ => 1) (d i) (C (c i) : MvPolynomial (Fin n) (Polynomial ℤ))).eval₂ phi y = 0 :=
    HomogenizationAtInfinity.eval_lower phi _ _ (by simpa only [totalDegree_C] using hd i) y hy
  have H := hz i
  rw [system, homogenize_sub, eval₂_sub, hc, sub_zero, ← map_homogenize, eval₂_map] at H
  have hphi : phi.comp Polynomial.C = Int.castRingHom ℂ := Subsingleton.elim _ _
  simpa only [hphi] using H

end LeanCanny.Algebra.AffineConstantParameterShift
