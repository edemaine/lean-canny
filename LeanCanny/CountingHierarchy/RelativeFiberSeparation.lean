/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.RelativeSectionNonvanishing
public import LeanCanny.CountingHierarchy.BivariateSwapBounds
public import LeanCanny.CountingHierarchy.AlgebraicFiberSeparation

/-! # Empty source fibers are clopen on the actual section's degree pieces -/

public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial Polynomial Set
open scoped Topology Classical

variable {n m : ℕ} {A : Type*} [TopologicalSpace A]

theorem relative_emptyFibers_isClopen (d : ℕ) (hd : 1 ≤ d) (he : Even (d + 2))
    (P : MvPolynomial (Fin (n + m)) ℤ) (hP : P.totalDegree ≤ d + 1)
    (r : A → (Fin m → ℝ)) (hr : Continuous r)
    (hFn : ∀ x z, 0 ≤ MvPolynomial.eval₂ (Int.castRingHom ℝ) (Fin.addCases z (r x)) P)
    (k : ℕ) (hdegree : ∀ x, (specializedRelativeSection d P hP (r x)).natDegree ≤ k)
    (hlead : ∀ x, (specializedRelativeSection d P hP (r x)).coeff k ≠ 0) :
    IsClopen {x | ¬∃ z : Fin n → ℝ,
      MvPolynomial.eval₂ (Int.castRingHom ℝ) (Fin.addCases z (r x)) P = 0} := by
  let F := MvPolynomial.rename finSumFinEquiv.symm P
  have hF : F.totalDegree ≤ d + 1 := (MvPolynomial.totalDegree_rename_le _ _).trans hP
  let f := fun x z => ((d + 2 : ℕ) : ℝ) * MvPolynomial.eval z (relativeSpecializedSource F (r x))
  let G := separatedPotential (d + 1) (fun _ : Fin n => (0 : ℝ))
  have hvalue (x : A) (z : Fin n → ℝ) :
      MvPolynomial.eval z (relativeSpecializedSource F (r x)) =
        MvPolynomial.eval₂ (Int.castRingHom ℝ) (Fin.addCases z (r x)) P := by
    exact eval_specializeFinitePolynomial P (Int.castRingHom ℝ) z (r x)
  have hf : Continuous (fun q : A × (Fin n → ℝ) => f q.1 q.2) := by
    have hcoords : Continuous (fun q : A × (Fin n → ℝ) => (Fin.addCases q.2 (r q.1) : Fin (n + m) → ℝ)) := by
      apply continuous_pi
      intro i
      refine Fin.addCases (motive := fun i : Fin (n + m) =>
        Continuous (fun q : A × (Fin n → ℝ) => ((Fin.addCases q.2 (r q.1) : Fin (n + m) → ℝ) i)))
        (fun j => ?_) (fun j => ?_) i
      · simpa only [Function.comp_def, Fin.addCases_left] using
          (show Continuous (fun z : Fin n → ℝ => z j) from continuous_apply j).comp
            (continuous_snd : Continuous (fun q : A × (Fin n → ℝ) => q.2))
      · simpa only [Function.comp_def, Fin.addCases_right] using
          ((continuous_apply j).comp hr).comp
            (continuous_fst : Continuous (fun q : A × (Fin n → ℝ) => q.1))
    have hv := (MvPolynomial.continuous_eval (P.map (Int.castRingHom ℝ))).comp hcoords
    apply continuous_const.mul
    convert hv using 1
    ext q
    simp only [Function.comp_def, MvPolynomial.eval_map]
    exact hvalue q.1 q.2
  have hnon (x : A) (z : Fin n → ℝ) : 0 ≤ f x z := by
    exact mul_nonneg (by positivity) ((hvalue x z).symm ▸ hFn x z)
  have hroot (x : A) (u : ℝ) (hu : 0 ≤ u) :
      (Bivariate.swap (relativeBivariate d F hF (r x))).eval₂
        (Polynomial.evalRingHom (coerciveMinimumValue (f x) G u)) u = 0 := by
    rw [bivariate_swap_eval]
    exact relativeBivariate_root_at_minimum d hd he F hF (r x)
      (fun z => (hvalue x z).symm ▸ hFn x z) u hu
  have hcoeff (i : ℕ) : Continuous (fun x => (specializedRelativeSection d P hP (r x)).coeff i) := by
    simp only [specializedRelativeSection, Polynomial.coeff_map, MvPolynomial.coe_eval₂Hom]
    simpa only [MvPolynomial.eval_map, firstVariableCoefficient, Function.comp_def] using
      (MvPolynomial.continuous_eval ((firstVariableCoefficient (finiteRelativeSection d P hP) i).map
        (Int.castRingHom ℝ))).comp hr
  have hsection (x : A) (v : ℝ) :
      (specializedRelativeSection d P hP (r x)).eval v =
        (Bivariate.swap (relativeBivariate d F hF (r x))).eval₂
          (Polynomial.evalRingHom v) (v ^ ((d + 1) ^ n + 1)) := by
    rw [specializedRelativeSection, Polynomial.eval_map, eval_finSuccEquiv,
      eval_finiteRelativeSection, bivariate_swap_eval]
  have hc := emptyFibers_isClopen_on_degree_piece f G hf
    (continuous_separatedPotential _ _) hnon
    (separatedPotential_nonneg (d + 1) he _ (fun _ => le_rfl))
    (separatedPotential_compact_sublevel (d + 1) (by omega) he _ (fun _ => le_rfl))
    (fun _ => 0) ((d + 1) ^ n) (fun x => Bivariate.swap (relativeBivariate d F hF (r x)))
    (fun x => by
      intro hz
      have h := congrArg Bivariate.swap hz
      simp only [Bivariate.swap_swap_apply, map_zero] at h
      exact (relativeBivariate_monic d F hF (r x)).ne_zero h)
    (fun x j => (bivariate_swap_coefficient_degree_le _ j).trans_eq (relativeBivariate_natDegree _ _ _ _))
    hroot (fun x => specializedRelativeSection d P hP (r x)) k hcoeff hdegree hlead hsection
  convert hc using 1
  ext x
  simp only [f, hvalue, mul_eq_zero, show ((d + 2 : ℕ) : ℝ) ≠ 0 by positivity, false_or]

end LeanCanny.CountingHierarchy
