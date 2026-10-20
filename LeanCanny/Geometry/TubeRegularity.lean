/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.TubePolynomial
public import LeanCanny.Geometry.RegularPolynomialLevels

/-! # A common interval of regular active tubes

At fixed epsilon and delta, the energy specializes to a real polynomial in
point and shift coordinates. Its small positive levels are regular. Finitely
many active sets give a common interval, without an effective lower bound.
-/

@[expose] public section

namespace LeanCanny.Geometry.TubePolynomial
open MvPolynomial

variable {ι : Type*} [Fintype ι]

noncomputable def realEnergy (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι))
    (epsilon delta : ℝ) : MvPolynomial (Coordinate ι) ℝ :=
  (energy p s).map (coefficientMap epsilon delta 0)

theorem eval_realEnergy (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι))
    (epsilon delta : ℝ) (x : Coordinate ι → ℝ) :
    aeval x (realEnergy p s epsilon delta) = (energy p s).eval₂ (coefficientMap epsilon delta 0) x := by
  simp only [realEnergy, aeval_def, eval₂_map, Algebra.algebraMap_self, RingHom.id_comp]

theorem eval_as_realEnergy (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι))
    (epsilon delta alpha : ℝ) (x : Coordinate ι → ℝ) :
    (polynomial p s).eval₂ (coefficientMap epsilon delta alpha) x = aeval x (realEnergy p s epsilon delta) - alpha := by
  rw [eval_realEnergy]
  have h0 := eval_energy p s epsilon delta 0 (splitPoint x)
  have ha := eval_polynomial p s epsilon delta alpha (splitPoint x)
  rw [point_splitPoint] at h0 ha
  rw [h0]
  exact ha

theorem exists_regular_interval (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι))
    (epsilon delta : ℝ) :
    ∃ a : ℝ, 0 < a ∧ ∀ alpha : ℝ, 0 < alpha → alpha < a → ∀ x : Coordinate ι → ℝ,
      (polynomial p s).eval₂ (coefficientMap epsilon delta alpha) x = 0 →
        Function.Surjective (fderiv ℝ (fun y => (polynomial p s).eval₂ (coefficientMap epsilon delta alpha) y) x) := by
  obtain ⟨a, ha, hr⟩ := RegularPolynomialLevels.exists_interval (realEnergy p s epsilon delta)
  refine ⟨a, ha, ?_⟩
  intro alpha hp hs x hx
  have hv : aeval x (realEnergy p s epsilon delta) = alpha := by
    rw [eval_as_realEnergy, sub_eq_zero] at hx
    exact hx
  have h := hr alpha hp hs x hv
  have he : (fun y => (polynomial p s).eval₂ (coefficientMap epsilon delta alpha) y) =
      (fun y => aeval y (realEnergy p s epsilon delta) - alpha) :=
    funext (eval_as_realEnergy p s epsilon delta alpha)
  rw [he]
  exact h

theorem exists_common_regular_interval (p : MvPolynomial ι ℤ) (epsilon delta : ℝ) :
    ∃ a : ℝ, 0 < a ∧ ∀ alpha : ℝ, 0 < alpha → alpha < a →
      ∀ (s : Finset (PolynomialPerturbation.Constraint ι)) (x : Coordinate ι → ℝ),
        (polynomial p s).eval₂ (coefficientMap epsilon delta alpha) x = 0 →
          Function.Surjective (fderiv ℝ (fun y => (polynomial p s).eval₂ (coefficientMap epsilon delta alpha) y) x) := by
  classical
  choose a ha hr using (fun s : Finset (PolynomialPerturbation.Constraint ι) => exists_regular_interval p s epsilon delta)
  obtain ⟨b, hb, hm⟩ := CubeCoordinates.finite_positive_margin Finset.univ a (fun s _ => ha s)
  exact ⟨b, hb, fun alpha hp hs s x hx => hr s alpha hp (lt_of_lt_of_le hs (hm s (Finset.mem_univ s))) x hx⟩

end LeanCanny.Geometry.TubePolynomial
