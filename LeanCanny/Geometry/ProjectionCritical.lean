/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.ActiveExtremum
public import LeanCanny.Geometry.PolynomialCalculus
public import LeanCanny.Algebra.ProjectionEquations
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Tactic.Ring

/-! # Hypersurface projection extrema satisfy polynomial critical equations

Normalized Lagrange multipliers and the formal derivative formula turn a local
projection maximum on a regular hypersurface into the polynomial system. The
statement allows an arbitrary coefficient homomorphism into the reals, so real
specialization of polynomial parameters is included.
-/

@[expose] public section

namespace LeanCanny.Geometry.ProjectionCritical
open MvPolynomial
open scoped BigOperators

variable {ι R : Type*} [Fintype ι] [CommRing R]

noncomputable def projection (v : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i, v i • ContinuousLinearMap.proj i

theorem projection_single [DecidableEq ι] (v : ι → ℝ) (i : ι) :
    projection v (Pi.single i 1) = v i := by
  simp [projection, Pi.single_apply]

theorem contDiff_eval (φ : R →+* ℝ) (p : MvPolynomial ι R) :
    ContDiff ℝ ⊤ (fun y => p.eval₂ φ y) := by
  induction p using MvPolynomial.induction_on with
  | C c => simpa only [MvPolynomial.eval₂_C] using (contDiff_const (c := φ c))
  | add p q hp hq => simpa only [MvPolynomial.eval₂_add] using hp.add hq
  | mul_X p i hp => simpa only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_X] using hp.mul (contDiff_apply ℝ ℝ i)

theorem exists_scalar (φ : R →+* ℝ) (p : MvPolynomial ι R) (x v : ι → ℝ)
    (hx : p.eval₂ φ x = 0)
    (hmax : IsLocalMaxOn (projection v) {y | p.eval₂ φ y = 0} x)
    (hregular : Function.Surjective (fderiv ℝ (fun y => p.eval₂ φ y) x)) :
    ∃ c : ℝ, ∀ i, v i = c * (pderiv i p).eval₂ φ x := by
  classical
  have hlocal : IsLocalMaxOn (projection v) {y | p.eval₂ φ y = p.eval₂ φ x} x := by
    simpa only [hx] using hmax
  obtain ⟨Λ, hΛ⟩ := ActiveExtremum.exists_normalized _ _ x _ (projection v) hlocal
    ((contDiff_eval φ p).hasStrictFDerivAt (by simp)) (projection v).hasStrictFDerivAt hregular
  refine ⟨Λ 1, ?_⟩
  intro i
  have h := hΛ (Pi.single i 1)
  rw [projection_single, PolynomialCalculus.fderiv_eq, PolynomialCalculus.derivative_single] at h
  have he : ∀ r : ℝ, Λ r = Λ 1 * r := by
    intro r
    simpa only [smul_eq_mul, mul_one, mul_comm] using Λ.map_smul r 1
  exact h.trans (he _)

theorem satisfies_equations (φ : R →+* ℝ) (p : MvPolynomial ι R) (base : ι) (x v : ι → ℝ)
    (hv : v base = 1) (hx : p.eval₂ φ x = 0)
    (hmax : IsLocalMaxOn (projection v) {y | p.eval₂ φ y = 0} x)
    (hregular : Function.Surjective (fderiv ℝ (fun y => p.eval₂ φ y) x)) :
    ∀ j, (Algebra.ProjectionEquations.polynomial p base j).eval₂ φ (Sum.elim x v) = 0 := by
  obtain ⟨c, hc⟩ := exists_scalar φ p x v hx hmax hregular
  apply (Algebra.ProjectionEquations.equations_iff p base φ x v).mpr
  refine ⟨hx, ?_⟩
  intro i
  calc
    _ = (pderiv i p).eval₂ φ x * (1 - c * (pderiv base p).eval₂ φ x) := by rw [hc i]; ring
    _ = 0 := by rw [← hc base, hv]; ring

theorem satisfies_system (φ : R →+* ℝ) (p : MvPolynomial ι R) (base : ι) (x v : ι → ℝ)
    (hv : v base = 1) (hx : p.eval₂ φ x = 0)
    (hmax : IsLocalMaxOn (projection v) {y | p.eval₂ φ y = 0} x)
    (hregular : Function.Surjective (fderiv ℝ (fun y => p.eval₂ φ y) x)) :
    ∀ j, (Algebra.ProjectionEquations.system p base j).eval₂ φ (Sum.elim x v) = 0 :=
  fun j => satisfies_equations φ p base x v hv hx hmax hregular (j.map Subtype.val)

end LeanCanny.Geometry.ProjectionCritical
