/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.ImplicitRootPersistence
public import LeanCanny.Geometry.ParametricPolynomialCalculus
public import LeanCanny.Algebra.MacaulayProjectiveRoots

/-! # Persistence and lowest-coefficient vanishing at regular projective roots

Let the coefficients and projective coordinates vary smoothly with a
parameter. An invertible Jacobian of the unshifted equations gives a local
root curve for the characteristic-shifted equations. Their quotient
polynomial vanishes along that curve, so its lowest characteristic
coefficient vanishes at the original parameter. A projective chart ensures
that the root coordinates stay nonzero. Singular points are not covered.
-/

@[expose] public section

open Filter
open scoped Topology

namespace LeanCanny.Geometry.MacaulayRegularPersistence
open LeanCanny.Algebra
variable {n : ℕ} {R K E : Type*} [CommRing R] [RCLike K]
  [NormedAddCommGroup E] [NormedSpace K E]

noncomputable def family (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R)
    (φ : E → R →+* K) (x : E → Fin (n + 1) → K) (a : E) : Fin (n + 1) → K :=
  fun i => MvPolynomial.eval₂ (φ a) (x a) (p i)

noncomputable def shiftedFamily (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R) (d : Fin (n + 1) → ℕ)
    (φ : E → R →+* K) (x : E → Fin (n + 1) → K) (z : K × E) : Fin (n + 1) → K :=
  fun i => MvPolynomial.eval₂ (φ z.2) (x z.2) (p i) - z.1 * (x z.2 i) ^ d i

theorem contDiff_shiftedFamily (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R) (d : Fin (n + 1) → ℕ)
    (φ : E → R →+* K) (x : E → Fin (n + 1) → K)
    (hφ : ∀ r, ContDiff K 1 (fun a => φ a r)) (hx : ∀ i, ContDiff K 1 (fun a => x a i)) :
    ContDiff K 1 (shiftedFamily p d φ x) := by
  apply contDiff_pi.mpr
  intro i
  exact (ParametricPolynomialCalculus.mvPolynomial_eval₂ (p i) (fun z : K × E => φ z.2)
    (fun z : K × E => x z.2) 1 (fun r => (hφ r).comp contDiff_snd)
    (fun j => (hx j).comp contDiff_snd)).sub (contDiff_fst.mul (((hx i).comp contDiff_snd).pow (d i)))

theorem partial_fderiv_shiftedFamily (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R) (d : Fin (n + 1) → ℕ)
    (φ : E → R →+* K) (x : E → Fin (n + 1) → K)
    (hφ : ∀ r, ContDiff K 1 (fun a => φ a r)) (hx : ∀ i, ContDiff K 1 (fun a => x a i)) (a : E) :
    fderiv K (shiftedFamily p d φ x) (0, a) ∘L ContinuousLinearMap.inr K K E =
      fderiv K (family p φ x) a := by
  have hf : HasFDerivAt (shiftedFamily p d φ x) (fderiv K (shiftedFamily p d φ x) (0, a)) (0, a) :=
    ((contDiff_shiftedFamily p d φ x hφ hx).differentiable (by simp)).differentiableAt.hasFDerivAt
  have hinr : HasFDerivAt (fun z : E => ((0 : K), z)) (ContinuousLinearMap.inr K K E) a :=
    (hasFDerivAt_const (0 : K) a).prodMk (hasFDerivAt_id a)
  have he := (hf.comp a hinr).fderiv
  have hfun : (fun z : E => shiftedFamily p d φ x (0, z)) = family p φ x := by
    funext z i
    simp only [shiftedFamily, family, zero_mul, sub_zero]
  change fderiv K (fun z : E => shiftedFamily p d φ x (0, z)) a = _ at he
  rw [hfun] at he
  exact he.symm

variable [CompleteSpace E]

theorem exists_shifted_root_curve (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R) (d : Fin (n + 1) → ℕ)
    (φ : E → R →+* K) (x : E → Fin (n + 1) → K)
    (hφ : ∀ r, ContDiff K 1 (fun a => φ a r)) (hx : ∀ i, ContDiff K 1 (fun a => x a i))
    (a : E) (hroot : family p φ x a = 0) (hJac : (fderiv K (family p φ x) a).IsInvertible) :
    ∃ curve : K → E, curve 0 = a ∧ ContinuousAt curve 0 ∧
      ∀ᶠ s in 𝓝 (0 : K), ∀ i, MvPolynomial.eval₂ (φ (curve s)) (x (curve s)) (p i) = s * x (curve s) i ^ d i := by
  obtain ⟨curve, hc0, hc, hcurve⟩ := ImplicitRootPersistence.exists_curve (shiftedFamily p d φ x) a
    (contDiff_shiftedFamily p d φ x hφ hx).contDiffAt (by
      funext i
      simpa only [shiftedFamily, family, zero_mul, sub_zero] using congrFun hroot i) (by
      rwa [partial_fderiv_shiftedFamily p d φ x hφ hx a])
  refine ⟨curve, hc0, hc, ?_⟩
  filter_upwards [hcurve] with s hs i
  exact sub_eq_zero.mp (congrFun hs i)

theorem trailingCoeff_eq_zero_of_regular_root (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R)
    (d : Fin (n + 1) → ℕ) (W : ℕ) (hdegree : ∀ i, d i < 2 ^ W) (hW : Macaulay.level d < 2 ^ W)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i)
    (φ : E → R →+* K) (x : E → Fin (n + 1) → K)
    (hφ : ∀ r, ContDiff K 1 (fun a => φ a r)) (hx : ∀ i, ContDiff K 1 (fun a => x a i))
    (hnz : ∀ a, ∃ j, x a j ≠ 0) (a : E) (hroot : family p φ x a = 0)
    (hJac : (fderiv K (family p φ x) a).IsInvertible) :
    φ a (Macaulay.characteristicQuotient p d W).trailingCoeff = 0 := by
  apply ImplicitRootPersistence.trailingCoeff_eq_zero (Macaulay.characteristicQuotient p d W) φ
    (fun r => (hφ r).continuous) (shiftedFamily p d φ x) a
    (contDiff_shiftedFamily p d φ x hφ hx).contDiffAt ?_ ?_ ?_
  · funext i
    simpa only [shiftedFamily, family, zero_mul, sub_zero] using congrFun hroot i
  · rwa [partial_fderiv_shiftedFamily p d φ x hφ hx a]
  · intro s z hz
    have hr (i : Fin (n + 1)) : MvPolynomial.eval₂ (φ z) (x z) (p i) = s * x z i ^ d i := by
      have he := congrFun hz i
      exact sub_eq_zero.mp he
    have he := MacaulayUniversal.eval_map_characteristicQuotient_eq_zero_of_common_root
      (φ z) d W hdegree hW p hp hd s (x z) hr (hnz z)
    rwa [Polynomial.eval_map] at he

end LeanCanny.Geometry.MacaulayRegularPersistence
