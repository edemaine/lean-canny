/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCriticalSweep
public import LeanCanny.Algebra.SelectedMultivariatePolynomialLift
/-! # Sufficient actual truncation bounds recover the selected coordinate head

One old interpreting hom controls every coefficient and the same weighted
raw tuple. No statement lifts arbitrary absolute-norm roots to that hom.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedSelectedCoordinateHead
open IntegralMixedHistory IntegralHistorySampler Polynomial
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

noncomputable def head (x : State P S B m ι) (hm : m≤S) (r : IntegralMixedCriticalSweep.Rule n)
    (j : Fin (n-r.critical.offset.val+1)) (d e : ℕ) :
    Polynomial (MvPolynomial (Fin (m+1)) ℤ) :=
  SelectedMultivariatePolynomialLift.lift (IntegralMixedCriticalSweep.coordinate x hm r j)
    (SelectedPoweredPolynomialLift.representative x.sampler.scalarPrefix.basis
      (UniformIntegralPowerSchedule.weights S (2^B) m)) d e

theorem selected (x : State P S B m ι) (hm : m≤S) (r : IntegralMixedCriticalSweep.Rule n)
    (j : Fin (n-r.critical.offset.val+1)) (d e : ℕ)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (z : Fin m→ℝ)
    (hφ : ∀ i,φ (x.sampler.scalarPrefix.basis.generator i)=
      z i^UniformIntegralPowerSchedule.weights S (2^B) m i)
    (hd : PurePowerReductionBounds.dimension (n-r.critical.offset.val+1) P.degree≤d)
    (he : IntegralMixedCriticalSweep.parameterDegree P.degree r≤e) :
    (head x hm r j d e).map (SelectedMultivariatePolynomialLift.evaluate (MvPolynomial.aeval z).toRingHom)=
      IntegralMixedCriticalSweep.selected x hm r j φ :=by
  apply SelectedMultivariatePolynomialLift.map_lift
  · exact SelectedPoweredPolynomialLift.evaluate _ _ z φ hφ
  · exact Polynomial.natDegree_map_le.trans ((IntegralMixedCriticalSweep.coordinate_degree x hm r j).trans hd)
  · intro i _
    exact Polynomial.natDegree_map_le.trans ((IntegralMixedCriticalSweep.coordinate_coefficient_degree x hm r j i).trans he)

theorem specialized_degree (x : State P S B m ι) (hm : m≤S) (r : IntegralMixedCriticalSweep.Rule n)
    (j : Fin (n-r.critical.offset.val+1)) (d e : ℕ)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (z : Fin m→ℝ)
    (hφ : ∀ i,φ (x.sampler.scalarPrefix.basis.generator i)=
      z i^UniformIntegralPowerSchedule.weights S (2^B) m i)
    (hd : PurePowerReductionBounds.dimension (n-r.critical.offset.val+1) P.degree≤d)
    (he : IntegralMixedCriticalSweep.parameterDegree P.degree r≤e) (η : ℝ) :
    (((head x hm r j d e).map (SelectedMultivariatePolynomialLift.evaluate (MvPolynomial.aeval z).toRingHom)).map
      (Polynomial.evalRingHom η)).natDegree=PurePowerReductionBounds.dimension (n-r.critical.offset.val+1) P.degree :=by
  rw [selected x hm r j d e φ z hφ hd he]
  exact IntegralMixedCriticalSweep.specialized_degree x hm r j φ η

end LeanCanny.Algebra.IntegralMixedSelectedCoordinateHead
