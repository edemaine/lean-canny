/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedLimitCoordinate

/-! # Original limit roots from actual selected mixed critical branches

Every annihilator equation is obtained from the actual frozen critical source.
The bank denominator relation is stated literally as Q*y=eta*x. The old hom
is fixed through the limit, including when its universal lowest coefficient
vanishes and a later selected coefficient must be chosen.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedLimitCoordinate
open LeanCanny.Encoding IntegralMixedHistory IntegralMixedCriticalSweep Polynomial Filter MvPolynomial
open scoped Topology
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

theorem valid_index (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n-r.critical.offset.val+1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (c : Fin (ChoiceBound P r)) (hc : Valid x hm r j φ c) :
    (selectedSeries x hm r j φ).natTrailingDegree=c.val := by
  apply Nat.le_antisymm
  · apply natTrailingDegree_le_of_ne_zero
    rw [selected_coefficient]
    exact hc.2
  · apply le_natTrailingDegree (selected_ne_zero x hm r j φ)
    intro k hk
    rw [selected_coefficient]
    exact hc.1 k hk

theorem selected_factor_eq (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n-r.critical.offset.val+1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (c : Fin (ChoiceBound P r)) (hc : Valid x hm r j φ c) :
    (factor x hm r j c).map φ.toRingHom=(selectedSeries x hm r j φ).trailingCoeff := by
  rw [factor,← selected_coefficient,trailingCoeff,valid_index x hm r j φ c hc]

theorem factor_coefficient (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n-r.critical.offset.val+1)) (c : Fin (ChoiceBound P r)) (k : ℕ) :
    (factor x hm r j c).coeff k = if k ≤ c.val then
      ((coordinate x hm r j).coeff k).coeff (c.val-k)*
        (commonDenominator x : x.sampler.scalarPrefix.carrier)^(degree P r-k) else 0 :=
  BoundedClearedDilation.swapped_coefficient _ _ _ (coordinate_degree x hm r j) c.val k

theorem series_value (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n-r.critical.offset.val+1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (eta v : ℝ) :
    (selectedSeries x hm r j φ).eval₂ (evalRingHom v) eta =
      (BoundedClearedDilation.rescale (coordinate x hm r j) (commonDenominator x : _) (degree P r)).eval₂
        (eval₂RingHom φ.toRingHom eta) v := by
  have HC : (evalRingHom v).comp (mapRingHom φ.toRingHom)=eval₂RingHom φ.toRingHom v := by
    ext a
    · simp [RingHom.comp_apply,coe_mapRingHom]
    · simp [RingHom.comp_apply,coe_mapRingHom]
  rw [selectedSeries,series,Polynomial.eval₂_map,HC,ClearedDilationLimit.swap_eval]

theorem critical_root (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n-r.critical.offset.val+1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (eta v : ℝ) (z : Fin (n+1) → ℝ)
    (hscale : (commonDenominator x : ℝ)*z (ClearedCoordinateCritical.freeIndex r.critical.offset.val (fit r).le j)=eta*v)
    (hfrozen : ∀ i, i.val<r.critical.offset.val →
      ((data x hm r.critical).scales i:ℝ)*z i=heightValue x r φ eta i)
    (hp : (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) z=0)
    (hg : ∀ i : Fin (n-r.critical.offset.val+1), i≠objective r →
      (MvPolynomial.pderiv (ClearedCoordinateCritical.freeIndex r.critical.offset.val (fit r).le i)
        (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂ (Int.castRingHom ℝ) z=0) :
    (selectedSeries x hm r j φ).eval₂ (evalRingHom v) eta=0 := by
  rw [series_value]
  apply BoundedClearedDilation.root φ.toRingHom (coordinate x hm r j)
    (commonDenominator x : _) (degree P r) eta
    (z (ClearedCoordinateCritical.freeIndex r.critical.offset.val (fit r).le j)) v
  · simpa only [map_intCast] using hscale
  · have H := IntegralMixedCriticalSweep.coordinate_root x hm r j φ eta z hfrozen hp hg
    rw [selected,Polynomial.eval₂_map] at H
    have HC : (evalRingHom eta).comp (mapRingHom φ.toRingHom)=eval₂RingHom φ.toRingHom eta := by
      ext a
      · simp [RingHom.comp_apply,coe_mapRingHom]
      · simp [RingHom.comp_apply,coe_mapRingHom]
    simpa only [HC] using H

theorem limit_root {I : Type*} (l : Filter I) [NeBot l]
    (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n-r.critical.offset.val+1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (c : Fin (ChoiceBound P r)) (hc : Valid x hm r j φ c)
    (eta v : I → ℝ) (a : ℝ) (z : I → Fin (n+1) → ℝ)
    (heta : Tendsto eta l (𝓝 0)) (hv : Tendsto v l (𝓝 a)) (hne : ∀ᶠ i in l, eta i≠0)
    (hscale : ∀ᶠ i in l, (commonDenominator x : ℝ)*z i (ClearedCoordinateCritical.freeIndex r.critical.offset.val (fit r).le j)=eta i*v i)
    (hfrozen : ∀ᶠ i in l, ∀ h, h.val<r.critical.offset.val →
      ((data x hm r.critical).scales h:ℝ)*z i h=heightValue x r φ (eta i) h)
    (hp : ∀ᶠ i in l, (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) (z i)=0)
    (hg : ∀ᶠ h in l, ∀ i : Fin (n-r.critical.offset.val+1), i≠objective r →
      (MvPolynomial.pderiv (ClearedCoordinateCritical.freeIndex r.critical.offset.val (fit r).le i)
        (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂ (Int.castRingHom ℝ) (z h)=0) :
    ((factor x hm r j c).map φ.toRingHom).eval a=0 := by
  rw [selected_factor_eq x hm r j φ c hc]
  apply DeformationLowestCoefficient.trailingCoeff_eq_zero_of_tendsto (selectedSeries x hm r j φ)
    (fun a => evalRingHom a) (fun p => p.continuous) l v eta a hv heta hne
  filter_upwards [hscale,hfrozen,hp,hg] with i his hif hip hig
  exact critical_root x hm r j φ (eta i) (v i) (z i) his hif hip hig

end LeanCanny.Algebra.IntegralMixedLimitCoordinate
