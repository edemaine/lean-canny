/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.HypersurfaceSweep
public import LeanCanny.Geometry.ComponentCriticalSampling
public import LeanCanny.Algebra.CoordinateCriticalValues

/-! # Constructed regular intervals for a polynomial hypersurface sweep

A nonzero exceptional polynomial excludes the critical coordinate values on
a fixed regular hypersurface. Away from those values, a non-base polynomial
partial gives an explicit right inverse for the combined derivative.
Consequently the coordinate sweep has actual local product charts and, for a
proper level polynomial, is itself proper. The exceptional polynomial is
constructed from the equations; its input-size bounds remain open.
-/

@[expose] public section

namespace LeanCanny.Geometry.PolynomialHypersurfaceSweep
open Set MvPolynomial
open LeanCanny.Algebra

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem surjective_combined_of_partial (p : MvPolynomial ι ℝ) (base i : ι) (x : ι → ℝ)
    (hi : i ≠ base) (hpartial : (pderiv i p).eval x ≠ 0) :
    Function.Surjective (fderiv ℝ (HypersurfaceSweep.combined (fun y => p.eval y) (fun y => y base)) x) := by
  have hder : HasFDerivAt (fun y : ι → ℝ => p.eval y)
      (PolynomialCalculus.derivative (RingHom.id ℝ) p x) x := by
    simpa only [eval₂_id] using PolynomialCalculus.hasFDerivAt (RingHom.id ℝ) p x
  change Function.Surjective (fderiv ℝ (fun y : ι → ℝ => (p.eval y, y base)) x)
  rw [(hder.prodMk (hasFDerivAt_apply (𝕜 := ℝ) base x)).fderiv]
  rintro ⟨a, b⟩
  let c := (a - b * (pderiv base p).eval x) / (pderiv i p).eval x
  refine ⟨b • Pi.single base 1 + c • Pi.single i 1, ?_⟩
  apply Prod.ext
  · change PolynomialCalculus.derivative (RingHom.id ℝ) p x
      (b • Pi.single base 1 + c • Pi.single i 1) = a
    rw [map_add, map_smul, map_smul, PolynomialCalculus.derivative_single,
      PolynomialCalculus.derivative_single]
    simp only [eval₂_id, smul_eq_mul]
    dsimp only [c]
    rw [div_mul_cancel₀ _ hpartial]
    ring
  · change ((b • Pi.single base 1 + c • Pi.single i 1) : ι → ℝ) base = b
    simp [Ne.symm hi]

/-- On any fixed regular level, the excluded sweep values are roots of an
actual nonzero univariate polynomial. The projection direction is a coordinate. -/
theorem exists_exceptional (p : MvPolynomial ι ℝ) (base : ι) (c : ℝ)
    (hregular : ∀ x : ι → ℝ, p.eval x = c → Function.Surjective (fderiv ℝ (fun y => p.eval y) x)) :
    ∃ d : Polynomial ℝ, d ≠ 0 ∧ {t : ℝ | d.eval t = 0}.Finite ∧
      ∀ x : ι → ℝ, p.eval x = c → d.eval (x base) ≠ 0 →
        Function.Surjective (fderiv ℝ (HypersurfaceSweep.combined (fun y => p.eval y) (fun y => y base)) x) := by
  obtain ⟨d, hd, hm⟩ := CoordinateCriticalValues.exists_annihilator (p - C c) base
  refine ⟨d, hd, Polynomial.finite_setOfPred_isRoot hd, ?_⟩
  intro x hx hnonzero
  by_cases hex : ∃ i, i ≠ base ∧ (pderiv i p).eval x ≠ 0
  · obtain ⟨i, hi, hp⟩ := hex
    exact surjective_combined_of_partial p base i x hi hp
  · have hother (i : ι) (hi : i ≠ base) : (pderiv i p).eval x = 0 := by
      by_contra h
      exact hex ⟨i, hi, h⟩
    have hb : (pderiv base p).eval x ≠ 0 := by
      intro hb
      have hall (i : ι) : (pderiv i p).eval x = 0 := by
        by_cases hi : i = base
        · simpa only [hi] using hb
        · exact hother i hi
      have hz := (PolynomialCalculus.critical_iff (RingHom.id ℝ) p x).mpr
        (fun i => by simpa only [eval₂_id] using hall i)
      have hzero : fderiv ℝ (fun y => p.eval y) x = 0 := by simpa only [eval₂_id] using hz
      obtain ⟨v, hv⟩ := hregular x hx 1
      rw [hzero] at hv
      exact zero_ne_one hv
    have hq : aeval x (p - C c) = 0 := by
      simp only [map_sub, aeval_def, Algebra.algebraMap_self, eval₂_id, hx, eval_C, sub_self]
    have hb' : aeval x (pderiv base (p - C c)) ≠ 0 := by
      simpa only [map_sub, pderiv_C, sub_zero, aeval_def, Algebra.algebraMap_self, eval₂_id] using hb
    have hother' (i : ι) (hi : i ≠ base) : aeval x (pderiv i (p - C c)) = 0 := by
      simpa only [map_sub, pderiv_C, sub_zero, aeval_def, Algebra.algebraMap_self, eval₂_id] using hother i hi
    have he := CoordinateCriticalValues.eval_annihilator (p - C c) base d hm x hq hb' hother'
    have hd0 : d.eval (x base) = 0 := by
      simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id] using he
    exact False.elim (hnonzero hd0)

/-- Avoiding the original polynomial's critical-value factor gives a proper
coordinate sweep and constructed regular charts between its exceptional values. -/
theorem exists_regular_sweeps (p : MvPolynomial ι ℝ) (base : ι)
    (hp : IsProperMap (fun x : ι → ℝ => p.eval x)) :
    ∃ h : Polynomial ℝ, h ≠ 0 ∧ {c : ℝ | h.eval c = 0}.Finite ∧
      ∀ c : ℝ, h.eval c ≠ 0 → ∃ d : Polynomial ℝ, d ≠ 0 ∧ {t : ℝ | d.eval t = 0}.Finite ∧
        IsProperMap (HypersurfaceSweep.projection (fun x => p.eval x) (fun x => x base) c) ∧
        ∀ S : Set ℝ, (∀ t ∈ S, d.eval t ≠ 0) →
          ∃ chart : ∀ x : HypersurfaceSweep.Slab (fun x => p.eval x) (fun x => x base) c S,
              OpenPartialHomeomorph (HypersurfaceSweep.Slab (fun x => p.eval x) (fun x => x base) c S)
                (S × (fderiv ℝ (HypersurfaceSweep.combined (fun x => p.eval x) (fun x => x base)) x.val.val).ker),
            (∀ x, x ∈ (chart x).source) ∧ ∀ a x, x ∈ (chart a).source →
              (chart a x).1 = S.restrictPreimage
                (HypersurfaceSweep.projection (fun x => p.eval x) (fun x => x base) c) x := by
  obtain ⟨h, hh, hm⟩ := CriticalValueAnnihilator.exists_annihilator p
  refine ⟨h, hh, Polynomial.finite_setOfPred_isRoot hh, ?_⟩
  intro c hc
  have hregular := ComponentCriticalSampling.regular_level_of_annihilator p h hm c hc
  obtain ⟨d, hd, hfinite, hcombined⟩ := exists_exceptional p base c hregular
  refine ⟨d, hd, hfinite, HypersurfaceSweep.isProperMap _ _ c hp (continuous_apply base), ?_⟩
  intro S hS
  apply HypersurfaceSweep.exists_charts
  · intro x _ _
    exact ((ProjectionCritical.contDiff_eval (RingHom.id ℝ) p).prodMk
      (contDiff_apply ℝ (fun _ : ι => ℝ) base)).of_le le_top |>.contDiffAt
  · intro x hx hxs
    exact hcombined x hx (hS _ hxs)

end LeanCanny.Geometry.PolynomialHypersurfaceSweep
