/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.ActiveExtremum
public import LeanCanny.Geometry.RegularRadius
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! # Critical maxima on compact regular perturbation sets

A maximum of a linear projection is locally maximal on the fiber of its active
constraints and the radius equation. Surjectivity on a regular radius gives
normalized Lagrange multipliers for that maximum.
-/

@[expose] public section

namespace LeanCanny.Geometry.PolynomialPerturbation

variable {ι : Type*} [Fintype ι]

noncomputable def activeSet (p : MvPolynomial ι ℤ) (epsilon : ℝ)
    (z : (ι → ℝ) × (Constraint ι → ℝ)) : Finset (Constraint ι) := by
  classical
  exact Finset.univ.filter (fun i => parameterMap p epsilon z i = 0)

theorem mem_activeSet (p : MvPolynomial ι ℤ) (epsilon : ℝ)
    (z : (ι → ℝ) × (Constraint ι → ℝ)) (i : Constraint ι) :
    i ∈ activeSet p epsilon z ↔ parameterMap p epsilon z i = 0 := by
  classical
  simp [activeSet]

theorem inactive_pos (p : MvPolynomial ι ℤ) (epsilon delta : ℝ)
    (z : (ι → ℝ) × (Constraint ι → ℝ)) (hz : z ∈ perturbed p epsilon delta)
    (i : Constraint ι) (hi : i ∉ activeSet p epsilon z) : 0 < parameterMap p epsilon z i := by
  exact lt_of_le_of_ne (hz.1 i) (Ne.symm fun h => hi ((mem_activeSet p epsilon z i).mpr h))

theorem contDiff_fixedMap (p : MvPolynomial ι ℤ) (epsilon delta : ℝ) (s : Finset (Constraint ι)) :
    ContDiff ℝ ⊤ (ActiveRadius.fixedMap (constraintMap p epsilon) s delta) := by
  have hh := (ActiveRadius.restriction s).contDiff.comp (contDiff_parameterMap p epsilon)
  have hr : ContDiff ℝ ⊤ (fun z : (ι → ℝ) × (Constraint ι → ℝ) => SquaredRadius.value z.2 - delta ^ 2) :=
    (SquaredRadius.contDiff.comp contDiff_snd).sub (contDiff_const (c := delta ^ 2))
  exact hh.prodMk hr

theorem isLocalMaxOn_active_fiber (p : MvPolynomial ι ℤ) (epsilon delta : ℝ)
    (φ : ((ι → ℝ) × (Constraint ι → ℝ)) → ℝ) (z : (ι → ℝ) × (Constraint ι → ℝ))
    (hz : z ∈ perturbed p epsilon delta) (hmax : IsMaxOn φ (perturbed p epsilon delta) z) :
    IsLocalMaxOn φ {w | ActiveRadius.fixedMap (constraintMap p epsilon) (activeSet p epsilon z) delta w =
      ActiveRadius.fixedMap (constraintMap p epsilon) (activeSet p epsilon z) delta z} z := by
  have he : ActiveExtremum.feasible (parameterMap p epsilon)
      (fun w => SquaredRadius.value w.2 - delta ^ 2) = perturbed p epsilon delta := by
    ext w
    simp only [ActiveExtremum.feasible, perturbed, Set.mem_ofPred_eq, SquaredRadius.value, sub_eq_zero]
    rfl
  have ha : ActiveExtremum.activeMap (parameterMap p epsilon)
      (fun w => SquaredRadius.value w.2 - delta ^ 2) (activeSet p epsilon z) =
        ActiveRadius.fixedMap (constraintMap p epsilon) (activeSet p epsilon z) delta := rfl
  have h := ActiveExtremum.isLocalMaxOn_fiber (parameterMap p epsilon)
    (fun w => SquaredRadius.value w.2 - delta ^ 2) φ (activeSet p epsilon z) z
    (he.symm ▸ hz) (fun i => ((continuous_apply i).comp (contDiff_parameterMap p epsilon).continuous).continuousAt)
    (inactive_pos p epsilon delta z hz) (he.symm ▸ hmax)
  simpa only [ha] using h

theorem normalized_of_isMax (p : MvPolynomial ι ℤ) (epsilon delta : ℝ)
    (L : ((ι → ℝ) × (Constraint ι → ℝ)) →L[ℝ] ℝ) (z : (ι → ℝ) × (Constraint ι → ℝ))
    (hz : z ∈ perturbed p epsilon delta) (hmax : IsMaxOn L (perturbed p epsilon delta) z)
    (hregular : Function.Surjective (fderiv ℝ (ActiveRadius.fixedMap (constraintMap p epsilon)
      (activeSet p epsilon z) delta) z)) :
    ∃ Λ : Module.Dual ℝ ((activeSet p epsilon z → ℝ) × ℝ), ∀ h,
      L h = Λ (fderiv ℝ (ActiveRadius.fixedMap (constraintMap p epsilon) (activeSet p epsilon z) delta) z h) :=
  ActiveExtremum.exists_normalized _ _ z _ L (isLocalMaxOn_active_fiber p epsilon delta L z hz hmax)
    ((contDiff_fixedMap p epsilon delta _).hasStrictFDerivAt (by simp)) L.hasStrictFDerivAt hregular

theorem exists_critical_max (p : MvPolynomial ι ℤ) (epsilon delta : ℝ)
    (he : 0 ≤ epsilon) (hd : 0 ≤ delta) (hn : (perturbed p epsilon delta).Nonempty)
    (L : ((ι → ℝ) × (Constraint ι → ℝ)) →L[ℝ] ℝ)
    (hregular : ∀ (s : Finset (Constraint ι)) (z : (ι → ℝ) × (Constraint ι → ℝ)),
      z ∈ perturbed p epsilon delta → (∀ i ∈ s, parameterMap p epsilon z i = 0) →
      Function.Surjective (fderiv ℝ (ActiveRadius.fixedMap (constraintMap p epsilon) s delta) z)) :
    ∃ z ∈ perturbed p epsilon delta, IsMaxOn L (perturbed p epsilon delta) z ∧
      ∃ Λ : Module.Dual ℝ ((activeSet p epsilon z → ℝ) × ℝ), ∀ h,
        L h = Λ (fderiv ℝ (ActiveRadius.fixedMap (constraintMap p epsilon) (activeSet p epsilon z) delta) z h) := by
  obtain ⟨z, hz, hmax⟩ := (isCompact_perturbed p epsilon delta he hd).exists_isMaxOn hn L.continuous.continuousOn
  refine ⟨z, hz, hmax, normalized_of_isMax p epsilon delta L z hz hmax ?_⟩
  exact hregular _ z hz (fun i hi => (mem_activeSet p epsilon z i).mp hi)

end LeanCanny.Geometry.PolynomialPerturbation
