/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.IsolatedCriticalMaximum
public import LeanCanny.Geometry.TubeSigns
public import Mathlib.Topology.Algebra.Module.Equiv.Pi

/-! # Finite active critical sets supply strict tube maxima

Finiteness of normalized critical points on each regular active fiber makes
an inequality-set projection maximum strict on its active zero locus. The
existing tube approximation then preserves all positive inactive signs.
Finiteness of critical sets remains a hypothesis, not a genericity theorem.
-/

@[expose] public section

namespace LeanCanny.Geometry.TubePolynomial
open Set Filter
open scoped Topology

variable {ι : Type*}

noncomputable def splitPointEquiv : (Coordinate ι → ℝ) ≃L[ℝ]
    (ι → ℝ) × (PolynomialPerturbation.Constraint ι → ℝ) :=
  ContinuousLinearEquiv.sumPiEquivProdPi ℝ ι (PolynomialPerturbation.Constraint ι) (fun _ => ℝ)

theorem splitPointEquiv_apply (x : Coordinate ι → ℝ) : splitPointEquiv x = splitPoint x := rfl

theorem splitPointEquiv_symm_apply (z : (ι → ℝ) × (PolynomialPerturbation.Constraint ι → ℝ)) :
    splitPointEquiv.symm z = point z := rfl

variable [Fintype ι]

noncomputable def splitProjection (v : Coordinate ι → ℝ) :
    ((ι → ℝ) × (PolynomialPerturbation.Constraint ι → ℝ)) →L[ℝ] ℝ :=
  (ProjectionCritical.projection v).comp splitPointEquiv.symm.toContinuousLinearMap

theorem splitProjection_apply (v : Coordinate ι → ℝ)
    (z : (ι → ℝ) × (PolynomialPerturbation.Constraint ι → ℝ)) :
    splitProjection v z = ProjectionCritical.projection v (point z) := rfl

def activeCriticalSet (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι))
    (epsilon delta : ℝ) (v : Coordinate ι → ℝ) :
    Set ((ι → ℝ) × (PolynomialPerturbation.Constraint ι → ℝ)) :=
  {z | z ∈ IsolatedCriticalMaximum.criticalFiber
    (ActiveRadius.fixedMap (PolynomialPerturbation.constraintMap p epsilon) s delta) (splitProjection v) 0}

def FiniteActiveCriticalSets (p : MvPolynomial ι ℤ) (epsilon delta : ℝ) (v : Coordinate ι → ℝ) : Prop :=
  ∀ s : Finset (PolynomialPerturbation.Constraint ι), (activeCriticalSet p s epsilon delta v).Finite

def RegularActiveFibers (p : MvPolynomial ι ℤ) (epsilon delta : ℝ) : Prop :=
  ∀ (s : Finset (PolynomialPerturbation.Constraint ι)) (z : (ι → ℝ) × (PolynomialPerturbation.Constraint ι → ℝ)),
    (∀ i ∈ s, PolynomialPerturbation.parameterMap p epsilon z i = 0) →
      SquaredRadius.value z.2 = delta ^ 2 →
        Function.Surjective (fderiv ℝ (ActiveRadius.fixedMap (PolynomialPerturbation.constraintMap p epsilon) s delta) z)

theorem fixedMap_eq_zero_iff (p : MvPolynomial ι ℤ) (s : Finset (PolynomialPerturbation.Constraint ι))
    (epsilon delta : ℝ) (z : (ι → ℝ) × (PolynomialPerturbation.Constraint ι → ℝ)) :
    ActiveRadius.fixedMap (PolynomialPerturbation.constraintMap p epsilon) s delta z = 0 ↔
      (∀ i ∈ s, PolynomialPerturbation.parameterMap p epsilon z i = 0) ∧ SquaredRadius.value z.2 = delta ^ 2 := by
  constructor
  · intro h
    constructor
    · intro i hi
      exact congrArg (fun w : (s → ℝ) × ℝ => w.1 ⟨i, hi⟩) h
    · have hr := congrArg Prod.snd h
      exact sub_eq_zero.mp hr
  · rintro ⟨ha, hr⟩
    apply Prod.ext
    · funext i
      exact ha i i.property
    · exact sub_eq_zero.mpr hr

theorem strict_maximum_of_finite_critical (p : MvPolynomial ι ℤ) (epsilon delta : ℝ)
    (v : Coordinate ι → ℝ) (z : (ι → ℝ) × (PolynomialPerturbation.Constraint ι → ℝ))
    (hz : z ∈ PolynomialPerturbation.perturbed p epsilon delta)
    (hmax : IsMaxOn (splitProjection v) (PolynomialPerturbation.perturbed p epsilon delta) z)
    (hregular : RegularActiveFibers p epsilon delta)
    (hfinite : (activeCriticalSet p (PolynomialPerturbation.activeSet p epsilon z) epsilon delta v).Finite) :
    StrictLocalMaximum p (PolynomialPerturbation.activeSet p epsilon z) epsilon delta v z := by
  let s := PolynomialPerturbation.activeSet p epsilon z
  let f := ActiveRadius.fixedMap (PolynomialPerturbation.constraintMap p epsilon) s delta
  have hfz : f z = 0 := (fixedMap_eq_zero_iff p s epsilon delta z).mpr
    ⟨fun i hi => (PolynomialPerturbation.mem_activeSet p epsilon z i).mp hi, hz.2⟩
  have hr : ∀ x, f x = f z → Function.Surjective (fderiv ℝ f x) := by
    intro x hx
    obtain ⟨ha, hrad⟩ := (fixedMap_eq_zero_iff p s epsilon delta x).mp (hx.trans hfz)
    exact hregular s x ha hrad
  have hfin : (IsolatedCriticalMaximum.criticalFiber f (splitProjection v) (f z)).Finite := by
    rw [hfz]
    exact hfinite
  have hs := IsolatedCriticalMaximum.strict_of_finite_critical f (splitProjection v) z
    (PolynomialPerturbation.contDiff_fixedMap p epsilon delta s) hr hfin
    (PolynomialPerturbation.isLocalMaxOn_active_fiber p epsilon delta (splitProjection v) z hz hmax)
  have hsplit : Tendsto (splitPoint : (Coordinate ι → ℝ) → _) (nhds (point z)) (nhds z) := by
    simpa only [splitPoint_point] using continuous_splitPoint.tendsto (point z)
  have hnear := hsplit.eventually hs
  filter_upwards [hnear] with x hx hxzero hne
  have hfzero := (fixedMap_eq_zero_iff p s epsilon delta (splitPoint x)).mpr
    ((mem_zeroLocus_iff p s epsilon delta x).mp hxzero).symm
  have hsplit : splitPoint x ≠ z := by
    intro heq
    exact hne ((point_splitPoint x).symm.trans (congrArg point heq))
  have h := hx (hfzero.trans hfz.symm) hsplit
  simpa only [splitProjection_apply, point_splitPoint] using h

theorem active_approximation_of_finite_critical (p : MvPolynomial ι ℤ) (epsilon delta : ℝ)
    (v : Coordinate ι → ℝ) (z : (ι → ℝ) × (PolynomialPerturbation.Constraint ι → ℝ))
    (hd : 0 < delta) (hz : z ∈ PolynomialPerturbation.perturbed p epsilon delta)
    (hmax : IsMaxOn (splitProjection v) (PolynomialPerturbation.perturbed p epsilon delta) z)
    (hv : v (base ι) = 1) (hregular : RegularActiveFibers p epsilon delta)
    (hfinite : (activeCriticalSet p (PolynomialPerturbation.activeSet p epsilon z) epsilon delta v).Finite) :
    CriticalApproximationWithPositiveInactive p (PolynomialPerturbation.activeSet p epsilon z) epsilon delta v z :=
  active_approximation_of_strict p epsilon delta v z hd hz hv
    (strict_maximum_of_finite_critical p epsilon delta v z hz hmax hregular hfinite)

theorem exists_active_approximation (p : MvPolynomial ι ℤ) (epsilon delta : ℝ)
    (v : Coordinate ι → ℝ) (he : 0 ≤ epsilon) (hd : 0 < delta)
    (hn : (PolynomialPerturbation.perturbed p epsilon delta).Nonempty)
    (hv : v (base ι) = 1) (hregular : RegularActiveFibers p epsilon delta)
    (hfinite : FiniteActiveCriticalSets p epsilon delta v) :
    ∃ z ∈ PolynomialPerturbation.perturbed p epsilon delta,
      CriticalApproximationWithPositiveInactive p (PolynomialPerturbation.activeSet p epsilon z) epsilon delta v z := by
  obtain ⟨z, hz, hm⟩ := (PolynomialPerturbation.isCompact_perturbed p epsilon delta he hd.le).exists_isMaxOn
    hn (splitProjection v).continuous.continuousOn
  exact ⟨z, hz, active_approximation_of_finite_critical p epsilon delta v z hd hz hm hv hregular (hfinite _)⟩

end LeanCanny.Geometry.TubePolynomial
