/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.ActiveRadiusLinearization
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Singular fixed-radius strata give critical sum-of-squares values

At a zero of the active shifted constraints, a singular derivative forces all
inactive shifts to vanish. Its weighted spatial derivative is the negative of
the derivative of the active sum of squares. The squared radius is consequently
a critical value of that function. Finiteness of these critical values remains
a separate algebraic obligation.
-/

@[expose] public section

namespace LeanCanny.Geometry.ActiveRadius
open scoped BigOperators

variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype I] [DecidableEq I]

noncomputable def fixedMap (f : E → I → ℝ) (s : Finset I) (delta : ℝ) (z : E × (I → ℝ)) : (s → ℝ) × ℝ :=
  (restriction s (f z.1 + z.2), SquaredRadius.value z.2 - delta ^ 2)

omit [DecidableEq I] in
theorem hasFDerivAt_fixedMap (f : E → I → ℝ) (s : Finset I) (delta : ℝ) (z : E × (I → ℝ))
    (D : E →L[ℝ] (I → ℝ)) (hf : HasFDerivAt f D z.1) :
    HasFDerivAt (fixedMap f s delta) (derivative D z.2 s) z := by
  have hh := (restriction s).hasFDerivAt.comp z (AdditiveSubmersion.hasFDerivAt f z D hf)
  have hr := ((SquaredRadius.hasFDerivAt z.2).comp z hasFDerivAt_snd).sub_const (delta ^ 2)
  exact hh.prodMk hr

theorem fderiv_surjective_iff (f : E → I → ℝ) (s : Finset I) (delta : ℝ) (z : E × (I → ℝ))
    (hf : DifferentiableAt ℝ f z.1) :
    Function.Surjective (fderiv ℝ (fixedMap f s delta) z) ↔
      (∃ j, j ∉ s ∧ z.2 j ≠ 0) ∨ (SquaredRadius.derivative z.2).comp (fderiv ℝ f z.1) ≠ 0 := by
  rw [(hasFDerivAt_fixedMap f s delta z _ hf.hasFDerivAt).fderiv]
  exact derivative_surjective_iff _ _ _

noncomputable def energy (f : E → I → ℝ) (s : Finset I) (x : E) : ℝ := ∑ i ∈ s, f x i ^ 2

noncomputable def energyDerivative (f : E → I → ℝ) (s : Finset I) (x : E) (D : E →L[ℝ] (I → ℝ)) : E →L[ℝ] ℝ :=
  ∑ i ∈ s, (2 * f x i) • (ContinuousLinearMap.proj i).comp D

omit [DecidableEq I] in
theorem hasFDerivAt_energy (f : E → I → ℝ) (s : Finset I) (x : E) (D : E →L[ℝ] (I → ℝ))
    (hf : HasFDerivAt f D x) : HasFDerivAt (energy f s) (energyDerivative f s x D) x := by
  unfold energy energyDerivative
  apply HasFDerivAt.fun_sum
  intro i _
  simpa only [Function.comp_apply, show 2 - 1 = 1 from rfl, pow_one, two_nsmul, two_mul] using
    ((hasFDerivAt_apply (𝕜 := ℝ) i (f x)).comp x hf).pow 2

omit [Fintype I] [DecidableEq I] in
theorem energyDerivative_apply (f : E → I → ℝ) (s : Finset I) (x h : E) (D : E →L[ℝ] (I → ℝ)) :
    energyDerivative f s x D h = ∑ i ∈ s, 2 * f x i * D h i := by
  simp [energyDerivative]

omit [DecidableEq I] in
theorem weighted_eq_neg_energy (f : E → I → ℝ) (s : Finset I) (x : E) (a : I → ℝ)
    (D : E →L[ℝ] (I → ℝ)) (hout : ∀ i, i ∉ s → a i = 0) (hin : ∀ i ∈ s, a i = -f x i) :
    (SquaredRadius.derivative a).comp D = -energyDerivative f s x D := by
  ext h
  rw [ContinuousLinearMap.comp_apply, SquaredRadius.derivative_apply, neg_apply,
    energyDerivative_apply]
  have hs : (∑ i : I, a i * D h i) = -(∑ i ∈ s, f x i * D h i) := by
    calc
      _ = ∑ i ∈ s, a i * D h i := (Finset.sum_subset (s.subset_univ)
        (fun i _ hi => by rw [hout i hi, zero_mul])).symm
      _ = _ := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro i hi
        rw [hin i hi, neg_mul]
  rw [hs, mul_neg, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [DecidableEq I] in
theorem radius_eq_energy (f : E → I → ℝ) (s : Finset I) (x : E) (a : I → ℝ)
    (hout : ∀ i, i ∉ s → a i = 0) (hin : ∀ i ∈ s, a i = -f x i) : SquaredRadius.value a = energy f s x := by
  unfold SquaredRadius.value energy
  calc
    _ = ∑ i ∈ s, a i ^ 2 := (Finset.sum_subset s.subset_univ (fun i _ hi => by rw [hout i hi, zero_pow (by decide)])).symm
    _ = _ := Finset.sum_congr rfl fun i hi => by rw [hin i hi, neg_sq]

theorem singular_implies_critical (f : E → I → ℝ) (s : Finset I) (delta : ℝ) (z : E × (I → ℝ))
    (hf : DifferentiableAt ℝ f z.1) (hz : ∀ i ∈ s, f z.1 i + z.2 i = 0)
    (hr : SquaredRadius.value z.2 = delta ^ 2)
    (hs : ¬ Function.Surjective (fderiv ℝ (fixedMap f s delta) z)) :
    energy f s z.1 = delta ^ 2 ∧ fderiv ℝ (energy f s) z.1 = 0 := by
  have hn := (fderiv_surjective_iff f s delta z hf).not.mp hs
  have hout : ∀ i, i ∉ s → z.2 i = 0 := by
    intro i hi
    by_contra ha
    exact hn (Or.inl ⟨i, hi, ha⟩)
  have hw : (SquaredRadius.derivative z.2).comp (fderiv ℝ f z.1) = 0 := by
    by_contra h
    exact hn (Or.inr h)
  have hin : ∀ i ∈ s, z.2 i = -f z.1 i := fun i hi => by linarith [hz i hi]
  refine ⟨(radius_eq_energy f s z.1 z.2 hout hin).symm.trans hr, ?_⟩
  rw [(hasFDerivAt_energy f s z.1 _ hf.hasFDerivAt).fderiv]
  have he := (weighted_eq_neg_energy f s z.1 z.2 _ hout hin).symm.trans hw
  exact neg_eq_zero.mp he

end LeanCanny.Geometry.ActiveRadius
