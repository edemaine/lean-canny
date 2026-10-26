/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.BoundedRegularSource

/-! # Exact level semantics of the bounded regular source

Scaling the source and shifting before regularization gives an actual integer
pure-power hypersurface. Its zero set is homeomorphic to the pure-power lift
at the safe shifted level, retaining the original component-preserving window.
-/

@[expose] public section
namespace LeanCanny.Geometry.BoundedRegularSource
open MvPolynomial Set LeanCanny.Algebra BoundedZeroSource
open scoped BigOperators

variable {n : ℕ}

noncomputable def scaledEnergy (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ) (w : Fin (n + 2) → ℝ) : ℝ :=
  (2 : ℝ) ^ perturbationExponent n D b R * (BoundedZeroSource.polynomial q R).eval₂ (Int.castRingHom ℝ) w +
    ∑ i : Fin (n + 2), w i ^ powerDegree D

theorem coefficient_mul_scale (n D b R : ℕ) :
    perturbationCoefficient n D b R * (2 : ℝ) ^ perturbationExponent n D b R = 1 := by
  unfold perturbationCoefficient InfinitesimalSign.dyadic
  exact inv_mul_cancel₀ (by positivity)

theorem perturbed_sublevel_iff (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ) (w : Fin (n + 2) → ℝ) :
    (BoundedZeroSource.polynomial q R).eval₂ (Int.castRingHom ℝ) w +
        perturbationCoefficient n D b R * ∑ i : Fin (n + 2), w i ^ powerDegree D ≤ originalLevel n D b R ↔
      scaledEnergy q D b R w ≤ level n D b R := by
  have he : (BoundedZeroSource.polynomial q R).eval₂ (Int.castRingHom ℝ) w +
      perturbationCoefficient n D b R * ∑ i : Fin (n + 2), w i ^ powerDegree D =
      perturbationCoefficient n D b R * scaledEnergy q D b R w := by
    unfold scaledEnergy
    rw [mul_add, ← mul_assoc, coefficient_mul_scale, one_mul]
  rw [he, originalLevel]
  exact mul_le_mul_iff_right₀
    (BoundedPositivePerturbation.coefficient_pos (n + 2) (degreeAllowance D) (massExponent n b R) (penaltyExponent n D R))

theorem eval_shifted (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ) (p : (Fin (n + 2) → ℝ) × ℂ) :
    (FermatCriticalHomogenization.polynomial (lower q D b R) 1 (powerDegree D)).eval₂ (Int.castRingHom ℝ)
        (BoundedZeroSource.coordinates p) =
      PurePowerSublevelLift.energy (powerHalfDegree D) (scaledEnergy q D b R) p - (2 : ℝ) ^ penaltyExponent n D R := by
  simp only [FermatCriticalHomogenization.polynomial, lower, eval₂_add, eval₂_sub, eval₂_mul, eval₂_C,
    eval₂_rename, Function.comp_def, Int.coe_castRingHom, Int.cast_pow, Int.cast_ofNat, Int.cast_one,
    one_mul, eval₂_sum, eval₂_pow, eval₂_X]
  rw [BoundedZeroSource.power_sum_coordinates]
  simp only [BoundedZeroSource.coordinates_apply, Fin.append_left, PurePowerSublevelLift.energy,
    PurePowerSublevelLift.penalty, scaledEnergy, powerDegree]
  ring

theorem eval_polynomial_coordinates (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ)
    (p : (Fin (n + 2) → ℝ) × ℂ) :
    (polynomial q D b R).eval₂ (Int.castRingHom ℝ) (BoundedZeroSource.coordinates p) =
      (2 : ℝ) ^ regularizationExponent n D b R *
        (PurePowerSublevelLift.energy (powerHalfDegree D) (scaledEnergy q D b R) p -
          (2 : ℝ) ^ penaltyExponent n D R) - 1 := by
  change (FermatCriticalHomogenization.polynomial _ _ _).eval₂ _ _ = _
  rw [IntegerRegularSource.polynomial_eq, eval₂_sub, eval₂_mul, eval₂_C, eval₂_one, eval_shifted]
  simp only [IntegerRegularSource.scale, regularizationExponent, Int.coe_castRingHom, Int.cast_pow, Int.cast_ofNat]

theorem zero_coordinates (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ) (p : (Fin (n + 2) → ℝ) × ℂ) :
    (polynomial q D b R).eval₂ (Int.castRingHom ℝ) (BoundedZeroSource.coordinates p) = 0 ↔
      PurePowerSublevelLift.energy (powerHalfDegree D) (scaledEnergy q D b R) p = level n D b R := by
  have hs : (2 : ℝ) ^ regularizationExponent n D b R ≠ 0 := by positivity
  rw [eval_polynomial_coordinates]
  unfold level InfinitesimalSign.dyadic
  constructor
  · intro h
    have hm : PurePowerSublevelLift.energy (powerHalfDegree D) (scaledEnergy q D b R) p -
        (2 : ℝ) ^ penaltyExponent n D R = ((2 : ℝ) ^ regularizationExponent n D b R)⁻¹ := by
      apply mul_left_cancel₀ hs
      rw [mul_inv_cancel₀ hs]
      exact sub_eq_zero.mp h
    linarith
  · intro h
    rw [h, add_sub_cancel_left, mul_inv_cancel₀ hs, sub_self]

noncomputable def Zeros (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ) :=
  {w : Fin (n + 4) → ℝ | (polynomial q D b R).eval₂ (Int.castRingHom ℝ) w = 0}

noncomputable def levelHomeomorph (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ) :
    Zeros q D b R ≃ₜ PurePowerSublevelLift.Total (powerHalfDegree D) (scaledEnergy q D b R) (level n D b R) :=
  (BoundedZeroSource.coordinates.symm.sets (by
    ext w
    change (polynomial q D b R).eval₂ (Int.castRingHom ℝ) w = 0 ↔
      PurePowerSublevelLift.energy (powerHalfDegree D) (scaledEnergy q D b R) (BoundedZeroSource.coordinates.symm w) = level n D b R
    have h := zero_coordinates q D b R (BoundedZeroSource.coordinates.symm w)
    simpa only [Homeomorph.apply_symm_apply] using h))

theorem continuous_scaledEnergy (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ) :
    Continuous (scaledEnergy q D b R) :=
  (continuous_const.mul (ProjectionCritical.contDiff_eval (Int.castRingHom ℝ) (BoundedZeroSource.polynomial q R)).continuous).add
    (continuous_finsetSum _ (fun i _ => (continuous_apply i).pow _))

theorem nonneg_scaledEnergy (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ) (w : Fin (n + 2) → ℝ) :
    0 ≤ scaledEnergy q D b R w :=
  add_nonneg (mul_nonneg (by positivity) (BoundedZeroSource.nonneg q R w))
    (Finset.sum_nonneg (fun i _ => (powerDegree_even D).pow_nonneg (w i)))

theorem compact_scaled_sublevels (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ) (e : ℝ) :
    IsCompact (CircleSublevelLift.Base (scaledEnergy q D b R) e) := by
  have hs : 0 < (2 : ℝ) ^ perturbationExponent n D b R := by positivity
  have hc : IsClosed (CircleSublevelLift.Base (scaledEnergy q D b R) e) :=
    isClosed_le (continuous_scaledEnergy q D b R) continuous_const
  apply (BoundedZeroSource.compact_sublevels q R (e / (2 : ℝ) ^ perturbationExponent n D b R)).of_isClosed_subset hc
  intro w hw
  change (BoundedZeroSource.polynomial q R).eval₂ (Int.castRingHom ℝ) w ≤ _
  apply (le_div_iff₀ hs).mpr
  have hn : 0 ≤ ∑ i : Fin (n + 2), w i ^ powerDegree D :=
    Finset.sum_nonneg (fun i _ => (powerDegree_even D).pow_nonneg (w i))
  change (2 : ℝ) ^ perturbationExponent n D b R *
    (BoundedZeroSource.polynomial q R).eval₂ (Int.castRingHom ℝ) w + _ ≤ e at hw
  nlinarith

theorem proper (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ) :
    IsProperMap (fun w : Fin (n + 4) → ℝ => (polynomial q D b R).eval₂ (Int.castRingHom ℝ) w) := by
  let post : ℝ → ℝ := fun t => (t + 1) / (2 : ℝ) ^ regularizationExponent n D b R + (2 : ℝ) ^ penaltyExponent n D R
  have hg := PurePowerSublevelLift.proper_energy (powerHalfDegree D) (powerHalfDegree_odd D)
    (scaledEnergy q D b R) (continuous_scaledEnergy q D b R) (nonneg_scaledEnergy q D b R)
    (compact_scaled_sublevels q D b R)
  have he : post ∘ (fun w : Fin (n + 4) → ℝ => (polynomial q D b R).eval₂ (Int.castRingHom ℝ) w) =
      PurePowerSublevelLift.energy (powerHalfDegree D) (scaledEnergy q D b R) ∘ BoundedZeroSource.coordinates.symm := by
    funext w
    have hv := eval_polynomial_coordinates q D b R (BoundedZeroSource.coordinates.symm w)
    simp only [Homeomorph.apply_symm_apply] at hv
    change ((polynomial q D b R).eval₂ (Int.castRingHom ℝ) w + 1) /
      (2 : ℝ) ^ regularizationExponent n D b R + (2 : ℝ) ^ penaltyExponent n D R = _
    rw [hv]
    simp only [Function.comp_apply]
    field_simp
    ring
  apply isProperMap_of_comp_of_t2 (ProjectionCritical.contDiff_eval (Int.castRingHom ℝ) (polynomial q D b R)).continuous
    (show Continuous post by unfold post; fun_prop)
  rw [he]
  exact hg.comp BoundedZeroSource.coordinates.symm.isProperMap

theorem zero_in_scaled_sublevel (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ) (w : BoundedZeroSource.Zeros q R) :
    scaledEnergy q D b R w.val ≤ level n D b R := by
  apply (perturbed_sublevel_iff q D b R w.val).mp
  rw [show (BoundedZeroSource.polynomial q R).eval₂ (Int.castRingHom ℝ) w.val = 0 from w.property, zero_add]
  have hp := BoundedPositivePerturbation.penalty_bound (powerDegree D) R w.val (zero_coordinate_bound q R w.val w.property)
  have hη : 0 ≤ perturbationCoefficient n D b R :=
    (BoundedPositivePerturbation.coefficient_pos (n + 2) (degreeAllowance D) (massExponent n b R) (penaltyExponent n D R)).le
  exact ((mul_le_mul_of_nonneg_left hp hη).trans_eq
    (BoundedPositivePerturbation.coefficient_mul_pow (n + 2) (degreeAllowance D) (massExponent n b R)
      (penaltyExponent n D R))).trans (originalLevel_window n D b R).1

noncomputable def basePoint (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ) (x : Bounded q R) :
    CircleSublevelLift.Base (scaledEnergy q D b R) (level n D b R) :=
  ⟨(sectionMap q R x).val, zero_in_scaled_sublevel q D b R (sectionMap q R x)⟩

noncomputable def lift (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ) (x : Bounded q R) : Zeros q D b R :=
  (levelHomeomorph q D b R).symm (PurePowerSublevelLift.sectionMap (powerHalfDegree D) (powerHalfDegree_odd D)
    (scaledEnergy q D b R) (level n D b R) (basePoint q D b R x))

theorem component_coordinates (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ) (w v : Zeros q D b R) :
    v ∈ connectedComponent w ↔ levelHomeomorph q D b R v ∈ connectedComponent (levelHomeomorph q D b R w) := by
  constructor
  · exact fun h => (levelHomeomorph q D b R).continuous.mapsTo_connectedComponent w h
  · intro h
    simpa only [Homeomorph.symm_apply_apply] using
      (levelHomeomorph q D b R).symm.continuous.mapsTo_connectedComponent (levelHomeomorph q D b R w) h

theorem component_iff_lift (q : MvPolynomial (Fin n) ℤ) (D b R : ℕ)
    (hD : q.totalDegree ≤ D) (hb : MvMass.mass q ≤ 2 ^ b) (x y : Bounded q R) :
    y.val ∈ connectedComponentIn (Bounded q R) x.val ↔ lift q D b R y ∈ connectedComponent (lift q D b R x) := by
  have hset : {w : Fin (n + 2) → ℝ | (BoundedZeroSource.polynomial q R).eval₂ (Int.castRingHom ℝ) w +
      perturbationCoefficient n D b R * ∑ i : Fin (n + 2), w i ^ powerDegree D ≤ originalLevel n D b R} =
      CircleSublevelLift.Base (scaledEnergy q D b R) (level n D b R) := by
    ext w
    exact perturbed_sublevel_iff q D b R w
  have hc := BoundedZeroSource.component_iff_perturbed q D b R hD hb (originalLevel n D b R)
    (originalLevel_window n D b R).1 (originalLevel_window n D b R).2 x y
  rw [hset] at hc
  have hp := PurePowerSublevelLift.section_component_iff (powerHalfDegree D) (powerHalfDegree_odd D)
    (scaledEnergy q D b R) (continuous_scaledEnergy q D b R) (level n D b R) (basePoint q D b R x) (basePoint q D b R y)
  have hh := component_coordinates q D b R (lift q D b R x) (lift q D b R y)
  simp only [lift, Homeomorph.apply_symm_apply] at hh
  exact hc.trans (hp.symm.trans hh.symm)

end LeanCanny.Geometry.BoundedRegularSource
