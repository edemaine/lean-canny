/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.SquaredRadius
import Mathlib.Tactic.Ring

/-! # Radius regularity for subsets of active constraints

For an active index set S, the fixed-radius derivative is onto precisely when
some shift outside S is nonzero or the weighted spatial derivative is nonzero.
This supplies the linear criterion for each sign stratum.
-/

@[expose] public section

namespace LeanCanny.Geometry.ActiveRadius
open scoped BigOperators

variable {E I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype I] [DecidableEq I]

noncomputable def restriction (s : Finset I) : (I → ℝ) →L[ℝ] (s → ℝ) :=
  ContinuousLinearMap.pi fun i : s => ContinuousLinearMap.proj i.val

omit [Fintype I] [DecidableEq I] in
@[simp] theorem restriction_apply (s : Finset I) (b : I → ℝ) (i : s) : restriction s b i = b i.val := rfl

noncomputable def extend (s : Finset I) (b : s → ℝ) (i : I) : ℝ := if h : i ∈ s then b ⟨i, h⟩ else 0

omit [Fintype I] in
theorem restriction_extend (s : Finset I) (b : s → ℝ) : restriction s (extend s b) = b := by
  funext i
  simp only [restriction_apply, extend, i.property, ↓reduceDIte]

def oneHot (j : I) (i : I) : ℝ := if i = j then 1 else 0

omit [Fintype I] in
theorem restriction_oneHot (s : Finset I) (j : I) (hj : j ∉ s) : restriction s (oneHot j) = 0 := by
  funext i
  have hi : i.val ≠ j := by intro h; exact hj (h ▸ i.property)
  simp only [restriction_apply, oneHot, hi, ↓reduceIte, Pi.zero_apply]

theorem derivative_oneHot (a : I → ℝ) (j : I) : SquaredRadius.derivative a (oneHot j) = 2 * a j := by
  rw [SquaredRadius.derivative_apply]
  simp [oneHot]

noncomputable def derivative (D : E →L[ℝ] (I → ℝ)) (a : I → ℝ) (s : Finset I) : E × (I → ℝ) →L[ℝ] (s → ℝ) × ℝ :=
  ((restriction s).comp (AdditiveSubmersion.derivative D)).prod
    ((SquaredRadius.derivative a).comp (ContinuousLinearMap.snd ℝ E (I → ℝ)))

omit [DecidableEq I] in
theorem derivative_apply (D : E →L[ℝ] (I → ℝ)) (a : I → ℝ) (s : Finset I) (w : E × (I → ℝ)) :
    derivative D a s w = ((fun i : s => D w.1 i.val + w.2 i.val), SquaredRadius.derivative a w.2) := by
  simp [derivative, restriction, AdditiveSubmersion.derivative]
  rfl

theorem surjective_of_full (D : E →L[ℝ] (I → ℝ)) (a : I → ℝ) (s : Finset I)
    (h : Function.Surjective (RadiusLinearization.fixedDerivative D (SquaredRadius.derivative a))) :
    Function.Surjective (derivative D a s) := by
  intro b
  obtain ⟨w, hw⟩ := h (extend s b.1, b.2)
  rw [RadiusLinearization.fixedDerivative_apply] at hw
  refine ⟨w, ?_⟩
  rw [derivative_apply]
  apply Prod.ext
  · funext i
    have hi := congrArg (fun v : (I → ℝ) × ℝ => v.1 i.val) hw
    simpa only [Pi.add_apply, extend, i.property, ↓reduceDIte] using hi
  · exact congrArg (fun v : (I → ℝ) × ℝ => v.2) hw

theorem surjective_of_outside (D : E →L[ℝ] (I → ℝ)) (a : I → ℝ) (s : Finset I)
    (j : I) (hj : j ∉ s) (ha : a j ≠ 0) : Function.Surjective (derivative D a s) := by
  intro b
  let L := SquaredRadius.derivative a
  let v := extend s b.1
  let e := oneHot j
  have hne : L e ≠ 0 := by rw [derivative_oneHot]; exact mul_ne_zero (by norm_num) ha
  let t := (b.2 - L v) / L e
  refine ⟨(0, v + t • e), ?_⟩
  rw [derivative_apply]
  apply Prod.ext
  · change restriction s (D 0 + (v + t • e)) = b.1
    simp only [map_zero, zero_add, map_add, map_smul, v, e, restriction_extend,
      restriction_oneHot s j hj, smul_zero, add_zero]
  · change L (v + t • e) = b.2
    rw [map_add, map_smul]
    change L v + ((b.2 - L v) / L e) * L e = b.2
    rw [div_mul_cancel₀ _ hne]
    ring

theorem derivative_surjective_iff (D : E →L[ℝ] (I → ℝ)) (a : I → ℝ) (s : Finset I) :
    Function.Surjective (derivative D a s) ↔
      (∃ j, j ∉ s ∧ a j ≠ 0) ∨ (SquaredRadius.derivative a).comp D ≠ 0 := by
  constructor
  · intro h
    by_cases hout : ∃ j, j ∉ s ∧ a j ≠ 0
    · exact Or.inl hout
    · apply Or.inr
      intro hz
      obtain ⟨w, hw⟩ := h (0, 1)
      rw [derivative_apply] at hw
      have hh : ∀ i : s, D w.1 i.val + w.2 i.val = 0 :=
        fun i => congrArg (fun v : (s → ℝ) × ℝ => v.1 i) hw
      have ht : SquaredRadius.derivative a w.2 = 1 := congrArg Prod.snd hw
      have hd : SquaredRadius.derivative a (D w.1) = 0 :=
        congrArg (fun M : E →L[ℝ] ℝ => M w.1) hz
      have hs : SquaredRadius.derivative a (D w.1 + w.2) = 0 := by
        rw [SquaredRadius.derivative_apply]
        have hsum : (∑ i, a i * (D w.1 i + w.2 i)) = 0 := by
          apply Finset.sum_eq_zero
          intro i _
          by_cases hi : i ∈ s
          · rw [hh ⟨i, hi⟩, mul_zero]
          · have ha : a i = 0 := by by_contra hn; exact hout ⟨i, hi, hn⟩
            rw [ha, zero_mul]
        simp only [Pi.add_apply, hsum, mul_zero]
      rw [map_add, hd, ht, zero_add] at hs
      exact one_ne_zero hs
  · rintro (⟨j, hj, ha⟩ | h)
    · exact surjective_of_outside D a s j hj ha
    · exact surjective_of_full D a s ((RadiusLinearization.fixedDerivative_surjective_iff D _).mpr h)

end LeanCanny.Geometry.ActiveRadius
