/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.FermatLevelCritical
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Topology.Homeomorph.Lemmas

/-! # A unique continuous bounded level sheet over its precise value region

On [-1,1], A*v-v^d is strictly increasing when A>d. Its inverse is continuous
on its actual range. Even d gives a level for every |w|≤A-1. No assertion
identifies this projected region with an original polynomial zero set.
-/
@[expose] public section
namespace LeanCanny.Geometry.FermatLevelSheet
open Set
open scoped Topology

abbrev Interval := Icc (-1:ℝ) 1
abbrev Values (A : ℤ) := {w : ℝ | |w|≤(A:ℝ)-1}

def forward (d : ℕ) (A : ℤ) (v : ℝ) : ℝ := (A:ℝ)*v-v^d

theorem hasDerivAt_forward (d : ℕ) (A : ℤ) (v : ℝ) :
    HasDerivAt (forward d A) ((A:ℝ)-(d:ℝ)*v^(d-1)) v := by
  have H := ((hasDerivAt_id v).const_mul (A:ℝ)).sub ((hasDerivAt_id v).pow d)
  have HF : ((fun y : ℝ => (A:ℝ)*id y)-id^d)=forward d A := by
    funext y
    simp only [Pi.sub_apply,Pi.pow_apply,id_eq,forward]
  rw [HF] at H
  simpa only [mul_one,id_eq] using H

theorem strictMonoOn_forward (d : ℕ) (A : ℤ) (hA : (d:ℝ)<(A:ℝ)) :
    StrictMonoOn (forward d A) (Icc (-1:ℝ) 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc (-1:ℝ) 1) (by unfold forward; fun_prop)
  intro v hv
  rw [(hasDerivAt_forward d A v).deriv]
  have HV : |v|≤1 := abs_le.mpr (interior_subset hv)
  have HP : v^(d-1)≤1 := (le_abs_self _).trans (by
    rw [abs_pow]
    simpa using pow_le_pow_left₀ (abs_nonneg v) HV (d-1))
  have HM := mul_le_mul_of_nonneg_left HP (Nat.cast_nonneg (α:=ℝ) d)
  nlinarith only [HM,hA]

def boundedForward (d : ℕ) (A : ℤ) : Interval → ℝ := fun v => forward d A v.val

theorem continuous_boundedForward (d : ℕ) (A : ℤ) : Continuous (boundedForward d A) := by
  unfold boundedForward forward
  fun_prop

theorem boundedForward_injective (d : ℕ) (A : ℤ) (hA : (d:ℝ)<(A:ℝ)) :
    Function.Injective (boundedForward d A) := by
  intro v w h
  apply Subtype.ext
  exact (strictMonoOn_forward d A hA).injOn v.property w.property h

noncomputable def rangeHomeomorph (d : ℕ) (A : ℤ) (hA : (d:ℝ)<(A:ℝ)) :
    Interval ≃ₜ Set.range (boundedForward d A) :=
  ((continuous_boundedForward d A).isClosedEmbedding (boundedForward_injective d A hA)).toIsEmbedding.toHomeomorph

theorem values_subset_range (d : ℕ) (A : ℤ) (hd : Even d) :
    Values A⊆Set.range (boundedForward d A) := by
  intro w hw
  obtain ⟨v,hv,hroot⟩ := FermatLevelCritical.exists_level w A d hd hw
  refine ⟨⟨v,hv⟩,?_⟩
  change (A:ℝ)*v-v^d=w
  linarith

noncomputable def valueInput (d : ℕ) (A : ℤ) (hd : Even d) :
    Values A → Set.range (boundedForward d A) := fun w => ⟨w.val,values_subset_range d A hd w.property⟩

theorem continuous_valueInput (d : ℕ) (A : ℤ) (hd : Even d) : Continuous (valueInput d A hd) :=
  continuous_subtype_val.subtype_mk _

noncomputable def level (d : ℕ) (A : ℤ) (hd : Even d) (hA : (d:ℝ)<(A:ℝ)) : Values A → Interval :=
  (rangeHomeomorph d A hA).symm ∘ valueInput d A hd

theorem continuous_level (d : ℕ) (A : ℤ) (hd : Even d) (hA : (d:ℝ)<(A:ℝ)) : Continuous (level d A hd hA) :=
  (rangeHomeomorph d A hA).symm.continuous.comp (continuous_valueInput d A hd)

theorem level_equation (d : ℕ) (A : ℤ) (hd : Even d) (hA : (d:ℝ)<(A:ℝ)) (w : Values A) :
    w.val+(level d A hd hA w).val^d-(A:ℝ)*(level d A hd hA w).val=0 := by
  have H := congrArg Subtype.val ((rangeHomeomorph d A hA).apply_symm_apply (valueInput d A hd w))
  change forward d A (level d A hd hA w).val=w.val at H
  unfold forward at H
  linarith

theorem level_unique (d : ℕ) (A : ℤ) (hd : Even d) (hA : (d:ℝ)<(A:ℝ)) (w : Values A)
    (v : Interval) (hv : w.val+v.val^d-(A:ℝ)*v.val=0) : v=level d A hd hA w := by
  apply boundedForward_injective d A hA
  have H := level_equation d A hd hA w
  change (A:ℝ)*v.val-v.val^d=(A:ℝ)*(level d A hd hA w).val-(level d A hd hA w).val^d
  linarith

end LeanCanny.Geometry.FermatLevelSheet
