/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedSelectedBadMembership
/-! # A sweep's unused companion field does not change its ordinary bad set -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedSweepRetarget
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedRelativeCuts
open LeanCanny.Connectivity.IntegralMixedSelectedCriticalCuts
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

noncomputable def choices (x : State P S B m ι) (hm : m≤S) (r : Rule n) (j : ℕ)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (c : Choices x hm r φ) : Choices x hm (rule r j) φ where
 coordinateIndex:=c.coordinateIndex
 coordinateValid:=c.coordinateValid
 squarefreeIndex:=c.squarefreeIndex
 squarefreeValid:=c.squarefreeValid
 valueIndex:=c.valueIndex
 valueValid:=c.valueValid
 limitIndex:=c.limitIndex
 limitValid:=c.limitValid

theorem bad_choices_eq (x : State P S B m ι) (hm : m≤S) (r : Rule n) (j : ℕ)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (c : Choices x hm r φ) :
    bad x hm (rule r j) φ (choices x hm r j φ c)=bad x hm r φ c:=by
 ext a
 constructor <;> rintro ⟨⟨tag,k⟩,hk⟩ <;> refine ⟨(tag,k),?_⟩
 all_goals fin_cases tag <;> exact hk

theorem bad_iff (x : State P S B m ι) (hm : m≤S) (r : Rule n) (j : ℕ)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (c : Choices x hm r φ)
    (e : Choices x hm (rule r j) φ) (a : ℝ) :
    a∈bad x hm (rule r j) φ e ↔a∈bad x hm r φ c:=by
 rw [IntegralMixedCurrentQCoordinateScaling.bad_choices_eq x hm (rule r j) φ e (choices x hm r j φ c),
   bad_choices_eq x hm r j φ c]

end LeanCanny.Algebra.IntegralMixedSweepRetarget
