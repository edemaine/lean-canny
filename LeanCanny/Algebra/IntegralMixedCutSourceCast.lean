/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedRelativeCutSpecialized
public import LeanCanny.Algebra.IntegralMixedSourceReframe
/-! # Exact cut transport when a source reframe is proved to be the same source -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCutSourceCast
open IntegralMixedHistory IntegralMixedCriticalSweep IntegralMixedRelativeCuts
variable {n S B m : ℕ} {P Q : SpatialSource n} {ι : Type}
set_option backward.isDefEq.respectTransparency false

def kind (hQ : Q=P) (r : Rule n) (c : Kind Q r) : Kind P r:=hQ ▸ c

theorem factor (x : State P S B m ι) (hm : m≤S)
    (hc : PurePowerReductionBounds.dimension (n+1) Q.degree≤2^B)
    (hQ : Q=P) (r : Rule n) (c : Kind Q r) :
    IntegralMixedRelativeCuts.factor (reframe x Q hc) hm r c=
      IntegralMixedRelativeCuts.factor x hm r (kind hQ r c) :=by
  subst Q
  cases x
  rfl

theorem valid_iff (x : State P S B m ι) (hm : m≤S)
    (hc : PurePowerReductionBounds.dimension (n+1) Q.degree≤2^B)
    (hQ : Q=P) (r : Rule n) (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (c : Kind Q r) :
    IntegralMixedRelativeCuts.Valid (reframe x Q hc) hm r φ c ↔
      IntegralMixedRelativeCuts.Valid x hm r φ (kind hQ r c) :=by
  subst Q
  cases x
  rfl

theorem selectedDegree (x : State P S B m ι) (hm : m≤S)
    (hc : PurePowerReductionBounds.dimension (n+1) Q.degree≤2^B)
    (hQ : Q=P) (r : Rule n) (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (c : Kind Q r) :
    IntegralMixedRelativeCuts.selectedDegree (reframe x Q hc) hm r φ c=
      IntegralMixedRelativeCuts.selectedDegree x hm r φ (kind hQ r c) :=by
  rw [IntegralMixedRelativeCuts.selectedDegree,factor]
  rfl

noncomputable def choices (x : State P S B m ι) (hm : m≤S)
    (hc : PurePowerReductionBounds.dimension (n+1) Q.degree≤2^B)
    (hQ : Q=P) (r : Rule n) (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (old : Choices (reframe x Q hc) hm r φ) : Choices x hm r φ :=by
  subst Q
  cases x
  exact old

end LeanCanny.Algebra.IntegralMixedCutSourceCast
