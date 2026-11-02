/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedHistoryScript

/-! # Equality transport for actual framed execution

Only explicit equality of birth numbers, carrier types and actual states is
used. Reframing retains the same sampler and bank; no algebra isomorphism or
independent interpretation of a root is assumed.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedStateTransport
open IntegralMixedHistory

 theorem reframe_twice {n p q S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (Q : SpatialSource p) (hQ : PurePowerReductionBounds.dimension (p+1) Q.degree≤2^B)
    (R : SpatialSource q) (hR : PurePowerReductionBounds.dimension (q+1) R.degree≤2^B) :
    reframe (reframe x Q hQ) R hR=reframe x R hR := rfl

theorem step_reframe_heq {n p S B m m' : ℕ} {P : SpatialSource n} {ι κ : Type}
    [hι : Fintype ι] [hκ : Fintype κ]
    (x : State P S B m ι) (y : State P S B m' κ) (hm : m=m') (hindex : ι=κ) (hxy : HEq x y)
    (hx : m≤S) (hy : m'≤S) (c : IntegralMixedFullHistoryScript.Command P B)
    (Q : SpatialSource p) (hQ : PurePowerReductionBounds.dimension (p+1) Q.degree≤2^B) :
    HEq (reframe (IntegralMixedFullHistoryScript.step x hx c) Q hQ)
      (reframe (IntegralMixedFullHistoryScript.step y hy c) Q hQ) := by
  subst m'
  subst κ
  cases Subsingleton.elim hκ hι
  have H : x=y := eq_of_heq hxy
  subst y
  rfl

end LeanCanny.Algebra.IntegralMixedFramedStateTransport
