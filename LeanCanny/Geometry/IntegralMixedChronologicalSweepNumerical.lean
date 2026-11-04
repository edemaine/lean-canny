/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedChronologicalSweepFrame
public import LeanCanny.Algebra.IntegralMixedNumericalSweepCongruence
/-! # Literal numerical levels of a chronological ordinary sweep -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedChronologicalSweepFrame
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedFrozenFrame
open IntegralMixedChronologicalFrame Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n birth :ℕ}

/-- Old frozen rows are their retained values; the next row varies with X.
The actual current-Q denominator cancels without being assumed to equal one. -/
theorem data_normalized (d :Descriptor n birth) (hk :d.labels.length<n+1)
    (g j :Fin (n+1)) (hg :g∉(frame d hk).frozen) (hj :j∉(frame d hk).frozen)
    (Q :ℤ) (hQ :Q≠0) (values :Fin birth→ℝ) (i :Fin (n+1)):
    IntegralMixedNumericalSweep.normalized ((data d hk g j hg hj).rule Q hQ) values i.val=
      C ((d.atom i).value.evaluate values)+(if i.val=d.labels.length then X else 0):=by
  have HS :((data d hk g j hg hj).rule Q hQ).critical.scales i=1:=rfl
  have HH :((data d hk g j hg hj).rule Q hQ).critical.heights i=(d.atom i).value:=by
    change (d.atom (FrozenCoordinateOrdering.permutation (frame d hk).frozen i)).value=_
    rw [(prefix_frozen d hk).permutation]
    rfl
  rw [IntegralMixedNumericalSweep.normalized_at,HS,HH,data_height]
  simp only [Int.cast_one,div_one,inv_one,map_one,one_mul,next,Fin.ext_iff]

theorem data_normalized_height (d :Descriptor n birth) (hk :d.labels.length<n+1)
    (g j :Fin (n+1)) (hg :g∉(frame d hk).frozen) (hj :j∉(frame d hk).frozen)
    (Q :ℤ) (hQ :Q≠0) (values :Fin birth→ℝ):
    IntegralMixedNumericalSweep.normalized ((data d hk g j hg hj).rule Q hQ) values d.labels.length=X:=by
  have H:=data_normalized d hk g j hg hj Q hQ values (next d hk)
  simpa only [next,Descriptor.atom,dite_eq_right (Nat.lt_irrefl d.labels.length),
    IntegralMixedCausalRowConstructor.Atom.value,AffineExpr.evaluate,Int.cast_zero,map_zero,
    ite_true,zero_add] using H

end LeanCanny.Geometry.IntegralMixedChronologicalSweepFrame
