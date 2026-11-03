/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedJointCriticalSlab
public import LeanCanny.Geometry.IntegralMixedCriticalReadback
/-! # The actual decoded midpoint block recovers the same parent slice

The real critical point predicate is supplied by the full physical row
readback, not an annihilator root. Actual current-Q clearing cancels using
literal bank values; no equality of successive denominators is assumed.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} {F : Frame n}

theorem midpoint_critical_sound (x : State P S B (m+2) ι) (hm : m+2≤S)
    (HA : AtomicRows F m) (HP : PrefixFrozen F) (h g j : Fin (n+1))
    (hfirst : h.val=F.frozen.card) (hh : h∉F.frozen)
    (hg : g∉(line F h).frozen) (hj : j∉(line F h).frozen)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (values : Fin m→ℝ) (a b : ℝ)
    (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=
      (Fin.cons b (Fin.cons a values) : Fin (m+2)→ℝ) i)
    (point : Fin (n+1)→ℝ)
    (HC : IntegralMixedCriticalReadback.CriticalPoint x hm (midpointData HA h g j hg hj).rule φ point) :
    point∈slice P F values ∧ point h=(a+b)/2 :=by
  let M:=midpointFrame HA h
  let d:=midpointData HA h g j hg hj
  have HM:=HP.midpointFrame HA h hfirst hh
  have HR (i : Fin (n+1)) : d.rule.heights i=M.heights i:=by
    change (midpointRows HA h (FrozenCoordinateOrdering.permutation M.frozen i)).value=(midpointRows HA h i).value
    rw [HM.permutation]
    rfl
  have HS (i : Fin (n+1)) : d.rule.scales i=M.scales i:=by
    change (if midpointDouble h (FrozenCoordinateOrdering.permutation M.frozen i) then 2 else 1)=_
    rw [HM.permutation]
    rfl
  have HPt : point∈actualSlice x φ M:=by
    refine ⟨HC.1,?_⟩
    intro i hi
    have HH:=HC.2.1 i ((HM i).mp hi)
    change ((commonDenominator x*d.rule.scales i:ℤ):ℝ)*point i=φ (expression x (d.rule.heights i)) at HH
    rw [HS,HR] at HH
    exact HH
  rw [actualSlice_eq x φ M (Fin.cons b (Fin.cons a values)) H] at HPt
  exact (Set.ext_iff.mp (midpointFrame_slice HA h hh values a b) point).mp HPt

end LeanCanny.Geometry.IntegralMixedFrozenFrame
