/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedChronologicalMidpointActual
public import LeanCanny.Geometry.IntegralMixedChronologicalSweepFrame
public import LeanCanny.Algebra.IntegralMixedMeanCenteredSweep
/-! # The literal chronological midpoint frame as a current-Q cut source -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedChronologicalMeanCut
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedCriticalSweep
open IntegralMixedFrozenFrame IntegralMixedCausalRowConstructor
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n birth : ℕ}

noncomputable def data (d : IntegralMixedChronologicalFrame.Descriptor n birth)
    (hk : d.labels.length<n+1) (a b : Fin birth) (g j : Fin (n+1))
    (hg : g∉(IntegralMixedChronologicalMidpoint.frame d hk a b).frozen)
    (hj : j∉(IntegralMixedChronologicalMidpoint.frame d hk a b).frozen) :
    IntegralMixedCutRecordConstructor.Data n birth where
  critical:=IntegralMixedChronologicalMidpointCode.data d hk a b g j hg hj
  positive:=by
    change 0<(IntegralMixedChronologicalMidpoint.frame d hk a b).frozen.card
    rw [IntegralMixedChronologicalMidpoint.frozen_card]
    omega
  height:=⟨d.labels.length,by
    change d.labels.length<(IntegralMixedChronologicalMidpoint.frame d hk a b).frozen.card
    rw [IntegralMixedChronologicalMidpoint.frozen_card]
    omega⟩
  current:=true

theorem data_offset (d : IntegralMixedChronologicalFrame.Descriptor n birth)
    (hk : d.labels.length<n+1) (a b : Fin birth) (g j : Fin (n+1))
    (hg : g∉(IntegralMixedChronologicalMidpoint.frame d hk a b).frozen)
    (hj : j∉(IntegralMixedChronologicalMidpoint.frame d hk a b).frozen) :
    (data d hk a b g j hg hj).critical.offset.val=d.labels.length+1:=
  IntegralMixedChronologicalMidpoint.frozen_card d hk a b

private theorem critical_ext (r s : CriticalRule n) (ho : r.offset=s.offset)
    (hg : r.objective=s.objective) (hj : r.coordinate=s.coordinate)
    (hs : ∀i,r.scales i=s.scales i) (hh : ∀i,r.heights i=s.heights i) : r=s:=by
  cases r
  cases s
  cases ho
  cases hg
  cases hj
  have HS:=funext hs
  cases HS
  have HH:=funext hh
  cases HH
  rfl

private theorem rule_ext (r s : Rule n) (hc : r.critical=s.critical)
    (hh : r.height=s.height) (hs : r.slope=s.slope) : r=s:=by
  cases r
  cases s
  cases hc
  cases hh
  cases hs
  rfl

theorem data_rule (d : IntegralMixedChronologicalFrame.Descriptor n birth)
    (hk : d.labels.length<n+1) (a b : Fin birth) (g j : Fin (n+1))
    (hg : g∉(IntegralMixedChronologicalMidpoint.frame d hk a b).frozen)
    (hj : j∉(IntegralMixedChronologicalMidpoint.frame d hk a b).frozen)
    (Q : ℤ) (hQ : Q≠0) :
    (data d hk a b g j hg hj).rule Q hQ=
      IntegralMixedMeanCenteredSweep.rule
        ((IntegralMixedChronologicalSweepFrame.data d hk g j hg hj).rule Q hQ)
        (IntegralMixedChronologicalMidpoint.reference a) (IntegralMixedChronologicalMidpoint.reference b):=by
  apply rule_ext
  · apply critical_ext
    · rfl
    · rfl
    · rfl
    · intro i
      change (if midpointDouble (IntegralMixedChronologicalMidpoint.next d hk)
          (FrozenCoordinateOrdering.permutation (IntegralMixedChronologicalMidpoint.frame d hk a b).frozen i) then 2 else 1)=
        if i=IntegralMixedChronologicalMidpoint.next d hk then 2 else 1
      simp only [(IntegralMixedChronologicalMidpoint.prefix_frozen d hk a b).permutation,
        Equiv.refl_apply,midpointDouble,decide_eq_true_eq]
    · intro i
      change (IntegralMixedChronologicalMidpoint.rows d hk a b
          (FrozenCoordinateOrdering.permutation (IntegralMixedChronologicalMidpoint.frame d hk a b).frozen i)).value=
        if i=IntegralMixedChronologicalMidpoint.next d hk then
          .add (.reference (IntegralMixedChronologicalMidpoint.reference a).val)
            (.reference (IntegralMixedChronologicalMidpoint.reference b).val)
        else (d.atom (FrozenCoordinateOrdering.permutation (IntegralMixedChronologicalMidpoint.frame d hk a b).frozen i)).value
      simp only [(IntegralMixedChronologicalMidpoint.prefix_frozen d hk a b).permutation,Equiv.refl_apply,
        IntegralMixedChronologicalMidpoint.rows]
      split_ifs <;> rfl
  · rfl
  · rfl

end LeanCanny.Geometry.IntegralMixedChronologicalMeanCut
