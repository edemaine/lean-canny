/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedScalarModel
public import LeanCanny.Algebra.IntegralMixedEntryDispatcher

/-! # Framed routine-two entries use current scalar and critical replies

The existing generic entry controller applies to the actual changing-source
family. Its external replies follow from the literal current scalar model
and framed critical controller, without an interpreted entry-cost premise.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedEntryBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical

noncomputable abbrev family := IntegralMixedFramedHistoryFamilyBits.family
abbrev Controls := IntegralMixedFramedCriticalBits.Controls
noncomputable abbrev input := IntegralMixedFramedCriticalBits.virtualInput

noncomputable abbrev machine (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) :=
  IntegralMixedEntryDispatcherBits.machine P a (family P D H) (input P a D H h)
abbrev Matches (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) :=
  IntegralMixedEntryDispatcherBits.Matches P a (family P D H) (input P a D H h)

theorem critical_at (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H)
    (answer : List Bool → List Bool) (hc : IntegralMixedFramedCriticalBits.Matches P a D H h answer)
    (p : Phase) (q : List Bool) (hp : p.code ≤ 25) (hv : IntegralMixedVirtualCaps.valid P q)
    (hr : IntegralMixedRoutineTaskBits.routine P q = 1) (hq : isPhase p q)
    (hx : IntegralMixedVirtualContextBits.context P q) :
    answer q = IntegralMixedVirtualContextComponentBits.component P (family P D H) p q :=
  IntegralMixedFramedCriticalBits.virtual_matches P a D H h answer hc p q hp
    (decide_eq_true ⟨hv, hr, hq, hx⟩)

theorem external (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H)
    (answer : List Bool → List Bool) (hc : IntegralMixedFramedCriticalBits.Matches P a D H h answer)
    (hs : IntegralMixedFramedScalarModelBits.Matches P D H answer) :
    IntegralMixedValueRowScopedBits.External P (family P D H) answer := by
  constructor
  · intro q hv hr hp hx
    exact critical_at P a D H h answer hc .frozenLower q (by decide) hv hr hp hx
  · intro q hv hr hp hx
    exact critical_at P a D H h answer hc .clearedGridSum q (by decide) hv hr hp hx
  · intro q hv hr hp hx
    exact critical_at P a D H h answer hc .criticalCoefficient q (by decide) hv hr hp hx
  · intro q hv hr hp hx
    have HX : 1 ≤ get P .slot15 q ∧ get P .slot15 q ≤ 4 := by
      unfold IntegralMixedVirtualContextBits.context at hx
      omega
    have HN : get P .slot15 q ≠ 1 := by
      unfold IntegralMixedVirtualContextBits.context at hx
      omega
    have HE := hs .productEntry q (Or.inr rfl) hv hr HX hp
    exact HE.trans (by
      simp only [IntegralMixedFramedScalarModelBits.component, ite_true, ite_eq_right HN]
      rfl)
  · intro q hv hr hp hx
    have HE := IntegralMixedFramedScalarModelBits.virtual_matches P D H answer hs
      .monomialFactor q (Or.inr (Or.inr (Or.inl rfl))) hv hr hx hp
    exact HE

theorem correct (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H)
    (answer : List Bool → List Bool) (hc : IntegralMixedFramedCriticalBits.Matches P a D H h answer)
    (hs : IntegralMixedFramedScalarModelBits.Matches P D H answer) (hm : Matches P a D H h answer) :
    Correct (machine P a D H h) answer (IntegralMixedRoutineTaskBits.Frame P) :=
  IntegralMixedEntryDispatcherBits.correct P a (family P D H) (input P a D H h)
    (IntegralMixedFramedHistoryFamilyBits.geometry P D H) answer hm
    (external P a D H h answer hc hs)
    (IntegralMixedFramedCriticalBits.virtual_matches P a D H h answer hc)

theorem selected (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (q : List Bool) :
    (machine P a D H h).selected q = true :=
  IntegralMixedEntryDispatcherBits.selected P a (family P D H) (input P a D H h) q

theorem canonical (P : Parameters) (a : Access P) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = (machine P a D H h).model q :=
  IntegralMixedEntryDispatcherBits.canonical P a (family P D H) (input P a D H h) q

end LeanCanny.Algebra.IntegralMixedFramedEntryBits
