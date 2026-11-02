/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedEntryDispatcher
public import LeanCanny.Algebra.IntegralMixedFullCoreCurrent
/-! # Routine-two external replies come from the actual scalar/critical core -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullEntryBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable abbrev family (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) := IntegralMixedFullHistoryFamilyBits.family P D

theorem virtual_matches (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : IntegralMixedFullCoreBits.Controls P D) (answer : List Bool → List Bool) (hm : IntegralMixedFullCoreBits.Matches P a D h answer) :
    IntegralMixedVirtualContextComponentBits.Matches P (family P D) answer :=
  IntegralMixedFullCriticalDispatcherBits.virtual_matches P a D h.algebra.critical answer
    (IntegralMixedFullAlgebraSpaceBits.critical_matches P a D h.algebra answer
      (IntegralMixedFullCoreBits.algebra_matches P a D h answer hm))

theorem critical_at (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : IntegralMixedFullCoreBits.Controls P D) (answer : List Bool → List Bool) (hm : IntegralMixedFullCoreBits.Matches P a D h answer)
    (p : Phase) (q : List Bool) (hp : p.code ≤ 25) (hv : IntegralMixedVirtualCaps.valid P q)
    (hr : IntegralMixedRoutineTaskBits.routine P q = 1) (hq : isPhase p q) (hx : IntegralMixedVirtualContextBits.context P q) :
    answer q = IntegralMixedVirtualContextComponentBits.component P (family P D) p q :=
  virtual_matches P a D h answer hm p q hp (decide_eq_true ⟨hv, hr, hq, hx⟩)

theorem external (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : IntegralMixedFullCoreBits.Controls P D) (answer : List Bool → List Bool) (hm : IntegralMixedFullCoreBits.Matches P a D h answer) :
    IntegralMixedValueRowScopedBits.External P (family P D) answer := by
  constructor
  · intro q hv hr hp hx
    exact critical_at P a D h answer hm .frozenLower q (by decide) hv hr hp hx
  · intro q hv hr hp hx
    exact critical_at P a D h answer hm .clearedGridSum q (by decide) hv hr hp hx
  · intro q hv hr hp hx
    exact critical_at P a D h answer hm .criticalCoefficient q (by decide) hv hr hp hx
  · intro q hv hr hp hx
    have HX : 1 ≤ get P .slot15 q ∧ get P .slot15 q ≤ 4 := ⟨by have := hx.1; omega, hx.2⟩
    have HS := (IntegralMixedFullScalarBits.selected_iff P .productEntry q).mpr ⟨hv, hr, hp, HX⟩
    have HE := IntegralMixedFullCoreBits.scalar_matches P a D h answer hm q hv hr HX (by omega)
    exact HE.trans ((IntegralMixedFullScalarBits.model5 P a D h.scalar q HS).trans
      (IntegralMixedFullScalarBits.scalar_virtual P a D h.scalar .originalScale q hx))
  · intro q hv hr hp hx
    have HX : 1 ≤ get P .slot15 q ∧ get P .slot15 q ≤ 4 := ⟨by have := hx.1; omega, hx.2⟩
    have HS := (IntegralMixedFullScalarBits.selected_iff P .monomialFactor q).mpr ⟨hv, hr, hp, HX⟩
    have HE := IntegralMixedFullCoreBits.scalar_matches P a D h answer hm q hv hr HX (by omega)
    exact HE.trans ((IntegralMixedFullScalarBits.model3 P a D h.scalar q HS).trans
      (IntegralMixedFullScalarBits.scalar_virtual P a D h.scalar .commonLeading q hx))

noncomputable abbrev input (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : IntegralMixedFullCoreBits.Controls P D) := IntegralMixedFullHistoryFamilyBits.inputMetadata P a D h.scalar.full
noncomputable abbrev machine (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : IntegralMixedFullCoreBits.Controls P D) := IntegralMixedEntryDispatcherBits.machine P a (family P D) (input P a D h)
abbrev Matches (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : IntegralMixedFullCoreBits.Controls P D) := IntegralMixedEntryDispatcherBits.Matches P a (family P D) (input P a D h)

theorem correct (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : IntegralMixedFullCoreBits.Controls P D) (answer : List Bool → List Bool)
    (hc : IntegralMixedFullCoreBits.Matches P a D h answer) (hm : Matches P a D h answer) :
    Correct (machine P a D h) answer (IntegralMixedRoutineTaskBits.Frame P) :=
  IntegralMixedEntryDispatcherBits.correct P a (family P D) (input P a D h) (IntegralMixedFullHistoryFamilyBits.geometry P D)
    answer hm (external P a D h answer hc) (virtual_matches P a D h answer hc)

theorem canonical (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : IntegralMixedFullCoreBits.Controls P D) (q : List Bool) : ∃ z : ZMod (modulus P q), residueBits z = (machine P a D h).model q :=
  IntegralMixedEntryDispatcherBits.canonical P a (family P D) (input P a D h) q
end LeanCanny.Algebra.IntegralMixedFullEntryBits
