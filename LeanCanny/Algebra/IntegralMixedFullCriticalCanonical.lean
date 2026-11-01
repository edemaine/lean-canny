/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullCriticalCurrent
public import LeanCanny.Algebra.IntegralMixedPhaseDecode
public import LeanCanny.Algebra.IntegralMixedCriticalPhaseBoundary
/-! # One canonical residue model for physical and virtual critical arithmetic -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullCriticalDispatcherBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem physical_canonical (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) (hr : IntegralMixedRoutineTaskBits.routine P q = 1)
    (hx : get P .slot15 q = 1) : ∃ z : ZMod (modulus P q), residueBits z = (physicalMachine P a D h).model q := by
  unfold physicalMachine
  by_cases hp : phase q = 26
  · rw [IntegralMixedCriticalPhaseBoundary.physical P a _ h.physical h.physicalOriginal q hp]
    exact ⟨0, (ArithmeticBits.zero_residueBits _).symm⟩
  · have he := IntegralMixedPhaseDecode.code (phase q) (IntegralMixedRoutineTaskBits.phase_lt q)
    have hb : (IntegralMixedPhaseDecode.decode (phase q)).code ≤ 25 := by
      have ht := IntegralMixedRoutineTaskBits.phase_lt q
      omega
    rw [IntegralMixedPhysicalDispatcherBits.model_phase P a _ h.physical h.physicalOriginal
      (IntegralMixedPhaseDecode.decode (phase q)) q hb hv hr hx (IntegralMixedPhaseDecode.task q)]
    exact IntegralMixedPhysicalComponentBits.component_canonical P _ _ q

theorem virtual_canonical (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) (hr : IntegralMixedRoutineTaskBits.routine P q = 1)
    (hx : IntegralMixedVirtualContextBits.context P q) : ∃ z : ZMod (modulus P q), residueBits z = (virtualMachine P a D h).model q := by
  unfold virtualMachine
  by_cases hp : phase q = 26
  · rw [IntegralMixedCriticalPhaseBoundary.virtual P a _ _ h.virtualOriginal q hp]
    exact ⟨0, (ArithmeticBits.zero_residueBits _).symm⟩
  · have he := IntegralMixedPhaseDecode.code (phase q) (IntegralMixedRoutineTaskBits.phase_lt q)
    have hb : (IntegralMixedPhaseDecode.decode (phase q)).code ≤ 25 := by
      have ht := IntegralMixedRoutineTaskBits.phase_lt q
      omega
    rw [IntegralMixedVirtualContextDispatcherBits.model_phase P a _
      (IntegralMixedFullHistoryFamilyBits.inputMetadata P a D h.full) h.virtualOriginal
      (IntegralMixedPhaseDecode.decode (phase q)) q hb hv hr hx (IntegralMixedPhaseDecode.task q)]
    exact IntegralMixedVirtualContextComponentBits.component_canonical P _ _ q

attribute [local irreducible] physicalMachine virtualMachine

theorem canonical (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (q : List Bool) : ∃ z : ZMod (modulus P q), residueBits z = (machine P a D h).model q := by
  change ∃ z : ZMod (modulus P q), residueBits z =
    if decide (IntegralMixedRoutineContextGuard.Selected P 1 1 1 q) then (physicalMachine P a D h).model q else
      if decide (IntegralMixedRoutineContextGuard.Selected P 1 2 4 q) then (virtualMachine P a D h).model q else []
  split_ifs with hp hv
  · have ht : IntegralMixedRoutineContextGuard.Selected P 1 1 1 q := of_decide_eq_true hp
    exact physical_canonical P a D h q ht.1 ht.2.1 (by have := ht.2.2; omega)
  · have ht : IntegralMixedRoutineContextGuard.Selected P 1 2 4 q := of_decide_eq_true hv
    exact virtual_canonical P a D h q ht.1 ht.2.1 ht.2.2
  · exact ⟨0, (ArithmeticBits.zero_residueBits _).symm⟩

end LeanCanny.Algebra.IntegralMixedFullCriticalDispatcherBits
