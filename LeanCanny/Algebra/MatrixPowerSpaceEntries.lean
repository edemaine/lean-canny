/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MatrixPowerPSPACE
public import LeanCanny.Algebra.MatrixPowerStepSpace
public import LeanCanny.Computation.SpaceFunctionComposition

/-! # Modular powering with native space-bounded entries

FP field writers and a tidy polynomial-space entry certificate give a composed
power-controller transition. Correctness and state-size invariants combine with
native iteration; no child execution clock or saved configuration is needed. -/

@[expose] public section

namespace LeanCanny.Algebra.MatrixPower.ModularAccess

open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets
open LeanCanny.Computation
open Controller

theorem callbacks_controls_polyTime {F : ModularFamily} (a : ModularAccess F) (ha : a.ControlsPolyTime) :
    (modularCallbacks a.dimension a.modulus a.entry).ControlsPolyTime := by
  have h := modularCallbacks_polyTime ha.dimension ha.modulus (constFn_mem_FP [])
  constructor
  · simpa only [modularCallbacks] using h.dimension
  · simpa only [modularCallbacks] using h.zero
  · simpa only [modularCallbacks] using h.one
  · simpa only [modularCallbacks] using h.combine

theorem evaluatorWithEntry {F : ModularFamily} (a : ModularAccess F)
    (ha : a.ControlsPolyTime) (E : SpaceFunction a.entry) : SpaceFunction F.value :=
  evaluatorWithStep a ha (stepEvaluator _ (callbacks_controls_polyTime a ha) E)

theorem zeroLanguage_mem_PSPACE_of_evaluator {F : ModularFamily} (a : ModularAccess F)
    (ha : a.ControlsPolyTime) (E : SpaceFunction a.entry) : F.zeroLanguage ∈ PSPACE := by
  let accept := fun bits : List Bool => decide (bits = [])
  have haccept : (fun bits => [accept bits]) ∈ FP :=
    (stringEq_fppred id_mem_FP (constFn_mem_FP [])).flag_mem_FP
  apply ((evaluatorWithEntry a ha E).decider accept haccept ?_).mem_PSPACE
  intro c
  let : NeZero (F.modulus c) := ⟨F.modulus_ne_zero c⟩
  have hz : residueBits (0 : ZMod (F.modulus c)) = [] := by simp [residueBits, BinaryNatCode.encode]
  change ((F.matrix c ^ F.exponent c) (F.row c) (F.col c) = 0) ↔ decide (F.value c = []) = true
  rw [decide_eq_true_eq, ModularFamily.value, ← hz, (residueBits_injective (F.modulus c)).eq_iff]

end LeanCanny.Algebra.MatrixPower.ModularAccess
