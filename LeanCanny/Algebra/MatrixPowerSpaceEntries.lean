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

structure ControlsPolyTime {F : ModularFamily} (a : ModularAccess F) : Prop where
  dimension : a.dimension ∈ FP
  modulus : a.modulus ∈ FP
  exponent : a.exponent ∈ FP
  row : a.row ∈ FP
  col : a.col ∈ FP

theorem controlsPolyTime_of_polyTime {F : ModularFamily} (a : ModularAccess F) (ha : a.PolyTime) :
    a.ControlsPolyTime := ⟨ha.dimension, ha.modulus, ha.exponent, ha.row, ha.col⟩

theorem callbacks_controls_polyTime {F : ModularFamily} (a : ModularAccess F) (ha : a.ControlsPolyTime) :
    (modularCallbacks a.dimension a.modulus a.entry).ControlsPolyTime := by
  have h := modularCallbacks_polyTime ha.dimension ha.modulus (constFn_mem_FP [])
  constructor
  · simpa only [modularCallbacks] using h.dimension
  · simpa only [modularCallbacks] using h.zero
  · simpa only [modularCallbacks] using h.one
  · simpa only [modularCallbacks] using h.combine

theorem evaluatorWithEntry {F : ModularFamily} (a : ModularAccess F)
    (ha : a.ControlsPolyTime) (E : SpaceFunction a.entry) : SpaceFunction F.value := by
  let ops := modularCallbacks a.dimension a.modulus a.entry
  let N := fun c => work (F.dimension c) (F.exponent c).size (F.exponent c) + 1
  let init := initialPacket a.exponent a.row a.col
  let f := Controller.step ops
  have hiter (c : List Bool) (j : ℕ) :
      f^[j] (init c) = (Controller.step ops)^[j] (init c) := rfl
  have hc (c : List Bool) : CorrectAt ops c (F.matrix c) residueBits := by
    let : NeZero (F.modulus c) := ⟨F.modulus_ne_zero c⟩
    exact modularCallbacks_correctAt a.dimension a.modulus a.entry c (F.modulus c) (F.matrix c)
      (a.dimension_eq c) (a.modulus_eq c) (a.entry_eq c)
  have hinit (c : List Bool) : init c = pair c (stateBits (residueBits (m := F.modulus c))
      (.eval ⟨(F.exponent c).size, F.exponent c, F.row c, F.col c⟩ [])) :=
    initialPacket_encode a.exponent a.row a.col c (residueBits (m := F.modulus c)) (F.exponent c)
      (F.row c) (F.col c) (a.exponent_eq c) (a.row_eq c) (a.col_eq c)
  let pd := Classical.choose (output_length_poly_of_mem_FP ha.dimension)
  have hd : ∀ c, (a.dimension c).length ≤ pd.eval c.length :=
    Classical.choose_spec (output_length_poly_of_mem_FP ha.dimension)
  let pm := Classical.choose (output_length_poly_of_mem_FP ha.modulus)
  have hm : ∀ c, (a.modulus c).length ≤ pm.eval c.length :=
    Classical.choose_spec (output_length_poly_of_mem_FP ha.modulus)
  let pe := Classical.choose (output_length_poly_of_mem_FP ha.exponent)
  have he : ∀ c, (a.exponent c).length ≤ pe.eval c.length :=
    Classical.choose_spec (output_length_poly_of_mem_FP ha.exponent)
  let p := pd + pe + pm
  let r := 2 * Polynomial.X + 2 + 64 * (p + 1) ^ 2
  have hbits (c : List Bool) :
      (F.dimension c).size + (F.exponent c).size + (F.modulus c).size ≤ p.eval c.length := by
    have hdc := hd c
    have hmc := hm c
    have hec := he c
    rw [a.dimension_eq, BinaryNatCode.length_encode] at hdc
    rw [a.modulus_eq, BinaryNatCode.length_encode] at hmc
    rw [a.exponent_eq, BinaryNatCode.length_encode] at hec
    simp only [p, Polynomial.eval_add]
    omega
  have hp (c : List Bool) (j : ℕ) : (f^[j] (init c)).length ≤ r.eval c.length := by
    let : NeZero (F.modulus c) := ⟨F.modulus_ne_zero c⟩
    rw [hiter, hinit]
    have hl := modular_run_length_le a.dimension a.modulus a.entry c (F.modulus c)
      (F.matrix c) (hc c) (F.exponent c) j (F.row c) (F.col c)
    have hpow := Nat.pow_le_pow_left (Nat.add_le_add_right (hbits c) 1) 2
    simp only [r, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_one]
    exact hl.trans (Nat.add_le_add_left (Nat.mul_le_mul_left 64 hpow) _)
  have R := SpaceFunction.orbit
    (stepEvaluator ops (callbacks_controls_polyTime a ha) E) init
    (initialPacket_mem_FP ha.exponent ha.row ha.col) halted valueBits halted_mem_FP valueBits_mem_FP
    N r ((p + 2) * p + 1) (by intro c j _; exact hp c j)
    (by
      intro c
      have hb := hbits c
      have hw := work_add_one_le_two_pow (F.dimension c) (F.exponent c).size (F.exponent c)
      have hm : ((F.dimension c).size + 2) * (F.exponent c).size ≤
          (p.eval c.length + 2) * p.eval c.length := Nat.mul_le_mul (by omega) (by omega)
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one]
      exact hw.trans (Nat.pow_le_pow_right (by decide) (Nat.add_le_add_right hm 1)))
    (by
      intro c j hj
      rw [hiter, hinit]
      exact halted_before ops c (F.matrix c) residueBits (hc c) (F.exponent c) j (F.row c) (F.col c) hj)
    (by
      intro c
      rw [hiter, hinit]
      exact halted_after ops c (F.matrix c) residueBits (hc c) (F.exponent c) (F.row c) (F.col c))
  refine R.congr ?_
  funext c
  rw [hiter, hinit, Controller.run_pow ops c (F.matrix c) residueBits (hc c), valueBits_done]
  rfl

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
