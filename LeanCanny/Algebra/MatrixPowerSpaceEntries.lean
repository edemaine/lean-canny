/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MatrixPowerPSPACE
public import LeanCanny.Algebra.MatrixPowerSubroutine
public import LeanCanny.Computation.SubroutineFunction
public import LeanCanny.Computation.SpaceFunctionComposition

/-!
# Modular powering with space-bounded matrix entry evaluation

Only field writers and scalar control arithmetic require FP certificates.
Entry calls run through a certified output routine while the parent controller
is retained. The complete physical state and expanded clock satisfy the output
certificate, so the whole entry computation need not be FP.
-/

@[expose] public section

namespace LeanCanny.Algebra.MatrixPower.ModularAccess
open Complexity
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

noncomputable def evaluatorWithEntry {F : ModularFamily} (a : ModularAccess F)
    (ha : a.ControlsPolyTime) (E : SpaceFunction a.entry) : SpaceFunction F.value := by
  let ops := modularCallbacks a.dimension a.modulus a.entry
  let P := entryProgram ops E.init E.advance E.halt E.output
  let T := fun p => E.time (entryInput p)
  let N := fun c => work (F.dimension c) (F.exponent c).size (F.exponent c) + 1
  let init := initialPacket a.exponent a.row a.col
  let f := SubroutineIteration.abstractStep P T
  have hP : P.PolyTime := entryProgram_polyTime ops (callbacks_controls_polyTime a ha)
    E.initFP E.advanceFP E.haltFP E.outputFP
  have hiter (c : List Bool) (j : ℕ) : f^[j] (init c) = (Controller.step ops)^[j] (init c) :=
    entryProgram_iterate ops E.init E.advance E.halt E.output T (init c) j
      (fun k _ _ => E.correct (entryInput ((Controller.step ops)^[k] (init c))))
  have hc (c : List Bool) : CorrectAt ops c (F.matrix c) residueBits := by
    let : NeZero (F.modulus c) := ⟨F.modulus_ne_zero c⟩
    exact modularCallbacks_correctAt a.dimension a.modulus a.entry c (F.modulus c) (F.matrix c)
      (a.dimension_eq c) (a.modulus_eq c) (a.entry_eq c)
  have hinit (c : List Bool) : init c = pair c (stateBits (residueBits (m := F.modulus c))
      (.eval ⟨(F.exponent c).size, F.exponent c, F.row c, F.col c⟩ [])) :=
    initialPacket_encode a.exponent a.row a.col c (residueBits (m := F.modulus c)) (F.exponent c)
      (F.row c) (F.col c) (a.exponent_eq c) (a.row_eq c) (a.col_eq c)
  let pd := Classical.choose (Cobham.output_length_poly_of_mem_FP ha.dimension)
  have hd : ∀ c, (a.dimension c).length ≤ pd.eval c.length :=
    Classical.choose_spec (Cobham.output_length_poly_of_mem_FP ha.dimension)
  let pm := Classical.choose (Cobham.output_length_poly_of_mem_FP ha.modulus)
  have hm : ∀ c, (a.modulus c).length ≤ pm.eval c.length :=
    Classical.choose_spec (Cobham.output_length_poly_of_mem_FP ha.modulus)
  let pe := Classical.choose (Cobham.output_length_poly_of_mem_FP ha.exponent)
  have he : ∀ c, (a.exponent c).length ≤ pe.eval c.length :=
    Classical.choose_spec (Cobham.output_length_poly_of_mem_FP ha.exponent)
  let pq := Classical.choose (Cobham.output_length_poly_of_mem_FP entryInput_mem_FP)
  have hq : ∀ p, (entryInput p).length ≤ pq.eval p.length :=
    Classical.choose_spec (Cobham.output_length_poly_of_mem_FP entryInput_mem_FP)
  let p := pd + pe + pm
  let r := 2 * Polynomial.X + 2 + 64 * (p + 1) ^ 2
  let q := pq.comp r
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
  have hquery (c : List Bool) (j : ℕ) : (entryInput (f^[j] (init c))).length ≤ q.eval c.length := by
    simpa only [q, Polynomial.eval_comp] using
      (hq (f^[j] (init c))).trans (polynomial_eval_mono_nat pq (hp c j))
  have R := SubroutineIteration.evaluator P hP init
    (initialPacket_mem_FP ha.exponent ha.row ha.col) halted valueBits halted_mem_FP valueBits_mem_FP
    T N r (E.space.comp q) ((p + 2) * p + 1) (E.clock.comp q)
    (by intro c j _ _; exact ⟨E.before (entryInput (f^[j] (init c))), E.after (entryInput (f^[j] (init c)))⟩)
    (by intro c j _; exact hp c j)
    (by
      intro c j _ _ t ht
      have hl := E.length_le (entryInput (f^[j] (init c))) t ht
      have hb := polynomial_eval_mono_nat E.space (hquery c j)
      simpa only [P, entryProgram, f, Polynomial.eval_comp] using hl.trans hb)
    (by
      intro c
      have hb := hbits c
      have hw := work_add_one_le_two_pow (F.dimension c) (F.exponent c).size (F.exponent c)
      have hm : ((F.dimension c).size + 2) * (F.exponent c).size ≤
          (p.eval c.length + 2) * p.eval c.length := Nat.mul_le_mul (by omega) (by omega)
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_one]
      exact hw.trans (Nat.pow_le_pow_right (by decide) (Nat.add_le_add_right hm 1)))
    (by
      intro c j _ _
      have ht := E.time_le (entryInput (f^[j] (init c)))
      have hb := polynomial_eval_mono_nat E.clock (hquery c j)
      simpa only [T, f, Polynomial.eval_comp] using ht.trans (Nat.pow_le_pow_right (by decide) hb))
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
