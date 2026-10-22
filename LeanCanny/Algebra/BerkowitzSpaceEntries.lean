/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BerkowitzFactorSpace

/-!
# Modular determinant zero testing with space-bounded original entries

The outer layered power calls the certified factor evaluator, whose moment
child calls the original entry evaluator. FP field writers and a complete
`SpaceFunction` entry certificate suffice; no whole entry call is assumed FP.
-/

@[expose] public section

namespace LeanCanny.Algebra.Berkowitz.ModularAccess

open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets
open LeanCanny.Computation
open MatrixPower

def powerFamily (F : ModularFamily) : MatrixPower.ModularFamily where
  dimension := fun c => (F.dimension c + 1) * (F.dimension c + 1)
  modulus := F.modulus
  exponent := F.dimension
  row := fun c => (powerQuery (F.dimension c) 0).row
  col := fun c => (powerQuery (F.dimension c) 0).col
  matrix := fun c => powerMatrix (F.matrix c)
  modulus_ne_zero := F.modulus_ne_zero

noncomputable def powerAccess {F : ModularFamily} (a : ModularAccess F) : MatrixPower.ModularAccess (powerFamily F) where
  dimension := PowerAccessBits.dimension a.access
  modulus := a.access.modulus
  exponent := a.access.dimension
  row := fun _ => []
  col := PowerAccessBits.target a.access
  entry := factorValue a
  dimension_eq := fun c => PowerAccessBits.dimension_code a.access c (F.dimension c) (a.correct c).dimension
  modulus_eq := fun c => (a.correct c).modulus
  exponent_eq := fun c => (a.correct c).dimension
  row_eq := fun c => by simp [powerFamily, powerQuery, finProdFinEquiv, BinaryNatCode.encode]
  col_eq := fun c => by
    simpa [powerFamily, powerQuery, finProdFinEquiv, Nat.mul_comm] using
      PowerAccessBits.target_code a.access c (F.dimension c) (a.correct c).dimension
  entry_eq := factorValue_packet a

theorem powerControls {F : ModularFamily} (a : ModularAccess F) (ha : a.ControlsPolyTime) :
    a.powerAccess.ControlsPolyTime := by
  have hw := mem_FP_comp ha.dimension BinaryNat.succ_mem_FP
  have hd0 := mem_FP_comp (mem_FP_pair hw hw) BinaryNat.mul_mem_FP
  have hc0 := mem_FP_comp (mem_FP_pair ha.dimension hw) BinaryNat.mul_mem_FP
  have hd : PowerAccessBits.dimension a.access ∈ FP := by
    refine mem_FP_of_eq (g := PowerAccessBits.dimension a.access) hd0 ?_
    intro c
    simp only [Function.comp_apply, PowerAccessBits.dimension]
  have hc : PowerAccessBits.target a.access ∈ FP := by
    refine mem_FP_of_eq (g := PowerAccessBits.target a.access) hc0 ?_
    intro c
    simp only [Function.comp_apply, PowerAccessBits.target]
  constructor
  · simpa only [powerAccess] using hd
  · simpa only [powerAccess] using ha.modulus
  · simpa only [powerAccess] using ha.dimension
  · exact constFn_mem_FP []
  · simpa only [powerAccess] using hc

theorem powerEvaluator {F : ModularFamily} (a : ModularAccess F) (ha : a.ControlsPolyTime)
    (E : SpaceFunction a.access.entry) : SpaceFunction (powerFamily F).value :=
  MatrixPower.ModularAccess.evaluatorWithEntry a.powerAccess (powerControls a ha) (factorEvaluator a ha E)

theorem deciderWithEntry {F : ModularFamily} (a : ModularAccess F) (ha : a.ControlsPolyTime)
    (E : SpaceFunction a.access.entry) : SpaceDecider F.zeroLanguage := by
  let accept := fun bits : List Bool => decide (bits = [])
  have haccept : (fun bits => [accept bits]) ∈ FP :=
    (stringEq_fppred id_mem_FP (constFn_mem_FP [])).flag_mem_FP
  refine (powerEvaluator a ha E).decider accept haccept ?_
  intro c
  let : NeZero (F.modulus c) := ⟨F.modulus_ne_zero c⟩
  have hz : residueBits (0 : ZMod (F.modulus c)) = [] := by simp [residueBits, BinaryNatCode.encode]
  change (F.matrix c).det = 0 ↔ decide ((powerFamily F).value c = []) = true
  rw [decide_eq_true_eq]
  change (F.matrix c).det = 0 ↔
    residueBits ((powerMatrix (F.matrix c) ^ F.dimension c)
      (powerQuery (F.dimension c) 0).row (powerQuery (F.dimension c) 0).col) = []
  rw [← hz, (residueBits_injective (F.modulus c)).eq_iff]
  exact (powerMatrix_zero_iff (F.matrix c)).symm

theorem zeroLanguage_mem_PSPACE_of_evaluator {F : ModularFamily} (a : ModularAccess F)
    (ha : a.ControlsPolyTime) (E : SpaceFunction a.access.entry) : F.zeroLanguage ∈ PSPACE :=
  (deciderWithEntry a ha E).mem_PSPACE

theorem decider {F : ModularFamily} (a : ModularAccess F)
    (ha : a.access.PolyTime) : SpaceDecider F.zeroLanguage :=
  deciderWithEntry a ⟨ha.dimension, ha.modulus⟩ (SpaceFunction.ofFP a.access.entry ha.entry)

theorem zeroLanguage_mem_PSPACE {F : ModularFamily} (a : ModularAccess F)
    (ha : a.access.PolyTime) : F.zeroLanguage ∈ PSPACE :=
  (decider a ha).mem_PSPACE

end LeanCanny.Algebra.Berkowitz.ModularAccess
