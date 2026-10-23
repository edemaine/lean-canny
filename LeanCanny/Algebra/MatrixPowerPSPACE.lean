/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MatrixPowerHalting
public import LeanCanny.Computation.SpaceIteration

/-!
# Polynomial-space modular matrix powering

A context specifies a matrix by an entry function, a nonzero modulus, a binary
exponent, and a pair of valid indices. Certified FP writers for these fields and
entries give a certified space-bounded evaluator for the selected power entry,
and suffice to decide whether it is zero in PSPACE.
Neither the dimension nor the exponent is required to be polynomially bounded:
only their binary descriptions are. No dense matrix is constructed.

The access contract covers every input string. A concrete input format must
supply validation/defaults satisfying it. This direct interface requires an FP
entry certificate. `MatrixPowerSpaceEntries` supplies the space-bounded simulation
for a certified space-bounded entry evaluator.
-/

@[expose] public section

namespace LeanCanny.Algebra.MatrixPower

open LeanCanny.Encoding

/-- The mathematical problem associated with each binary input context. -/
structure ModularFamily where
  dimension : List Bool → ℕ
  modulus : List Bool → ℕ
  exponent : List Bool → ℕ
  row : (c : List Bool) → Fin (dimension c)
  col : (c : List Bool) → Fin (dimension c)
  matrix : (c : List Bool) → Matrix (Fin (dimension c)) (Fin (dimension c)) (ZMod (modulus c))
  modulus_ne_zero : ∀ c, modulus c ≠ 0

def ModularFamily.zeroLanguage (F : ModularFamily) : Language :=
  {c | (F.matrix c ^ F.exponent c) (F.row c) (F.col c) = 0}

noncomputable def ModularFamily.value (F : ModularFamily) (c : List Bool) : List Bool :=
  residueBits ((F.matrix c ^ F.exponent c) (F.row c) (F.col c))

/-- Canonical binary field access and uniform entry access, on all contexts. -/
structure ModularAccess (F : ModularFamily) where
  dimension : List Bool → List Bool
  modulus : List Bool → List Bool
  exponent : List Bool → List Bool
  row : List Bool → List Bool
  col : List Bool → List Bool
  entry : List Bool → List Bool
  dimension_eq : ∀ c, dimension c = BinaryNatCode.encode (F.dimension c)
  modulus_eq : ∀ c, modulus c = BinaryNatCode.encode (F.modulus c)
  exponent_eq : ∀ c, exponent c = BinaryNatCode.encode (F.exponent c)
  row_eq : ∀ c, row c = BinaryNatCode.encode (F.row c).val
  col_eq : ∀ c, col c = BinaryNatCode.encode (F.col c).val
  entry_eq : ∀ c i j, entry (pair c
    (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) = residueBits (F.matrix c i j)

structure ModularAccess.PolyTime {F : ModularFamily} (a : ModularAccess F) : Prop where
  dimension : a.dimension ∈ FP
  modulus : a.modulus ∈ FP
  exponent : a.exponent ∈ FP
  row : a.row ∈ FP
  col : a.col ∈ FP
  entry : a.entry ∈ FP

structure ModularAccess.ControlsPolyTime {F : ModularFamily} (a : ModularAccess F) : Prop where
  dimension : a.dimension ∈ FP
  modulus : a.modulus ∈ FP
  exponent : a.exponent ∈ FP
  row : a.row ∈ FP
  col : a.col ∈ FP

theorem ModularAccess.controlsPolyTime_of_polyTime {F : ModularFamily} (a : ModularAccess F) (ha : a.PolyTime) :
    a.ControlsPolyTime := ⟨ha.dimension, ha.modulus, ha.exponent, ha.row, ha.col⟩

namespace ModularAccess
open Controller
open LeanCanny.Encoding.Brackets

def valueBits (packet : List Bool) : List Bool := (pairSnd packet).drop 1

theorem valueBits_mem_FP : valueBits ∈ FP := drop_mem_FP pairSnd_mem_FP (UnaryFn.const 1)

theorem valueBits_done {R : Type*} {n : ℕ} (c : List Bool) (enc : R → List Bool) (x : R) :
    valueBits (pair c (stateBits (n := n) enc (.done x))) = enc x := by
  simp [valueBits, stateBits]

/-- The orbit proof depends only on field writers and a transition certificate. -/
theorem evaluatorWithStep {F : ModularFamily} (a : ModularAccess F) (ha : a.ControlsPolyTime)
    (E : Computation.SpaceFunction (Controller.step (modularCallbacks a.dimension a.modulus a.entry))) :
    Computation.SpaceFunction F.value := by
  let ops := modularCallbacks a.dimension a.modulus a.entry
  let N := fun c => work (F.dimension c) (F.exponent c).size (F.exponent c) + 1
  let fields := fun c => (F.dimension c).size + (F.exponent c).size + (F.modulus c).size
  let B := fun c => 2 * c.length + 2 + 64 * (fields c + 1) ^ 2
  let W := fun c => (fields c + 2) * fields c + 1
  have hfields : Turing.MultiTapeTM.PolyBounded List.length fields := by
    have h := (ha.dimension.polyBounded_length.add ha.exponent.polyBounded_length).add
      ha.modulus.polyBounded_length
    simpa only [a.dimension_eq, a.exponent_eq, a.modulus_eq, Turing.MultiTapeTM.encBits_apply,
      BinaryNatCode.length_encode] using h
  have hB : Turing.MultiTapeTM.PolyBounded List.length B := by
    simpa only [B, pow_two] using
      (((Turing.MultiTapeTM.PolyBounded.const 2).mul Turing.MultiTapeTM.PolyBounded.self).add (.const 2)).add
        ((Turing.MultiTapeTM.PolyBounded.const 64).mul ((hfields.add (.const 1)).mul (hfields.add (.const 1))))
  have hW : Turing.MultiTapeTM.PolyBounded List.length W :=
    ((hfields.add (.const 2)).mul hfields).add (.const 1)
  have hc (c : List Bool) : CorrectAt ops c (F.matrix c) residueBits := by
    let : NeZero (F.modulus c) := ⟨F.modulus_ne_zero c⟩
    exact modularCallbacks_correctAt a.dimension a.modulus a.entry c (F.modulus c)
      (F.matrix c) (a.dimension_eq c) (a.modulus_eq c) (a.entry_eq c)
  have hinit (c : List Bool) : initialPacket a.exponent a.row a.col c =
      pair c (stateBits (residueBits (m := F.modulus c))
      (.eval ⟨(F.exponent c).size, F.exponent c, F.row c, F.col c⟩ [])) :=
    initialPacket_encode a.exponent a.row a.col c (residueBits (m := F.modulus c)) (F.exponent c)
      (F.row c) (F.col c) (a.exponent_eq c) (a.row_eq c) (a.col_eq c)
  refine (Computation.SpaceFunction.orbit_of_polyBounded E
    (initialPacket a.exponent a.row a.col) (initialPacket_mem_FP ha.exponent ha.row ha.col)
    halted valueBits halted_mem_FP valueBits_mem_FP N B W hB hW ?_ ?_ ?_ ?_).congr ?_
  · intro c t _
    let : NeZero (F.modulus c) := ⟨F.modulus_ne_zero c⟩
    rw [hinit c]
    exact modular_run_length_le a.dimension a.modulus a.entry c (F.modulus c)
      (F.matrix c) (hc c) (F.exponent c) t (F.row c) (F.col c)
  · intro c
    apply (work_add_one_le_two_pow (F.dimension c) (F.exponent c).size (F.exponent c)).trans
    apply Nat.pow_le_pow_right (by decide)
    dsimp only [W, fields]
    exact Nat.add_le_add_right (Nat.mul_le_mul (by omega) (by omega)) 1
  · intro c t ht
    rw [hinit c]
    exact halted_before ops c (F.matrix c) residueBits (hc c) (F.exponent c) t (F.row c) (F.col c) ht
  · intro c
    rw [hinit c]
    exact halted_after ops c (F.matrix c) residueBits (hc c) (F.exponent c) (F.row c) (F.col c)
  · funext c
    let : NeZero (F.modulus c) := ⟨F.modulus_ne_zero c⟩
    rw [hinit c, Controller.run_pow ops c (F.matrix c) residueBits (hc c), valueBits_done]
    rfl

theorem evaluator {F : ModularFamily} (a : ModularAccess F) (ha : a.PolyTime) :
    Computation.SpaceFunction F.value :=
  evaluatorWithStep a (controlsPolyTime_of_polyTime a ha)
    (Computation.SpaceFunction.ofFP _ (step_mem_FP _ (modularCallbacks_polyTime ha.dimension ha.modulus ha.entry)))

theorem zeroLanguage_mem_PSPACE {F : ModularFamily} (a : ModularAccess F) (ha : a.PolyTime) :
    F.zeroLanguage ∈ PSPACE := by
  let accept := fun bits : List Bool => decide (bits = [])
  have haFP : (fun bits => [accept bits]) ∈ FP :=
    (stringEq_fppred id_mem_FP (constFn_mem_FP [])).flag_mem_FP
  apply ((evaluator a ha).decider accept haFP ?_).mem_PSPACE
  intro c
  let : NeZero (F.modulus c) := ⟨F.modulus_ne_zero c⟩
  have hz : residueBits (0 : ZMod (F.modulus c)) = [] := by simp [residueBits, BinaryNatCode.encode]
  change ((F.matrix c ^ F.exponent c) (F.row c) (F.col c) = 0) ↔ decide (F.value c = []) = true
  rw [decide_eq_true_eq, ModularFamily.value, ← hz, (residueBits_injective (F.modulus c)).eq_iff]

end ModularAccess
end LeanCanny.Algebra.MatrixPower
