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

namespace ModularAccess
open Controller
open LeanCanny.Encoding.Brackets

def valueBits (packet : List Bool) : List Bool := (pairSnd packet).drop 1

theorem valueBits_mem_FP : valueBits ∈ FP := drop_mem_FP pairSnd_mem_FP (UnaryFn.const 1)

theorem valueBits_done {R : Type*} {n : ℕ} (c : List Bool) (enc : R → List Bool) (x : R) :
    valueBits (pair c (stateBits (n := n) enc (.done x))) = enc x := by
  simp [valueBits, stateBits]

theorem evaluator {F : ModularFamily} (a : ModularAccess F) (ha : a.PolyTime) :
    Computation.SpaceFunction F.value := by
  let ops := modularCallbacks a.dimension a.modulus a.entry
  let T := fun c => work (F.dimension c) (F.exponent c).size (F.exponent c) + 1
  have hc (c : List Bool) : CorrectAt ops c (F.matrix c) residueBits := by
    let : NeZero (F.modulus c) := ⟨F.modulus_ne_zero c⟩
    exact modularCallbacks_correctAt a.dimension a.modulus a.entry c (F.modulus c)
      (F.matrix c) (a.dimension_eq c) (a.modulus_eq c) (a.entry_eq c)
  have hinit (c : List Bool) : initialPacket a.exponent a.row a.col c =
      pair c (stateBits (residueBits (m := F.modulus c))
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
  refine (Computation.SpaceFunction.orbit
    (Computation.SpaceFunction.ofFP (Controller.step ops)
      (step_mem_FP ops (modularCallbacks_polyTime ha.dimension ha.modulus ha.entry)))
    (initialPacket a.exponent a.row a.col) (initialPacket_mem_FP ha.exponent ha.row ha.col)
    halted valueBits halted_mem_FP valueBits_mem_FP T
    (2 * Polynomial.X + 2 + 64 * (p + 1) ^ 2) ((p + 2) * p + 1)
    ?_ ?_ ?_ ?_).congr ?_
  · intro c t _
    let : NeZero (F.modulus c) := ⟨F.modulus_ne_zero c⟩
    rw [hinit c]
    have hlen := modular_run_length_le a.dimension a.modulus a.entry c (F.modulus c)
      (F.matrix c) (hc c) (F.exponent c) t (F.row c) (F.col c)
    have hpow := Nat.pow_le_pow_left (Nat.add_le_add_right (hbits c) 1) 2
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_X, Polynomial.eval_pow, Polynomial.eval_one]
    exact hlen.trans (Nat.add_le_add_left (Nat.mul_le_mul_left 64 hpow) _)
  · intro c
    have hb := hbits c
    have hw := work_add_one_le_two_pow (F.dimension c) (F.exponent c).size (F.exponent c)
    have hprod : ((F.dimension c).size + 2) * (F.exponent c).size ≤
        (p.eval c.length + 2) * p.eval c.length :=
      Nat.mul_le_mul (by omega) (by omega)
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_one]
    exact hw.trans (Nat.pow_le_pow_right (by decide) (Nat.add_le_add_right hprod 1))
  · intro c t ht
    rw [hinit c]
    exact halted_before ops c (F.matrix c) residueBits (hc c) (F.exponent c) t
      (F.row c) (F.col c) ht
  · intro c
    rw [hinit c]
    exact halted_after ops c (F.matrix c) residueBits (hc c) (F.exponent c) (F.row c) (F.col c)
  · funext c
    let : NeZero (F.modulus c) := ⟨F.modulus_ne_zero c⟩
    rw [hinit c, show T c = work (F.dimension c) (F.exponent c).size (F.exponent c) + 1 from rfl,
      Controller.run_pow ops c (F.matrix c) residueBits (hc c)]
    rw [valueBits_done]
    rfl

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
