/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BinaryModFP

/-!
# Polynomial-time modular exponentiation on binary words

Repeated squaring folds over exponent digits, reducing after each product.
Input `pair base (pair exponent b)` specifies positive modulus `fromBitsLE b+1`.
Every partial result fits in the modulus word, so exponential exponents cause
no expansion of either the exponent or the unreduced power.
-/

@[expose] public section

namespace LeanCanny.Encoding.BinaryNat
open Complexity

/-- Input `pair modulus (pair left right)`. -/
def mulMod (p : List Bool) : List Bool := mod (pair (mul (pairSnd p)) (pairFst p))

theorem mulMod_mem_FP : mulMod ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair (mem_FP_comp pairSnd_mem_FP mul_mem_FP) pairFst_mem_FP) mod_mem_FP
  refine mem_FP_of_eq (g := mulMod) h ?_
  intro p
  simp only [Function.comp_apply, mulMod]

theorem mulMod_pair (m a b : List Bool) : mulMod (pair m (pair a b)) =
    (Nat.fromBitsLE a * Nat.fromBitsLE b % Nat.fromBitsLE m).bits := by
  simp only [mulMod, pairSnd_pair, pairFst_pair, mod_pair, mul_pair, Nat.fromBitsLE_bits]

def powFold (a m : List Bool) : List Bool → List Bool
  | [] => mod (pair [true] m)
  | false :: t => mulMod (pair m (pair (powFold a m t) (powFold a m t)))
  | true :: t => mulMod (pair m (pair a (mulMod (pair m (pair (powFold a m t) (powFold a m t))))))

theorem powFold_eq_bits (a m t : List Bool) :
    powFold a m t = (Nat.fromBitsLE a ^ Nat.fromBitsLE t % Nat.fromBitsLE m).bits := by
  induction t with
  | nil => simp [powFold, mod_pair, Nat.fromBitsLE, Nat.fromBits]
  | cons b t ih =>
    cases b with
    | false =>
      simp only [powFold, mulMod_pair, ih, Nat.fromBitsLE_bits, Nat.fromBitsLE_cons,
        Bool.false_eq_true, ↓reduceIte, Nat.zero_add]
      rw [← Nat.mul_mod, show 2 * Nat.fromBitsLE t = Nat.fromBitsLE t + Nat.fromBitsLE t by omega, pow_add]
    | true =>
      simp only [powFold, mulMod_pair, ih, Nat.fromBitsLE_bits, Nat.fromBitsLE_cons, ↓reduceIte]
      rw [show 1 + 2 * Nat.fromBitsLE t = 1 + (Nat.fromBitsLE t + Nat.fromBitsLE t) by omega,
        pow_add, pow_one, pow_add]
      simp only [Nat.mul_mod, Nat.mod_mod]

theorem powFold_length_le (a m t : List Bool) (hm : 0 < Nat.fromBitsLE m) :
    (powFold a m t).length ≤ m.length := by
  rw [powFold_eq_bits, Nat.size_eq_bits_len]
  exact (Nat.size_le_size (Nat.mod_lt _ hm).le).trans
    (Nat.size_le.mpr (Nat.fromBitsLE_lt_pow_length m))

def powContext (p : List Bool) : List Bool :=
  pair (pairFst p) (succ (pairSnd (pairSnd p)))

def powSquare (p : List Bool) : List Bool :=
  mulMod (pair (pairSnd (pairFst (pairFst p))) (pair (pairSnd (pairFst p)) (pairSnd (pairFst p))))

def powOdd (p : List Bool) : List Bool :=
  mulMod (pair (pairSnd (pairFst (pairFst p))) (pair (pairFst (pairFst (pairFst p))) (powSquare p)))

def powMod (p : List Bool) : List Bool :=
  powFold (pairFst (powContext p)) (pairSnd (powContext p)) (pairFst (pairSnd p))

theorem powContext_mem_FP : powContext ∈ FP := by
  have hm := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) succ_mem_FP
  have h := mem_FP_pair pairFst_mem_FP hm
  refine mem_FP_of_eq (g := powContext) h ?_
  intro p
  simp only [Function.comp_apply, powContext]

theorem powSquare_mem_FP : powSquare ∈ FP := by
  have hp := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have hm := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP
  have h := mem_FP_comp (mem_FP_pair hm (mem_FP_pair hp hp)) mulMod_mem_FP
  refine mem_FP_of_eq (g := powSquare) h ?_
  intro p
  simp only [Function.comp_apply, powSquare]

theorem powOdd_mem_FP : powOdd ∈ FP := by
  have hc := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hm := mem_FP_comp hc pairSnd_mem_FP
  have ha := mem_FP_comp hc pairFst_mem_FP
  have h := mem_FP_comp (mem_FP_pair hm (mem_FP_pair ha powSquare_mem_FP)) mulMod_mem_FP
  refine mem_FP_of_eq (g := powOdd) h ?_
  intro p
  simp only [Function.comp_apply, powOdd]

theorem powMod_eq_bits (p : List Bool) : powMod p =
    (Nat.fromBitsLE (pairFst p) ^ Nat.fromBitsLE (pairFst (pairSnd p)) %
      (Nat.fromBitsLE (pairSnd (pairSnd p)) + 1)).bits := by
  simp only [powMod, powFold_eq_bits, powContext, pairFst_pair, pairSnd_pair, succ_eq_bits,
    Nat.fromBitsLE_bits]

theorem powMod_mem_FP : powMod ∈ FP := by
  have hs := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
  have hm := mem_FP_comp powContext_mem_FP pairSnd_mem_FP
  have he := mem_FP_comp (mem_FP_pair (constFn_mem_FP [true]) hm) mod_mem_FP
  refine recFold_mem_FP_of_bound
    (g := fun z t => powFold (pairFst (powContext z)) (pairSnd (powContext z)) t)
    powSquare_mem_FP powOdd_mem_FP he powContext_mem_FP hs
    (bound := fun n => n + 1) ?_ ?_ ?_ (PolyBound.id.add (PolyBound.const 1)) ?_
  · intro z
    simp only [powFold, Function.comp_apply]
  · intro z t
    simp only [powFold, powSquare, pairFst_pair, pairSnd_pair]
  · intro z t
    simp only [powFold, powOdd, powSquare, pairFst_pair, pairSnd_pair]
  · intro z t _
    have hpos : 0 < Nat.fromBitsLE (pairSnd (powContext z)) := by
      simp only [powContext, pairSnd_pair, succ_eq_bits, Nat.fromBitsLE_bits]
      omega
    have hlen := powFold_length_le (pairFst (powContext z)) (pairSnd (powContext z)) t hpos
    have hsucc : (succ (pairSnd (pairSnd z))).length ≤ (pairSnd (pairSnd z)).length + 1 :=
      (normalize_length_le _).trans (increment_length_le _)
    have hmLen : (pairSnd (powContext z)).length ≤ z.length + 1 := by
      simp only [powContext, pairSnd_pair]
      exact hsucc.trans (Nat.add_le_add_right
        ((pairSnd_length_le (pairSnd z)).trans (pairSnd_length_le z)) 1)
    exact hlen.trans hmLen

end LeanCanny.Encoding.BinaryNat
