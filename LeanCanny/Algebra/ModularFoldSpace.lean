/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.BoundedFoldSpace
public import LeanCanny.Algebra.MatrixPowerArithmeticFP

/-! # Shared space certificates for modular folds

Only retained prefixes must be reduced. Child operands may be unreduced: the
finisher applies the operation and then reduces its result. An FP modulus bounds
every prefix, including the empty fold and modulus one.
-/

@[expose] public section

namespace LeanCanny.Algebra.ModularFold

open Turing.MultiTapeTM
open LeanCanny.Encoding LeanCanny.Computation
open MatrixPower

def finish (op modulus : List Bool → List Bool) (z : List Bool) : List Bool :=
  BinaryNat.mod (pair (op (pair (BoundedFold.accumulator (pairFst z)) (pairSnd z)))
    (modulus (pairFst (pairFst z))))

theorem finish_mem_FP {op modulus : List Bool → List Bool} (ho : op ∈ FP) (hm : modulus ∈ FP) :
    finish op modulus ∈ FP := by
  have ha := mem_FP_comp pairFst_mem_FP BoundedFold.accumulator_mem_FP
  have hc := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hv := mem_FP_comp (mem_FP_pair ha pairSnd_mem_FP) ho
  exact mem_FP_of_eq
    (mem_FP_comp (mem_FP_pair hv (mem_FP_comp hc hm)) BinaryNat.mod_mem_FP) (fun _ => rfl)

/-- A natural prefix fits in the FP modulus word whenever it is reduced. -/
theorem bits_length_le (modulus : List Bool → List Bool) (c : List Bool) (n : ℕ)
    (hn : n < Nat.fromBitsLE (modulus c)) : n.bits.length ≤ (modulus c).length := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr (hn.trans (Nat.fromBitsLE_lt_pow_length (modulus c)))

/-- Lift already proved prefix equations, deriving the space allowance from the
modulus writer. No bound on child operand values is required. -/
theorem evaluator_eq {f : List Bool → List Bool} (E : SpaceFunction f)
    (count modulus seed : List Bool → List Bool) (hc : count ∈ FP) (hm : modulus ∈ FP) (hs : seed ∈ FP)
    (v : List Bool → ℕ → ℕ)
    (hfold : ∀ c k, k ≤ Nat.fromBitsLE (count c) →
      BoundedFold.fold f seed c k = (v c k).bits)
    (hlt : ∀ c k, k ≤ Nat.fromBitsLE (count c) → v c k < Nat.fromBitsLE (modulus c)) :
    SpaceFunction (fun c => (v c (Nat.fromBitsLE (count c))).bits) := by
  apply BoundedFold.evaluator_eq E count seed hc hs (fun c k => (v c k).bits) hfold
    (B := fun c => (modulus c).length)
    (by simpa only [encBits_apply] using (FP.computable hm).polyBounded_length)
  exact fun c k hk => bits_length_le modulus c _ (hlt c k hk)

/-- Seed/update form of the modular semantic certificate. Values are reduced
after each update, so an empty product at modulus one also has a zero seed. -/
theorem evaluator_spec {f : List Bool → List Bool} (E : SpaceFunction f)
    (count modulus seed : List Bool → List Bool) (hc : count ∈ FP) (hm : modulus ∈ FP) (hs : seed ∈ FP)
    (v : List Bool → ℕ → ℕ) (hpos : ∀ c, 0 < Nat.fromBitsLE (modulus c))
    (hseed : ∀ c, seed c = (v c 0 % Nat.fromBitsLE (modulus c)).bits)
    (hstep : ∀ c k, k < Nat.fromBitsLE (count c) →
      f (BoundedFold.packet c k (v c k % Nat.fromBitsLE (modulus c)).bits) =
        (v c (k + 1) % Nat.fromBitsLE (modulus c)).bits) :
    SpaceFunction (fun c => (v c (Nat.fromBitsLE (count c)) % Nat.fromBitsLE (modulus c)).bits) := by
  apply BoundedFold.evaluator_spec E count seed hc hs
    (fun c k => (v c k % Nat.fromBitsLE (modulus c)).bits) hseed hstep
    (B := fun c => (modulus c).length)
    (by simpa only [encBits_apply] using (FP.computable hm).polyBounded_length)
  exact fun c k _ => bits_length_le modulus c _ (Nat.mod_lt _ (hpos c))

/-- Residue-valued prefixes share the same modulus-word bound. -/
theorem evaluator_residue {f : List Bool → List Bool} (E : SpaceFunction f)
    (count modulus seed : List Bool → List Bool) (hc : count ∈ FP) (hm : modulus ∈ FP) (hs : seed ∈ FP)
    (v : (c : List Bool) → ℕ → ZMod (Nat.fromBitsLE (modulus c)))
    (hpos : ∀ c, 0 < Nat.fromBitsLE (modulus c))
    (hfold : ∀ c k, k ≤ Nat.fromBitsLE (count c) →
      BoundedFold.fold f seed c k = residueBits (v c k)) :
    SpaceFunction (fun c => residueBits (v c (Nat.fromBitsLE (count c)))) := by
  apply evaluator_eq E count modulus seed hc hm hs (fun c k => (v c k).val) hfold
  intro c k _
  let : NeZero (Nat.fromBitsLE (modulus c)) := ⟨(hpos c).ne'⟩
  exact ZMod.val_lt _

end LeanCanny.Algebra.ModularFold
