/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.RecursiveFoldController
public import LeanCanny.Algebra.ModularProductSpace

/-! # Resumable modular sums and products of recursive entries

Local certificates assume no computation of the recursively requested
entries. The accumulator always fits in the requested modulus word, even
for empty folds and modulus one. Requests are precisely the bounded entry
queries, ready for a ranked mixed-stage controller.
-/

@[expose] public section
namespace LeanCanny.Algebra.ModularFold.RecursiveStage
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

def sumProgram (count : List Bool → ℕ) (modulus entryTask : List Bool → List Bool) : RecursiveFold.Program where
  count := count
  seed _ := []
  entryTask := entryTask
  finish := ModularSum.finish modulus

def productProgram (count : List Bool → ℕ) (modulus entryTask : List Bool → List Bool) : RecursiveFold.Program where
  count := count
  seed := ModularProduct.seed modulus
  entryTask := entryTask
  finish := ModularProduct.finish modulus

variable (count : List Bool → ℕ) (modulus entryTask answer : List Bool → List Bool)

theorem sum_certificates (hc : BinaryFn count) (hm : modulus ∈ FP) (he : entryTask ∈ FP) :
    (sumProgram count modulus entryTask).controller.Certificates (encQ := encBits) (encS := RecursiveFold.encState) :=
  RecursiveFold.Program.certificates _ hc (constFn_mem_FP []) he (ModularSum.finish_mem_FP hm)

theorem product_certificates (hc : BinaryFn count) (hm : modulus ∈ FP) (he : entryTask ∈ FP) :
    (productProgram count modulus entryTask).controller.Certificates (encQ := encBits) (encS := RecursiveFold.encState) :=
  RecursiveFold.Program.certificates _ hc (ModularProduct.seed_mem_FP hm) he (ModularProduct.finish_mem_FP hm)

theorem sum_partialValue (c : List Bool) (a : ℕ → ZMod (Nat.fromBitsLE (modulus c)))
    (hpos : 0 < Nat.fromBitsLE (modulus c))
    (ha : ∀ i < count c, answer (entryTask (pair c (BinaryNatCode.encode i))) = residueBits (a i))
    (k : ℕ) (hk : k ≤ count c) :
    (sumProgram count modulus entryTask).partialValue answer c k = residueBits (∑ i ∈ Finset.range k, a i) :=
  ModularSum.fold_eq_sum modulus (answer ∘ entryTask) c (count c) a hpos ha k hk

theorem product_partialValue (c : List Bool) (a : ℕ → ZMod (Nat.fromBitsLE (modulus c)))
    (hpos : 0 < Nat.fromBitsLE (modulus c))
    (ha : ∀ i < count c, answer (entryTask (pair c (BinaryNatCode.encode i))) = residueBits (a i))
    (k : ℕ) (hk : k ≤ count c) :
    (productProgram count modulus entryTask).partialValue answer c k = residueBits (∏ i ∈ Finset.range k, a i) :=
  ModularProduct.fold_eq_product modulus (answer ∘ entryTask) c (count c) a hpos ha k hk

theorem residue_length (c : List Bool) (hpos : 0 < Nat.fromBitsLE (modulus c))
    (x : ZMod (Nat.fromBitsLE (modulus c))) : (residueBits x).length ≤ (modulus c).length := by
  let : NeZero (Nat.fromBitsLE (modulus c)) := ⟨hpos.ne'⟩
  exact ModularFold.bits_length_le modulus c x.val (ZMod.val_lt x)

theorem sum_orbit_length (c : List Bool) (a : ℕ → ZMod (Nat.fromBitsLE (modulus c)))
    (hpos : 0 < Nat.fromBitsLE (modulus c))
    (ha : ∀ i < count c, answer (entryTask (pair c (BinaryNatCode.encode i))) = residueBits (a i)) (t : ℕ) :
    (RecursiveFold.encState (((sumProgram count modulus entryTask).controller.reference answer)^[t]
      ((sumProgram count modulus entryTask).initial c))).length ≤
        2 * c.length + 2 * (encNat (count c)).length + (modulus c).length + 2 := by
  apply RecursiveFold.Program.orbit_length
  intro k hk
  rw [sum_partialValue count modulus entryTask answer c a hpos ha k hk]
  exact residue_length modulus c hpos _

theorem product_orbit_length (c : List Bool) (a : ℕ → ZMod (Nat.fromBitsLE (modulus c)))
    (hpos : 0 < Nat.fromBitsLE (modulus c))
    (ha : ∀ i < count c, answer (entryTask (pair c (BinaryNatCode.encode i))) = residueBits (a i)) (t : ℕ) :
    (RecursiveFold.encState (((productProgram count modulus entryTask).controller.reference answer)^[t]
      ((productProgram count modulus entryTask).initial c))).length ≤
        2 * c.length + 2 * (encNat (count c)).length + (modulus c).length + 2 := by
  apply RecursiveFold.Program.orbit_length
  intro k hk
  rw [product_partialValue count modulus entryTask answer c a hpos ha k hk]
  exact residue_length modulus c hpos _

theorem sum_output (c : List Bool) (a : ℕ → ZMod (Nat.fromBitsLE (modulus c)))
    (hpos : 0 < Nat.fromBitsLE (modulus c))
    (ha : ∀ i < count c, answer (entryTask (pair c (BinaryNatCode.encode i))) = residueBits (a i)) (t : ℕ)
    (hh : (sumProgram count modulus entryTask).controller.halted
      (((sumProgram count modulus entryTask).controller.reference answer)^[t]
        ((sumProgram count modulus entryTask).initial c)) = true) :
    (sumProgram count modulus entryTask).controller.output
      (((sumProgram count modulus entryTask).controller.reference answer)^[t]
        ((sumProgram count modulus entryTask).initial c)) = residueBits (∑ i ∈ Finset.range (count c), a i) :=
  (RecursiveFold.Program.output_when_halted _ answer c t hh).trans
    (sum_partialValue count modulus entryTask answer c a hpos ha _ le_rfl)

theorem product_output (c : List Bool) (a : ℕ → ZMod (Nat.fromBitsLE (modulus c)))
    (hpos : 0 < Nat.fromBitsLE (modulus c))
    (ha : ∀ i < count c, answer (entryTask (pair c (BinaryNatCode.encode i))) = residueBits (a i)) (t : ℕ)
    (hh : (productProgram count modulus entryTask).controller.halted
      (((productProgram count modulus entryTask).controller.reference answer)^[t]
        ((productProgram count modulus entryTask).initial c)) = true) :
    (productProgram count modulus entryTask).controller.output
      (((productProgram count modulus entryTask).controller.reference answer)^[t]
        ((productProgram count modulus entryTask).initial c)) = residueBits (∏ i ∈ Finset.range (count c), a i) :=
  (RecursiveFold.Program.output_when_halted _ answer c t hh).trans
    (product_partialValue count modulus entryTask answer c a hpos ha _ le_rfl)

end LeanCanny.Algebra.ModularFold.RecursiveStage
