/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.ModularFoldRecursiveController

/-! # Native modular products with local processing of each charged reply

The transformation receives the original context, the binary factor index,
and its recursively computed residue. Powers can therefore be applied before
multiplication without assuming an evaluator for any factor.
-/
@[expose] public section
namespace LeanCanny.Algebra.TransformedRecursiveProduct
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM
open scoped BigOperators

def finish (modulus transform : List Bool → List Bool) (z : List Bool) : List Bool :=
  ModularProduct.finish modulus (pair (pairFst z)
    (transform (pair (BoundedFold.query (pairFst z)) (pairSnd z))))

theorem finish_FP (modulus transform : List Bool → List Bool)
    (hm : modulus ∈ FP) (ht : transform ∈ FP) : finish modulus transform ∈ FP :=
  mem_FP_comp (mem_FP_pair pairFst_mem_FP
    (mem_FP_comp (mem_FP_pair (mem_FP_comp pairFst_mem_FP BoundedFold.query_mem_FP) pairSnd_mem_FP) ht))
    (ModularProduct.finish_mem_FP hm)

def program (count : List Bool → ℕ) (modulus task transform : List Bool → List Bool) : RecursiveFold.Program where
  count := count
  seed := ModularProduct.seed modulus
  entryTask := task
  finish := finish modulus transform

theorem certificates (count : List Bool → ℕ) (modulus task transform : List Bool → List Bool)
    (hc : BinaryFn count) (hm : modulus ∈ FP) (hq : task ∈ FP) (ht : transform ∈ FP) :
    (program count modulus task transform).controller.Certificates (encQ := encBits) (encS := RecursiveFold.encState) :=
  RecursiveFold.Program.certificates _ hc (ModularProduct.seed_mem_FP hm) hq (finish_FP modulus transform hm ht)

def mapped (task transform answer : List Bool → List Bool) (p : List Bool) : List Bool :=
  transform (pair p (answer (task p)))

theorem update_eq (count : List Bool → ℕ) (modulus task transform answer : List Bool → List Bool) :
    (program count modulus task transform).update answer =
      ModularProduct.update modulus (mapped task transform answer) := by
  funext p
  simp only [RecursiveFold.Program.update, program, finish, mapped, ModularProduct.update,
    BoundedFold.update, Function.comp_apply, pairFst_pair, pairSnd_pair]

theorem partialValue (count : List Bool → ℕ) (modulus task transform answer : List Bool → List Bool)
    (q : List Bool) (a : ℕ → ZMod (Nat.fromBitsLE (modulus q)))
    (hpos : 0 < Nat.fromBitsLE (modulus q))
    (ha : ∀ i < count q, mapped task transform answer (pair q (BinaryNatCode.encode i)) = residueBits (a i))
    (k : ℕ) (hk : k ≤ count q) :
    (program count modulus task transform).partialValue answer q k = residueBits (∏ i ∈ Finset.range k, a i) := by
  unfold RecursiveFold.Program.partialValue
  rw [update_eq]
  exact ModularProduct.fold_eq_product modulus (mapped task transform answer) q (count q) a hpos ha k hk

/-- Avoid rewriting dependent residue types through the interpreted controller. -/
theorem partialValueWithModulus (count : List Bool → ℕ) (modulus task transform answer : List Bool → List Bool)
    (m : List Bool → ℕ) (hm : (fun q => Nat.fromBitsLE (modulus q)) = m)
    (q : List Bool) (a : ℕ → ZMod (m q)) (hpos : 0 < m q)
    (ha : ∀ i < count q, mapped task transform answer (pair q (BinaryNatCode.encode i)) = residueBits (a i))
    (k : ℕ) (hk : k ≤ count q) :
    (program count modulus task transform).partialValue answer q k = residueBits (∏ i ∈ Finset.range k, a i) := by
  subst m
  exact partialValue count modulus task transform answer q a hpos ha k hk

theorem orbit_length (count : List Bool → ℕ) (modulus task transform answer : List Bool → List Bool)
    (q : List Bool) (a : ℕ → ZMod (Nat.fromBitsLE (modulus q)))
    (hpos : 0 < Nat.fromBitsLE (modulus q))
    (ha : ∀ i < count q, mapped task transform answer (pair q (BinaryNatCode.encode i)) = residueBits (a i)) (t : ℕ) :
    (RecursiveFold.encState (((program count modulus task transform).controller.reference answer)^[t]
      ((program count modulus task transform).initial q))).length ≤
      2 * q.length + 2 * (encNat (count q)).length + (modulus q).length + 2 := by
  apply RecursiveFold.Program.orbit_length
  intro k hk
  rw [partialValue count modulus task transform answer q a hpos ha k hk]
  exact ModularFold.RecursiveStage.residue_length modulus q hpos _

theorem output_when_halted (count : List Bool → ℕ) (modulus task transform answer : List Bool → List Bool)
    (q : List Bool) (a : ℕ → ZMod (Nat.fromBitsLE (modulus q)))
    (hpos : 0 < Nat.fromBitsLE (modulus q))
    (ha : ∀ i < count q, mapped task transform answer (pair q (BinaryNatCode.encode i)) = residueBits (a i)) (t : ℕ)
    (hh : (program count modulus task transform).controller.halted
      (((program count modulus task transform).controller.reference answer)^[t]
        ((program count modulus task transform).initial q)) = true) :
    (program count modulus task transform).controller.output
      (((program count modulus task transform).controller.reference answer)^[t]
        ((program count modulus task transform).initial q)) = residueBits (∏ i ∈ Finset.range (count q), a i) :=
  ((program count modulus task transform).output_when_halted answer q t hh).trans
    (partialValue count modulus task transform answer q a hpos ha _ le_rfl)

end LeanCanny.Algebra.TransformedRecursiveProduct
