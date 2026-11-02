/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.TransformedRecursiveProduct
/-! # Charged product folds over an already verified native space subroutine

Every update reduces modulo the original positive modulus. The number of
factors may be binary; accumulator length depends only on the modulus word.
-/
@[expose] public section
namespace LeanCanny.Algebra.TransformedRecursiveProduct
open LeanCanny.Encoding LeanCanny.Computation MatrixPower

private theorem fold_length (modulus f : List Bool→List Bool) (q : List Bool)
    (hpos : 0<Nat.fromBitsLE (modulus q)) (k : ℕ) :
    (BoundedFold.fold (ModularProduct.update modulus f) (ModularProduct.seed modulus) q k).length≤(modulus q).length := by
  cases k with
  | zero =>
    simp only [BoundedFold.fold,ModularProduct.seed,ArithmeticBits.one,BinaryNat.mod_pair]
    exact ModularFold.bits_length_le modulus q _ (Nat.mod_lt _ hpos)
  | succ k =>
    simp only [BoundedFold.fold,ModularProduct.update,BoundedFold.update,ModularProduct.finish,ModularFold.finish,
      pairFst_pair,pairSnd_pair,BoundedFold.context_packet,BinaryNat.mod_pair]
    exact ModularFold.bits_length_le modulus q _ (Nat.mod_lt _ hpos)

theorem value_evaluator (count : List Bool→ℕ) (modulus task transform : List Bool→List Bool)
    (hc : BinaryFn count) (hm : modulus∈FP) (ht : task∈FP) (htr : transform∈FP)
    (hpos : ∀ q,0<Nat.fromBitsLE (modulus q))
    (answer : List Bool→List Bool) (E : SpaceFunction answer) :
    SpaceFunction ((program count modulus task transform).value answer) := by
  have EM : SpaceFunction (mapped task transform answer) := E.call task transform ht htr
  have EU := ModularProduct.updateEvaluator EM modulus hm
  have EF := BoundedFold.evaluator_polyBounded EU (fun q=>BinaryNatCode.encode (count q)) (ModularProduct.seed modulus)
    hc.bits_mem_FP (ModularProduct.seed_mem_FP hm)
    (B:=fun q=>(modulus q).length)
    (by simpa only [Turing.MultiTapeTM.encBits_apply] using (FP.computable hm).polyBounded_length)
    (fun q k _=>fold_length modulus (mapped task transform answer) q (hpos q) k)
  apply EF.congr
  funext q
  rw [BinaryNatCode.encode,Nat.fromBitsLE_bits]
  change _=(BoundedFold.fold ((program count modulus task transform).update answer)
    (ModularProduct.seed modulus) q (count q))
  rw [update_eq]

end LeanCanny.Algebra.TransformedRecursiveProduct
