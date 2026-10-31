/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.BoundedFoldFP
public import LeanCanny.Algebra.ModularProductSpace

/-! # Polynomial-time modular folds over unary coordinate lists

FP factors or summands, a unary count, and an FP modulus give a native FP
sum or product. Every retained prefix is reduced, so its size bound is the
modulus word length. These folds can be nested inside a bounded modular
pass over the retained integer denominators.
-/

@[expose] public section
namespace LeanCanny.Algebra.ModularProduct
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] finish

theorem update_FP (modulus f : List Bool → List Bool) (hm : modulus ∈ FP) (hf : f ∈ FP) : update modulus f ∈ FP := by
  have HQ : (fun p => f (BoundedFold.query p)) ∈ FP := mem_FP_comp
    (f := BoundedFold.query) (g := f) BoundedFold.query_mem_FP hf
  exact mem_FP_comp (f := fun p => pair p (f (BoundedFold.query p))) (g := finish modulus)
    (mem_FP_pair id_mem_FP HQ) (finish_mem_FP hm)

theorem evaluator_FP (f modulus : List Bool → List Bool) (count : List Bool → ℕ)
    (hf : f ∈ FP) (hm : modulus ∈ FP) (hc : UnaryFn count)
    (a : (c : List Bool) → ℕ → ZMod (Nat.fromBitsLE (modulus c)))
    (hpos : ∀ c, 0 < Nat.fromBitsLE (modulus c))
    (ha : ∀ c i, i < count c → f (pair c (BinaryNatCode.encode i)) = residueBits (a c i)) :
    (fun c => residueBits (∏ i ∈ Finset.range (count c), a c i)) ∈ FP := by
  have E := BoundedFold.evaluator_FP (update modulus f) (seed modulus) count (fun c => (modulus c).length)
    (update_FP modulus f hm hf) (seed_mem_FP hm) hc (UnaryFn.length hm) (by
      intro c k hk
      let : NeZero (Nat.fromBitsLE (modulus c)) := ⟨(hpos c).ne'⟩
      rw [fold_eq_product modulus f c (count c) (a c) (hpos c) (ha c) k hk]
      exact ModularFold.bits_length_le modulus c _ (ZMod.val_lt _))
  refine mem_FP_of_eq E (fun c => ?_)
  exact fold_eq_product modulus f c (count c) (a c) (hpos c) (ha c) _ le_rfl

theorem evaluatorWithModulus_FP (f modulus : List Bool → List Bool) (count : List Bool → ℕ)
    (hf : f ∈ FP) (hm : modulus ∈ FP) (hc : UnaryFn count) (m : List Bool → ℕ)
    (hvalue : (fun c => Nat.fromBitsLE (modulus c)) = m)
    (a : (c : List Bool) → ℕ → ZMod (m c)) (hpos : ∀ c, 0 < m c)
    (ha : ∀ c i, i < count c → f (pair c (BinaryNatCode.encode i)) = residueBits (a c i)) :
    (fun c => residueBits (∏ i ∈ Finset.range (count c), a c i)) ∈ FP := by
  subst m
  exact evaluator_FP f modulus count hf hm hc a hpos ha

end LeanCanny.Algebra.ModularProduct

namespace LeanCanny.Algebra.ModularSum
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] finish

theorem update_FP (modulus f : List Bool → List Bool) (hm : modulus ∈ FP) (hf : f ∈ FP) : update modulus f ∈ FP := by
  have HQ : (fun p => f (BoundedFold.query p)) ∈ FP := mem_FP_comp
    (f := BoundedFold.query) (g := f) BoundedFold.query_mem_FP hf
  exact mem_FP_comp (f := fun p => pair p (f (BoundedFold.query p))) (g := finish modulus)
    (mem_FP_pair id_mem_FP HQ) (finish_mem_FP hm)

theorem evaluator_FP (f modulus : List Bool → List Bool) (count : List Bool → ℕ)
    (hf : f ∈ FP) (hm : modulus ∈ FP) (hc : UnaryFn count)
    (a : (c : List Bool) → ℕ → ZMod (Nat.fromBitsLE (modulus c)))
    (hpos : ∀ c, 0 < Nat.fromBitsLE (modulus c))
    (ha : ∀ c i, i < count c → f (pair c (BinaryNatCode.encode i)) = residueBits (a c i)) :
    (fun c => residueBits (∑ i ∈ Finset.range (count c), a c i)) ∈ FP := by
  have E := BoundedFold.evaluator_FP (update modulus f) (fun _ => []) count (fun c => (modulus c).length)
    (update_FP modulus f hm hf) (constFn_mem_FP []) hc (UnaryFn.length hm) (by
      intro c k hk
      let : NeZero (Nat.fromBitsLE (modulus c)) := ⟨(hpos c).ne'⟩
      rw [fold_eq_sum modulus f c (count c) (a c) (hpos c) (ha c) k hk]
      exact ModularFold.bits_length_le modulus c _ (ZMod.val_lt _))
  refine mem_FP_of_eq E (fun c => ?_)
  exact fold_eq_sum modulus f c (count c) (a c) (hpos c) (ha c) _ le_rfl

theorem evaluatorWithModulus_FP (f modulus : List Bool → List Bool) (count : List Bool → ℕ)
    (hf : f ∈ FP) (hm : modulus ∈ FP) (hc : UnaryFn count) (m : List Bool → ℕ)
    (hvalue : (fun c => Nat.fromBitsLE (modulus c)) = m)
    (a : (c : List Bool) → ℕ → ZMod (m c)) (hpos : ∀ c, 0 < m c)
    (ha : ∀ c i, i < count c → f (pair c (BinaryNatCode.encode i)) = residueBits (a c i)) :
    (fun c => residueBits (∑ i ∈ Finset.range (count c), a c i)) ∈ FP := by
  subst m
  exact evaluator_FP f modulus count hf hm hc a hpos ha

end LeanCanny.Algebra.ModularSum
