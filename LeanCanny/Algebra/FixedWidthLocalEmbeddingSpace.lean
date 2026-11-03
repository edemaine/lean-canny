/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.FixedWidthEmbeddingSpace
/-! # Local injective embeddings need no malformed-input finite injection

The native repack and foreign-coordinate guard are total. Their coefficient
identity uses an injective embedding only at the current guarded input.
-/
@[expose] public section
namespace LeanCanny.Algebra.FixedWidthLocalEmbeddingBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower MvPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable (A N W : List Bool→ℕ) (target index modulus : List Bool→List Bool)

noncomputable def value (p : (c : List Bool)→MvPolynomial (Fin (A c)) ℤ) (c : List Bool) :=
  if FixedWidthEmbeddingBits.Guard A N W target index c then
    FixedWidthRowBits.value A W p (FixedWidthEmbeddingBits.word A N W target index) modulus c else []

theorem evaluator (p : (c : List Bool)→MvPolynomial (Fin (A c)) ℤ)
    (hA : UnaryFn A) (hN : UnaryFn N) (hW : UnaryFn W) (ht : target∈FP) (hi : index∈FP)
    (E : SpaceFunction (FixedWidthRowBits.value A W p (FixedWidthEmbeddingBits.word A N W target index) modulus)) :
    SpaceFunction (value A N W target index modulus p) := by
  have H:=SpaceFunction.branch (fun c=>decide (FixedWidthEmbeddingBits.Guard A N W target index c))
    (FixedWidthEmbeddingBits.guard_FP A N W target index hA hN hW ht hi).flag_mem_FP E
    (SpaceFunction.ofFP _ (constFn_mem_FP []))
  exact H.congr (funext fun c=>by simp only [value,decide_eq_true_eq])

private theorem queryExponent (q : List Bool) :
    FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (N q))) (W q) (Nat.fromBitsLE (target q))=
      RationalSubstitution.Indexed.exponentVector (N q) (FixedWidthQuery.coordinate W target q) := by
  ext i
  exact FixedWidthBlockRenameBits.entry_bits _ _ _

theorem value_at (p : (c : List Bool)→MvPolynomial (Fin (A c)) ℤ) (c : List Bool)
    (f : Fin (A c)→Fin (N c)) (hf : Function.Injective f)
    (hindex : ∀i,index (pair c (BinaryNatCode.encode i.val))=BinaryNatCode.encode (f i).val) :
    value A N W target index modulus p c=residueBits
      (((rename f (p c)).coeff (FixedWidthPolynomial.nativeExponent (Equiv.refl _) (W c)
        (Nat.fromBitsLE (target c)))) : ZMod (Nat.fromBitsLE (modulus c)+1)) := by
  rw [queryExponent,FixedWidthEmbeddingBits.coefficient A N W target index c f hf hindex]
  unfold value FixedWidthRowBits.value
  rw [queryExponent A W (FixedWidthEmbeddingBits.word A N W target index) c]
  by_cases h : FixedWidthEmbeddingBits.Guard A N W target index c
  · simp only [ite_eq_left h]
  · simp only [ite_eq_right h,Int.cast_zero,residueBits,ZMod.val_zero,BinaryNatCode.encode,Nat.zero_bits]

end LeanCanny.Algebra.FixedWidthLocalEmbeddingBits
