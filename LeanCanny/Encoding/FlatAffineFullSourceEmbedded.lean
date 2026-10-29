/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineFullSourceDerivative

/-! # Native original-source rows in arbitrary ambient layouts

The ambient variable count is a caller control. In particular it can include
the dummy coordinate of positive completion. One original coefficient call
reads either the embedded source or one of its embedded derivative derivatives.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineFullSourceEmbedded
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR MvPolynomial
open FlatAffineFullSourceTower (Inputs arity degree)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedFullCriticalSamples.polynomial

noncomputable def coefficient (F : Inputs) (A O W : List Bool → ℕ)
    (target modulus : List Bool → List Bool) : List Bool → List Bool :=
  FixedWidthBlockRenameBits.value (arity F) A O W target (FlatAffineFullSourceBlockCoefficient.reader F W modulus)

theorem coefficient_evaluator {F : Inputs} (h : F.Access) {A O W : List Bool → ℕ}
    (hA : UnaryFn A) (hO : UnaryFn O) (hW : UnaryFn W)
    {target modulus : List Bool → List Bool} (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (coefficient F A O W target modulus) :=
  FixedWidthBlockRenameBits.evaluator _ _ _ _ _ (FlatAffineFullSourceBlockCoefficient.reader_evaluator h hW hm)
    (FlatAffineFullSourceTower.arity_unary h) hA hO hW ht

theorem coefficient_packet (F : Inputs) (A O W : List Bool → ℕ) (target modulus : List Bool → List Bool)
    (c : List Bool) (hfit : O c + arity F c ≤ A c) :
    coefficient F A O W target modulus c = MatrixPower.residueBits
      (((rename (BlockRenameCoefficient.shift (arity F c) (A c) (O c) hfit)
        (BoundedFullCriticalSamples.polynomial F.source c)).coeff
          (FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (A c))) (W c) (Nat.fromBitsLE (target c))) : ℤ) :
            ZMod (Nat.fromBitsLE (modulus c) + 1)) :=
  FixedWidthBlockRenameBits.packet _ _ _ _ _ _ hfit _ c _ rfl rfl rfl
    (FlatAffineFullSourceBlockCoefficient.reader_packet F W modulus c)

noncomputable def indexed (F : Inputs) (A O W : List Bool → ℕ)
    (modulus : List Bool → List Bool) : List Bool → List Bool :=
  FixedWidthBlockRenameBits.value (arity F ∘ pairFst) (A ∘ pairFst) (O ∘ pairFst) (W ∘ pairFst)
    pairSnd ((FlatAffineFullSourceBlockCoefficient.reader F W modulus) ∘ FlatAffineFullSourceDerivative.flattenQuery)

theorem indexed_evaluator {F : Inputs} (h : F.Access) {A O W : List Bool → ℕ}
    (hA : UnaryFn A) (hO : UnaryFn O) (hW : UnaryFn W)
    {modulus : List Bool → List Bool} (hm : modulus ∈ FP) : SpaceFunction (indexed F A O W modulus) :=
  FixedWidthBlockRenameBits.evaluator _ _ _ _ _
    ((FlatAffineFullSourceBlockCoefficient.reader_evaluator h hW hm).precompose _ FlatAffineFullSourceDerivative.flattenQuery_FP)
    ((FlatAffineFullSourceTower.arity_unary h).comp pairFst_mem_FP) (hA.comp pairFst_mem_FP)
    (hO.comp pairFst_mem_FP) (hW.comp pairFst_mem_FP) pairSnd_mem_FP

theorem indexed_packet (F : Inputs) (A O W : List Bool → ℕ) (modulus : List Bool → List Bool)
    (c : List Bool) (hfit : O c + arity F c ≤ A c) (r : ℕ) :
    indexed F A O W modulus (pair c (BinaryNatCode.encode r)) = MatrixPower.residueBits
      (((rename (BlockRenameCoefficient.shift (arity F c) (A c) (O c) hfit)
        (BoundedFullCriticalSamples.polynomial F.source c)).coeff
          (FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (A c))) (W c) r) : ℤ) :
            ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  generalize hz : pair c (BinaryNatCode.encode r) = z
  have hc : pairFst z = c := by rw [← hz, pairFst_pair]
  have hr : Nat.fromBitsLE (pairSnd z) = r := by rw [← hz, pairSnd_pair, MacaulayBits.fromBits_encode]
  subst c
  subst r
  apply FixedWidthBlockRenameBits.packet _ _ _ _ _ _ hfit _ z _ rfl rfl rfl
  intro k
  simp only [Function.comp_apply, FlatAffineFullSourceDerivative.flattenQuery, pairFst_pair, pairSnd_pair]
  exact FlatAffineFullSourceBlockCoefficient.reader_packet F W modulus (pairFst z) k

noncomputable def derivative (F : Inputs) (A O W V selected : List Bool → ℕ)
    (target modulus : List Bool → List Bool) : List Bool → List Bool :=
  FixedWidthDerivativeBits.value A W V (degree F) selected target
    (FlatAffineIntegerSpace.modulusCode modulus) (indexed F A O W modulus)

theorem derivative_evaluator {F : Inputs} (h : F.Access) {A O W V selected : List Bool → ℕ}
    (hA : UnaryFn A) (hO : UnaryFn O) (hW : UnaryFn W) (hV : UnaryFn V) (hs : UnaryFn selected)
    {target modulus : List Bool → List Bool} (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (derivative F A O W V selected target modulus) :=
  FixedWidthDerivativeBits.evaluator_binary_degree _ _ _ _ _ _ _ (indexed_evaluator h hA hO hW hm)
    hA hW hV (FlatAffineFullSourceTower.degree_binary h) hs ht (FlatAffineIntegerSpace.modulusCode_FP modulus hm)

theorem derivative_packet (F : Inputs) (A O W V selected : List Bool → ℕ) (target modulus : List Bool → List Bool)
    (c : List Bool) (hfit : O c + arity F c ≤ A c) (i : Fin (arity F c))
    (hi : selected c = O c + i.val) (hW : degree F c < 2 ^ W c) :
    derivative F A O W V selected target modulus c = MatrixPower.residueBits
      (((rename (BlockRenameCoefficient.shift (arity F c) (A c) (O c) hfit)
        (pderiv i (BoundedFullCriticalSamples.polynomial F.source c))).coeff
          (FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (A c))) (V c) (Nat.fromBitsLE (target c))) : ℤ) :
            ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  let f := BlockRenameCoefficient.shift (arity F c) (A c) (O c) hfit
  have H := FixedWidthDerivativeBits.packet A W V (degree F) selected target
    (FlatAffineIntegerSpace.modulusCode modulus) (Equiv.refl (Fin (A c)))
    (indexed F A O W modulus) c (rename f (BoundedFullCriticalSamples.polynomial F.source c)) (f i)
      (Nat.fromBitsLE (modulus c) + 1) rfl hi (by unfold degree; omega)
      ((totalDegree_rename_le _ _).trans ((BoundedFullCriticalSamples.source_degree F.source c).trans (Nat.le_succ _)))
      hW (FlatAffineIntegerSpace.modulusCode_eq modulus c) (indexed_packet F A O W modulus c hfit)
  have he : FixedWidthDerivativeBits.exponent V target (Equiv.refl (Fin (A c))) c =
      FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (A c))) (V c) (Nat.fromBitsLE (target c)) := by
    ext j
    exact (FixedWidthBlockRenameBits.entry_bits _ _ _).symm
  rw [pderiv_rename (BlockRenameCoefficient.shift_injective _ _ _ _) i, he] at H
  exact H

end LeanCanny.Encoding.FlatAffineFullSourceEmbedded
