/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineFullSourceBlockCoefficient
public import LeanCanny.Algebra.FixedWidthDerivativeBinarySpace
public import LeanCanny.Encoding.FlatAffineIntegerSpace

/-! # Native source partial derivatives in affine tower blocks

One native coefficient call computes a partial derivative of the embedded
original source. Degree bounds stay binary; exponent widths stay unary.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineFullSourceDerivative
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR MvPolynomial
open FlatAffineFullSourceTower (Inputs arity count degree)
open FlatAffineFullSourceBlockCoefficient (reader reader_evaluator reader_packet)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedFullCriticalSamples.polynomial

def flattenQuery (q : List Bool) : List Bool := pair (pairFst (pairFst q)) (pairSnd q)
theorem flattenQuery_FP : flattenQuery ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP

noncomputable def indexedReader (F : Inputs) (O W : List Bool → ℕ)
    (modulus : List Bool → List Bool) : List Bool → List Bool :=
  FixedWidthBlockRenameBits.value (arity F ∘ pairFst) (count F ∘ pairFst) (O ∘ pairFst) (W ∘ pairFst)
    pairSnd ((reader F W modulus) ∘ flattenQuery)

theorem indexedReader_evaluator {F : Inputs} (h : F.Access) {O W : List Bool → ℕ}
    (hO : UnaryFn O) (hW : UnaryFn W) {modulus : List Bool → List Bool} (hm : modulus ∈ FP) :
    SpaceFunction (indexedReader F O W modulus) :=
  FixedWidthBlockRenameBits.evaluator _ _ _ _ _
    ((reader_evaluator h hW hm).precompose flattenQuery flattenQuery_FP)
    ((FlatAffineFullSourceTower.arity_unary h).comp pairFst_mem_FP)
    ((FlatAffineFullSourceTower.count_unary h).comp pairFst_mem_FP)
    (hO.comp pairFst_mem_FP) (hW.comp pairFst_mem_FP) pairSnd_mem_FP

theorem indexedReader_packet (F : Inputs) (O W : List Bool → ℕ) (modulus : List Bool → List Bool)
    (c : List Bool) (hfit : O c + arity F c ≤ count F c) (r : ℕ) :
    indexedReader F O W modulus (pair c (BinaryNatCode.encode r)) = MatrixPower.residueBits
      (((rename (BlockRenameCoefficient.shift (arity F c) (count F c) (O c) hfit)
        (BoundedFullCriticalSamples.polynomial F.source c)).coeff
          (FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (count F c))) (W c) r) : ℤ) :
            ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  generalize hz : pair c (BinaryNatCode.encode r) = z
  have hc : pairFst z = c := by rw [← hz, pairFst_pair]
  have hr : Nat.fromBitsLE (pairSnd z) = r := by rw [← hz, pairSnd_pair, MacaulayBits.fromBits_encode]
  subst c
  subst r
  apply FixedWidthBlockRenameBits.packet _ _ _ _ _ _ hfit _ z _ rfl rfl rfl
  intro k
  simp only [Function.comp_apply, flattenQuery, pairFst_pair, pairSnd_pair]
  exact reader_packet F W modulus (pairFst z) k

noncomputable def value (F : Inputs) (O W V selected : List Bool → ℕ)
    (target modulus : List Bool → List Bool) : List Bool → List Bool :=
  FixedWidthDerivativeBits.value (count F) W V (degree F) selected target
    (FlatAffineIntegerSpace.modulusCode modulus) (indexedReader F O W modulus)

theorem evaluator {F : Inputs} (h : F.Access) {O W V selected : List Bool → ℕ}
    (hO : UnaryFn O) (hW : UnaryFn W) (hV : UnaryFn V) (hs : UnaryFn selected)
    {target modulus : List Bool → List Bool} (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (value F O W V selected target modulus) :=
  FixedWidthDerivativeBits.evaluator_binary_degree _ _ _ _ _ _ _ (indexedReader_evaluator h hO hW hm)
    (FlatAffineFullSourceTower.count_unary h) hW hV (FlatAffineFullSourceTower.degree_binary h) hs ht
      (FlatAffineIntegerSpace.modulusCode_FP modulus hm)

theorem packet (F : Inputs) (O W V selected : List Bool → ℕ) (target modulus : List Bool → List Bool)
    (c : List Bool) (hfit : O c + arity F c ≤ count F c) (i : Fin (arity F c))
    (hi : selected c = O c + i.val) (hW : degree F c < 2 ^ W c) :
    value F O W V selected target modulus c = MatrixPower.residueBits
      (((pderiv (BlockRenameCoefficient.shift (arity F c) (count F c) (O c) hfit i)
        (rename (BlockRenameCoefficient.shift (arity F c) (count F c) (O c) hfit)
          (BoundedFullCriticalSamples.polynomial F.source c))).coeff
            (FixedWidthDerivativeBits.exponent V target (Equiv.refl (Fin (count F c))) c) : ℤ) :
        ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  apply FixedWidthDerivativeBits.packet _ _ _ _ _ _ _ (Equiv.refl (Fin (count F c)))
    (indexedReader F O W modulus) c _ _ (Nat.fromBitsLE (modulus c) + 1) rfl hi
    (by unfold degree; omega) ?_ hW (FlatAffineIntegerSpace.modulusCode_eq modulus c)
    (indexedReader_packet F O W modulus c hfit)
  exact (totalDegree_rename_le _ _).trans
    ((BoundedFullCriticalSamples.source_degree F.source c).trans (Nat.le_succ _))

end LeanCanny.Encoding.FlatAffineFullSourceDerivative
