/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatFullSourceTower
public import LeanCanny.Algebra.FixedWidthBlockRenameSpace

/-! # Native original-source coefficients in one flat stage block

The original full source is embedded in a selected block of the complete
tower's variables. The native reader rejects outside-block exponents and
retains the source context, modulus, and fixed-width layout. No ancestral
primitive-polynomial coefficient is an input.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatFullSourceBlockCoefficient
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR MvPolynomial
open FlatFullSourceTower (Inputs arity count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedFullCoefficient.valueData

noncomputable def reader (F : Inputs) (W : List Bool → ℕ) (modulus : List Bool → List Bool) :
    List Bool → List Bool :=
  BoundedFullCoefficient.value (F.source.comp pairFst) (W ∘ pairFst) pairSnd (modulus ∘ pairFst)

theorem reader_evaluator {F : Inputs} (h : F.Access) {W : List Bool → ℕ} (hW : UnaryFn W)
    {modulus : List Bool → List Bool} (hm : modulus ∈ FP) : SpaceFunction (reader F W modulus) :=
  BoundedFullCoefficient.evaluator (h.source.comp pairFst_mem_FP) (hW.comp pairFst_mem_FP)
    pairSnd_mem_FP (mem_FP_comp pairFst_mem_FP hm) (fun q => h.sourceArity (pairFst q))

theorem reader_packet (F : Inputs) (W : List Bool → ℕ) (modulus : List Bool → List Bool)
    (c : List Bool) (r : ℕ) : reader F W modulus (pair c (BinaryNatCode.encode r)) =
      MatrixPower.residueBits (((BoundedFullCriticalSamples.polynomial F.source c).coeff
        (FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (arity F c))) (W c) r) : ℤ) :
          ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  unfold reader
  rw [BoundedFullCoefficient.value_data]
  simp only [BoundedFullWriter.Readers.comp, Function.comp_apply, pairFst_pair, pairSnd_pair]
  rw [← BoundedFullCoefficient.value_data F.source W (fun _ => BinaryNatCode.encode r) modulus c]
  rw [FixedWidthPolynomial.nativeExponent_refl]
  rfl

noncomputable def value (F : Inputs) (O W : List Bool → ℕ)
    (target modulus : List Bool → List Bool) : List Bool → List Bool :=
  FixedWidthBlockRenameBits.value (arity F) (count F) O W target (reader F W modulus)

theorem evaluator {F : Inputs} (h : F.Access) {O W : List Bool → ℕ} (hO : UnaryFn O) (hW : UnaryFn W)
    {target modulus : List Bool → List Bool} (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (value F O W target modulus) :=
  FixedWidthBlockRenameBits.evaluator _ _ _ _ _ (reader_evaluator h hW hm)
    (FlatFullSourceTower.arity_unary h) (FlatFullSourceTower.count_unary h) hO hW ht

theorem packet (F : Inputs) (O W : List Bool → ℕ) (target modulus : List Bool → List Bool)
    (c : List Bool) (hfit : O c + arity F c ≤ count F c) :
    value F O W target modulus c = MatrixPower.residueBits
      (((rename (BlockRenameCoefficient.shift (arity F c) (count F c) (O c) hfit)
        (BoundedFullCriticalSamples.polynomial F.source c)).coeff
          (FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (count F c))) (W c)
            (Nat.fromBitsLE (target c))) : ℤ) : ZMod (Nat.fromBitsLE (modulus c) + 1)) :=
  FixedWidthBlockRenameBits.packet _ _ _ _ _ _ hfit _ c _ rfl rfl rfl
    (reader_packet F W modulus c)

end LeanCanny.Encoding.FlatFullSourceBlockCoefficient
