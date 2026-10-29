/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FixedWidthHeightSpace
public import LeanCanny.Encoding.FlatAffineIntegerSpace

/-! # Native weighted linear rows from signed affine records

The scalar reader decodes actual signed blocks of a charged record. The
streamed linear reader collects them at their selected variables, permitting
coincident indices. This covers direction rows and ancestral height rows.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineHeightCoefficient
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR MvPolynomial
open scoped BigOperators Classical
set_option backward.isDefEq.respectTransparency false

variable (A N W V entry : List Bool → ℕ) (record target modulus : List Bool → List Bool)

noncomputable def scalar (c : List Bool) (i : Fin (N c)) : ℤ :=
  FlatAffineFullSourceTower.integer (V c) (record c) (entry (pair c (BinaryNatCode.encode i.val)))

noncomputable def polynomial (f : (c : List Bool) → Fin (N c) → Fin (A c)) (c : List Bool) :
    MvPolynomial (Fin (A c)) ℤ := FixedWidthHeightBits.polynomial A N (scalar N V entry record) f c

noncomputable def value (f : (c : List Bool) → Fin (N c) → Fin (A c)) : List Bool → List Bool :=
  FixedWidthHeightBits.value A N W (scalar N V entry record) f target (FlatAffineIntegerSpace.modulusCode modulus)

noncomputable def reader : List Bool → List Bool :=
  FlatAffineIntegerSpace.value (V ∘ pairFst) entry (record ∘ pairFst) (modulus ∘ pairFst)

theorem reader_evaluator (hV : UnaryFn V) (he : UnaryFn entry) (hr : SpaceFunction record) (hm : modulus ∈ FP) :
    SpaceFunction (reader V entry record modulus) :=
  FlatAffineIntegerSpace.evaluator _ _ _ _ (hV.comp pairFst_mem_FP) he (hr.precompose _ pairFst_mem_FP)
    (mem_FP_comp pairFst_mem_FP hm)

theorem reader_packet (c : List Bool) (i : Fin (N c)) :
    reader V entry record modulus (pair c (BinaryNatCode.encode i.val)) =
      MatrixPower.residueBits ((scalar N V entry record c i : ℤ) :
        ZMod (Nat.fromBitsLE (FlatAffineIntegerSpace.modulusCode modulus c))) := by
  have he (q : List Bool) : reader V entry record modulus q =
      FlatAffineIntegerSpace.value V (fun _ => entry q) record modulus (pairFst q) := rfl
  rw [he, pairFst_pair]
  rw [FlatAffineIntegerSpace.modulusCode_eq, MacaulayBits.fromBits_encode]
  rfl

theorem evaluator {selected : List Bool → ℕ}
    (hA : UnaryFn A) (hN : UnaryFn N) (hW : UnaryFn W) (hV : UnaryFn V) (he : UnaryFn entry)
    (hs : BinaryFn selected) (hr : SpaceFunction record) (ht : target ∈ FP) (hm : modulus ∈ FP)
    (f : (c : List Bool) → Fin (N c) → Fin (A c))
    (hf : ∀ c i, selected (pair c (BinaryNatCode.encode i.val)) = (f c i).val) :
    SpaceFunction (value A N W V entry record target modulus f) := by
  apply FixedWidthHeightBits.evaluator hA hN hW hs ht (FlatAffineIntegerSpace.modulusCode_FP modulus hm)
    (reader_evaluator V entry record modulus hV he hr hm) (scalar N V entry record) f hf
  · intro c
    rw [FlatAffineIntegerSpace.modulusCode_eq, MacaulayBits.fromBits_encode]
    omega
  · exact reader_packet N V entry record modulus

theorem evaluator_space {selected : List Bool → ℕ}
    (hA : UnaryFn A) (hN : UnaryFn N) (hW : UnaryFn W) (hV : UnaryFn V) (he : UnaryFn entry)
    (hs : SpaceFunction (BinaryNatCode.encode ∘ selected)) (hr : SpaceFunction record)
    (ht : target ∈ FP) (hm : modulus ∈ FP)
    (f : (c : List Bool) → Fin (N c) → Fin (A c))
    (hf : ∀ c i, selected (pair c (BinaryNatCode.encode i.val)) = (f c i).val) :
    SpaceFunction (value A N W V entry record target modulus f) := by
  apply FixedWidthHeightBits.evaluator_space hA hN hW hs ht (FlatAffineIntegerSpace.modulusCode_FP modulus hm)
    (reader_evaluator V entry record modulus hV he hr hm) (scalar N V entry record) f hf
  · intro c
    rw [FlatAffineIntegerSpace.modulusCode_eq, MacaulayBits.fromBits_encode]
    omega
  · exact reader_packet N V entry record modulus

theorem packet (f : (c : List Bool) → Fin (N c) → Fin (A c)) (c : List Bool) :
    value A N W V entry record target modulus f c =
      MatrixPower.residueBits (((polynomial A N V entry record f c).coeff
        (FixedWidthPolynomial.nativeExponent (Equiv.refl (Fin (A c))) (W c) (Nat.fromBitsLE (target c))) : ℤ) :
          ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  unfold value FixedWidthHeightBits.value
  rw [FlatAffineIntegerSpace.modulusCode_eq, MacaulayBits.fromBits_encode]
  rfl

end LeanCanny.Encoding.FlatAffineHeightCoefficient
