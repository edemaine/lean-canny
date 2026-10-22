/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.CoerciveHomogeneousRowParts
public import LeanCanny.Algebra.CoerciveHomogeneousLayout

/-! # Actual homogeneous row coefficients from the native branching reader -/

@[expose] public section
namespace LeanCanny.ETR.CoerciveHomogeneousReaderCorrect
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra MatrixPower
open CoerciveSourceSampling CoerciveHomogeneousRowReader
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] RationalSubstitutionBits.compiledTerm

abbrev word (c : List Bool) (i r u v : ℕ) :=
  pair c (pair (BinaryNatCode.encode i) (pair (BinaryNatCode.encode r)
    (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v))))

@[simp] lemma context_word (c : List Bool) (i r u v : ℕ) : context (word c i r u v) = c := by
  simp only [context, word, pairFst_pair]
@[simp] lemma row_word (c : List Bool) (i r u v : ℕ) : row (word c i r u v) = BinaryNatCode.encode i := by
  simp only [row, word, pairFst_pair, pairSnd_pair]
@[simp] lemma inner_word (c : List Bool) (i r u v : ℕ) : CoerciveHomogeneousRowReader.inner (word c i r u v) = BinaryNatCode.encode u := by
  simp only [CoerciveHomogeneousRowReader.inner, word, pairFst_pair, pairSnd_pair]
@[simp] lemma outer_word (c : List Bool) (i r u v : ℕ) : outer (word c i r u v) = BinaryNatCode.encode v := by
  simp only [outer, word, pairSnd_pair]
lemma zeroRow_word (c : List Bool) (i r u v : ℕ) : zeroRow (word c i r u v) ↔ i = 0 := by
  simp only [zeroRow, row_word, BinaryNatCode.encode, Nat.fromBitsLE_bits]

noncomputable def residue (modulus : List Bool → List Bool) (c : List Bool) (a : ℤ) :=
  residueBits (a : ZMod (Nat.fromBitsLE (modulus c) + 1))

private lemma mask_word (modulus : List Bool → List Bool) (c : List Bool) (i r u v s t : ℕ)
    (f : List Bool → List Bool) (a : ℤ) (hf : f (word c i r u v) = residue modulus c a) :
    maskValue (phase s t) f (word c i r u v) =
      residue modulus c (if v = s ∧ u = t then a else 0) := by
  have h := ModularResidueReaders.maskValue_eq (phase s t) f (word c i r u v)
    (a : ZMod (Nat.fromBitsLE (modulus c) + 1)) hf
  simpa only [ModularResidueReaders.maskValue, maskValue, residue, phase, outer_word,
    inner_word, BinaryNatCode.encode, Nat.fromBitsLE_bits, apply_ite, Int.cast_zero] using h

variable (input modulus : List Bool → List Bool) (coordinate : List Bool → ℕ) (c : List Bool)
variable (i : Fin (dimension (input c))) (hi : coordinate c = i.val) (r u v : ℕ)

include hi in
lemma coordinatePart_packet : coordinatePart input modulus coordinate (word c 0 r u v) =
    residue modulus c (((CoerciveCriticalHomogenization.finSystem (polynomial (input c))
      (degreeAllowance (input c)) i 0).coeff (RationalSubstitution.Indexed.exponentVector
        (dimension (input c) + 1) (FixedWidthPolynomial.entry (CoerciveHomogeneousRepack.width (input c)) r))).coeff v |>.coeff u) := by
  have hH := CoerciveHomogeneousRowParts.homogeneousCoordinate_packet input modulus c 0 r u v
  have hP := CoerciveHomogeneousRowParts.pointCoordinate_packet input modulus coordinate c i hi 0 r u v
  have hHm := mask_word modulus c 0 r u v 0 1 _ _ hH
  have hPm := mask_word modulus c 0 r u v 0 0 _ _ hP
  rw [coordinatePart, CoerciveQueryCoefficient.addValue, CoerciveQueryCoefficient.negValue]
  simp only [Function.comp_apply, context_word]
  change ModularResidueReaders.addValue (fun _ => modulus c)
    (maskValue (phase 0 1) (homogeneousCoordinate input modulus))
    (ModularResidueReaders.negValue (fun _ => modulus c)
      (maskValue (phase 0 0) (pointCoordinate input modulus coordinate))) (word c 0 r u v) = _
  rw [ModularResidueReaders.addValue_eq _ _ _ _ _ _ hHm
    (ModularResidueReaders.negValue_eq _ _ _ _ hPm)]
  rw [CoerciveHomogeneousLayout.fin_coordinate_coeff]
  simp only [residue, sub_eq_add_neg, Int.cast_add, Int.cast_neg]

lemma gradientPart_packet (j : Fin (dimension (input c))) :
    gradientPart input modulus (word c j.succ.val r u v) =
    residue modulus c (((CoerciveCriticalHomogenization.finSystem (polynomial (input c))
      (degreeAllowance (input c)) i j.succ).coeff (RationalSubstitution.Indexed.exponentVector
        (dimension (input c) + 1) (FixedWidthPolynomial.entry (CoerciveHomogeneousRepack.width (input c)) r))).coeff v |>.coeff u) := by
  have hO := CoerciveHomogeneousRowParts.ordinary_packet input modulus c j r u v
  have hL := CoerciveHomogeneousRowParts.leading_packet input modulus c j r u v
  have hOm := mask_word modulus c j.succ.val r u v 0 0 _ _ hO
  have hLm := mask_word modulus c j.succ.val r u v 1 0 _ _ hL
  rw [gradientPart, CoerciveQueryCoefficient.addValue]
  simp only [Function.comp_apply, context_word]
  change ModularResidueReaders.addValue (fun _ => modulus c)
    (maskValue (phase 0 0) (ordinary input modulus))
    (maskValue (phase 1 0) (leading input modulus)) (word c j.succ.val r u v) = _
  rw [ModularResidueReaders.addValue_eq _ _ _ _ _ _ hOm hLm]
  rw [CoerciveHomogeneousLayout.fin_gradient]
  simp only [residue, Int.cast_add]

include hi in
lemma value_packet (j : Fin (dimension (input c) + 1)) :
    value input modulus coordinate (word c j.val r u v) =
    residueBits (((((CoerciveCriticalHomogenization.finSystem (polynomial (input c))
      (degreeAllowance (input c)) i j).coeff (RationalSubstitution.Indexed.exponentVector
        (dimension (input c) + 1) (FixedWidthPolynomial.entry (CoerciveHomogeneousRepack.width (input c)) r))).coeff v).coeff u : ℤ) :
          ZMod (Nat.fromBitsLE (modulus c) + 1)) := by
  have hv : valid input coordinate (word c j.val r u v) := by
    simp only [valid, context_word, row_word, BinaryNatCode.encode, Nat.fromBitsLE_bits, hi]
    exact ⟨i.isLt,j.isLt⟩
  unfold CoerciveHomogeneousRowReader.value
  rw [ite_eq_left hv]
  refine Fin.cases ?_ (fun j => ?_) j
  · simp only [Fin.val_zero, zeroRow_word, ite_true]
    exact coordinatePart_packet input modulus coordinate c i hi r u v
  · simp only [Fin.val_succ, zeroRow_word, Nat.add_one_ne_zero, ite_false]
    exact gradientPart_packet input modulus c i r u v j

lemma value_invalid (hn : ¬coordinate c < dimension (input c)) (j : ℕ) :
    value input modulus coordinate (word c j r u v) = [] := by
  have hv : ¬valid input coordinate (word c j r u v) := by
    intro h
    apply hn
    simpa only [context_word] using h.1
  unfold CoerciveHomogeneousRowReader.value
  rw [ite_eq_right hv]

end LeanCanny.ETR.CoerciveHomogeneousReaderCorrect
