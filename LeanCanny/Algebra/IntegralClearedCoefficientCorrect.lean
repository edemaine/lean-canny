/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralClearedCoefficientTerm

/-! # Correctness of the masked original-grid coefficient sum -/

@[expose] public section
namespace LeanCanny.Algebra.IntegralClearedCoefficientBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

noncomputable def Source.targetExponent (S : Source) (c : List Bool) : Fin (S.free c) →₀ ℕ :=
  RationalSubstitution.Indexed.exponentVector (S.free c) (FixedWidthPolynomial.entry (S.targetWidth c) (S.target c))

noncomputable def Source.term (S : Source) (c : List Bool) (i : ℕ) : S.carrier c := by
  letI := S.ring c
  let e := RationalSubstitution.Indexed.exponentVector (S.arity c) (FixedWidthPolynomial.entry (S.sourceWidth c) i)
  exact ClearedCoordinateBlock.monomialScalar (S.allowance c) (S.denominator c : S.carrier c)
    (S.height c) (S.offset c) (S.free c) e ((S.polynomial c).coeff e)

noncomputable def Source.summand (S : Source) (c : List Bool) (i : ℕ) : ℤ := by
  letI := S.ring c
  let e := RationalSubstitution.Indexed.exponentVector (S.arity c) (FixedWidthPolynomial.entry (S.sourceWidth c) i)
  exact Algebra.leftMulMatrix (S.basis c)
    (if ClearedCoordinateBlock.freeExponent (S.offset c) (S.free c) e = S.targetExponent c then S.term c i else 0)
    (S.row c) (S.col c)

noncomputable def Source.value (S : Source) (c : List Bool) : List Bool := by
  letI := S.ring c
  exact residueBits ((Algebra.leftMulMatrix (S.basis c)
    ((ClearedCoordinateBlock.specialize (S.allowance c) (S.denominator c : S.carrier c)
      (S.height c) (S.offset c) (S.free c) (S.polynomial c)).coeff (S.targetExponent c)) (S.row c) (S.col c) : ℤ) : ZMod (S.modulus c))

theorem masked_packet (S : Source) (c : List Bool) (i : ℕ)
    (hi : i < FixedWidthPolynomial.count (S.arity c) (S.sourceWidth c)) :
    maskedProgram S (pair c (BinaryNatCode.encode i)) = residueBits (S.summand c i : ZMod (S.modulus c)) := by
  generalize hz : pair c (BinaryNatCode.encode i) = p
  have ho : pairFst p = c := by rw [← hz, pairFst_pair]
  have hw : pairSnd p = BinaryNatCode.encode i := by rw [← hz, pairSnd_pair]
  subst c
  let := S.ring (pairFst p)
  let r : Fin (FixedWidthPolynomial.count (S.arity (pairFst p)) (S.sourceWidth (pairFst p))) := ⟨i, hi⟩
  have HE : exponentVector S p = FixedWidthPolynomial.vector _ _ r := by
    unfold exponentVector
    rw [hw, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact FixedWidthPolynomial.entry_vector _ _ r
  have HN : RationalSubstitution.Indexed.exponentVector (S.arity (pairFst p))
      (FixedWidthPolynomial.entry (S.sourceWidth (pairFst p)) i) = FixedWidthPolynomial.vector _ _ r :=
    FixedWidthPolynomial.entry_vector _ _ r
  have HG : ClearedCoordinateExponentBits.mask (maskLayout S) p ↔
      ClearedCoordinateBlock.freeExponent (S.offset (pairFst p)) (S.free (pairFst p))
        (FixedWidthPolynomial.vector _ _ r) = S.targetExponent (pairFst p) :=
    ClearedCoordinateExponentBits.mask_eq (maskLayout S) p (S.fit (pairFst p)) r (S.target (pairFst p)) hw rfl
  have HV : (termSource S).value p = residueBits ((Algebra.leftMulMatrix (S.basis (pairFst p))
      (ClearedCoordinateBlock.monomialScalar (S.allowance (pairFst p))
        (S.denominator (pairFst p) : S.carrier (pairFst p)) (S.height (pairFst p)) (S.offset (pairFst p)) (S.free (pairFst p))
        (FixedWidthPolynomial.vector _ _ r) ((S.polynomial (pairFst p)).coeff (FixedWidthPolynomial.vector _ _ r)))
      (S.row (pairFst p)) (S.col (pairFst p)) : ℤ) : ZMod (S.modulus (pairFst p))) := by
    rw [term_value, HE]
  unfold maskedProgram Source.summand Source.term
  dsimp only
  rw [HN]
  by_cases hm : ClearedCoordinateBlock.freeExponent (S.offset (pairFst p)) (S.free (pairFst p))
      (FixedWidthPolynomial.vector _ _ r) = S.targetExponent (pairFst p)
  · rw [ite_eq_left (HG.mpr hm), ite_eq_left hm]
    exact HV
  · rw [ite_eq_right (fun H => hm (HG.mp H)), ite_eq_right hm]
    simp only [map_zero, Matrix.zero_apply, Int.cast_zero, residueBits, ZMod.val_zero,
      BinaryNatCode.encode, Nat.zero_bits]

theorem sum_summands (S : Source) (c : List Bool) :
    letI := S.ring c
    (∑ i ∈ Finset.range (FixedWidthPolynomial.count (S.arity c) (S.sourceWidth c)), S.summand c i) =
      Algebra.leftMulMatrix (S.basis c)
        ((ClearedCoordinateBlock.specialize (S.allowance c) (S.denominator c : S.carrier c)
          (S.height c) (S.offset c) (S.free c) (S.polynomial c)).coeff (S.targetExponent c)) (S.row c) (S.col c) := by
  let := S.ring c
  rw [ClearedCoordinateBlock.specialize_coefficient_grid (S.sourceWidth c) _ _ _ _ _ _ (S.support c),
    map_sum, Matrix.sum_apply, Finset.sum_range]
  apply Finset.sum_congr rfl
  intro r _
  unfold Source.summand Source.term
  rw [FixedWidthPolynomial.entry_vector]

theorem sum_value (S : Source) (c : List Bool) :
    residueBits (∑ i ∈ Finset.range (FixedWidthPolynomial.count (S.arity c) (S.sourceWidth c)),
      (S.summand c i : ZMod (S.modulus c))) = S.value c := by
  let := S.ring c
  rw [← Int.cast_sum, sum_summands]
  rfl

end LeanCanny.Algebra.IntegralClearedCoefficientBits
