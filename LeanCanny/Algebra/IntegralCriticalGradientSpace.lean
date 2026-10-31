/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralClearedCoefficientRequery
public import LeanCanny.Algebra.IntegralDerivativeClearingSpace
public import LeanCanny.Algebra.IntegralFrozenPowerSource

/-! # Native cleared gradients with a selected free spatial coordinate

A query retains the original record and separately carries a free-coordinate
rank and target exponent. The selected original derivative index is offset
plus that free rank. Invalid ranks are clipped before unary arithmetic. All
original polynomial, height, and denominator data retain the saved record.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalGradientBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Source extends toFrozen : IntegralFrozenPowerBits.Source where
  free_pos : ∀ c, 0 < free c
  degree : List Bool → ℕ
  degree_pos : ∀ c, 0 < degree c
  degree_le : ∀ c, letI := ring c
    (polynomial c).totalDegree ≤ degree c
  degree_lt : ∀ c, degree c < 2 ^ sourceWidth c

structure Access (S : Source) extends toFrozen : IntegralFrozenPowerBits.Access S.toFrozen where
  degree : BinaryFn S.degree

def selectedRank (S : Source) (z : List Bool) : ℕ :=
  min (Nat.fromBitsLE (pairFst (pairSnd z))) (S.free (pairFst z) - 1)

theorem selectedRank_lt (S : Source) (z : List Bool) : selectedRank S z < S.free (pairFst z) := by
  have H := S.free_pos (pairFst z)
  have HM := min_le_right (Nat.fromBitsLE (pairFst (pairSnd z))) (S.free (pairFst z) - 1)
  unfold selectedRank
  omega

def selected (S : Source) (z : List Bool) : Fin (S.arity (pairFst z)) :=
  ⟨S.offset (pairFst z) + selectedRank S z, by
    have H := selectedRank_lt S z
    have HF := S.fit (pairFst z)
    omega⟩

def target (z : List Bool) : ℕ := Nat.fromBitsLE (pairSnd (pairSnd z))
theorem target_binary : BinaryFn target :=
  BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)

noncomputable def baseFamily (S : Source) : IntegralClearedCoefficientBits.Source :=
  S.toFrozen.toSource.requery pairFst target (fun z => S.row (pairFst z)) (fun z => S.col (pairFst z))

noncomputable def derivativeFamily (S : Source) : IntegralDerivativeBits.Source where
  __ := baseFamily S
  selected := selected S
  degree z := S.degree (pairFst z)
  degree_pos z := S.degree_pos (pairFst z)
  degree_le z := S.degree_le (pairFst z)
  degree_lt z := S.degree_lt (pairFst z)

noncomputable def baseAccess (S : Source) (a : Access S) : IntegralClearedCoefficientBits.Access (baseFamily S) :=
  a.toFrozen.toAccess.requery S.toFrozen.toSource pairFst target
    (fun z => S.row (pairFst z)) (fun z => S.col (pairFst z)) pairFst_mem_FP target_binary
    (a.row.comp pairFst_mem_FP) (a.col.comp pairFst_mem_FP)

theorem selected_unary (S : Source) (a : Access S) : UnaryFn (fun z => (selected S z).val) := by
  have HF : UnaryFn (fun z => S.free (pairFst z) - 1) := (a.free.comp pairFst_mem_FP).sub (UnaryFn.const 1)
  have HI : UnaryFn (selectedRank S) :=
    UnaryFn.fromBitsLE_min (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) HF
  exact (a.offset.comp pairFst_mem_FP).add HI

noncomputable def derivativeAccess (S : Source) (a : Access S) : IntegralDerivativeBits.Access (derivativeFamily S) where
  __ := baseAccess S a
  selected := selected_unary S a
  degree := a.degree.comp pairFst_mem_FP

noncomputable def family (S : Source) : IntegralClearedCoefficientBits.Source :=
  IntegralDerivativeBits.clearedSource (derivativeFamily S)

theorem evaluator (S : Source) (a : Access S) (EC : SpaceFunction a.coefficient)
    (EH : SpaceFunction a.height) (EQ : SpaceFunction a.denominator) : SpaceFunction (family S).value :=
  IntegralDerivativeBits.cleared_evaluator (derivativeFamily S) (derivativeAccess S a)
    (EC.precompose (IntegralClearedCoefficientBits.coefficientRequery pairFst)
      (IntegralClearedCoefficientBits.coefficientRequery_FP pairFst pairFst_mem_FP))
    (EH.precompose (IntegralClearedCoefficientBits.heightRequery pairFst)
      (IntegralClearedCoefficientBits.heightRequery_FP pairFst pairFst_mem_FP))
    (EQ.precompose pairFst pairFst_mem_FP)

theorem selected_packet (S : Source) (c : List Bool) (j : Fin (S.free c)) (e : ℕ) :
    (selected S (pair c (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode e)))).val = S.offset c + j.val := by
  have H : j.val ≤ S.free c - 1 := by have := j.isLt; omega
  simp only [selected, selectedRank, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    min_eq_left H]


def freeIndex (S : Source) (c : List Bool) (j : Fin (S.free c)) : Fin (S.arity c) :=
  ⟨S.offset c + j.val, by have := S.fit c; have := j.isLt; omega⟩

noncomputable def polynomial (S : Source) (c : List Bool) (j : Fin (S.free c)) :
    letI := S.ring c
    MvPolynomial (Fin (S.free c)) (S.carrier c) := by
  letI := S.ring c
  exact ClearedCoordinateBlock.specialize (S.allowance c) (S.denominator c : S.carrier c)
    (S.height c) (S.offset c) (S.free c) (MvPolynomial.pderiv (freeIndex S c j) (S.polynomial c))

theorem packet (S : Source) (c : List Bool) (j : Fin (S.free c)) (e : ℕ) :
    letI := S.ring c
    (family S).value (pair c (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode e))) =
      residueBits ((Algebra.leftMulMatrix (S.basis c)
        ((polynomial S c j).coeff (RationalSubstitution.Indexed.exponentVector (S.free c)
          (FixedWidthPolynomial.entry (S.targetWidth c) e))) (S.row c) (S.col c) : ℤ) : ZMod (S.modulus c)) := by
  generalize hz : pair c (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode e)) = z
  have HO : pairFst z = c := by rw [← hz, pairFst_pair]
  have HJ : Nat.fromBitsLE (pairFst (pairSnd z)) = j.val := by
    rw [← hz, pairSnd_pair, pairFst_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have HE : Nat.fromBitsLE (pairSnd (pairSnd z)) = e := by
    rw [← hz, pairSnd_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  subst c
  let := S.ring (pairFst z)
  have HI : selected S z = freeIndex S (pairFst z) j := by
    apply Fin.ext
    have H : j.val ≤ S.free (pairFst z) - 1 := by have := j.isLt; omega
    simp only [selected, freeIndex, selectedRank, HJ, min_eq_left H]
  change residueBits ((Algebra.leftMulMatrix (S.basis (pairFst z))
    ((ClearedCoordinateBlock.specialize (S.allowance (pairFst z)) (S.denominator (pairFst z) : S.carrier (pairFst z))
      (S.height (pairFst z)) (S.offset (pairFst z)) (S.free (pairFst z))
      (MvPolynomial.pderiv (selected S z) (S.polynomial (pairFst z)))).coeff
        (RationalSubstitution.Indexed.exponentVector (S.free (pairFst z))
          (FixedWidthPolynomial.entry (S.targetWidth (pairFst z)) (target z))))
      (S.row (pairFst z)) (S.col (pairFst z)) : ℤ) : ZMod (S.modulus (pairFst z))) = _
  rw [HI, show target z = e from HE]
  rfl

end LeanCanny.Algebra.IntegralCriticalGradientBits
