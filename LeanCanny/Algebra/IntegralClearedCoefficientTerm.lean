/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralClearedCoefficientSource

/-! # Actual cleared spatial-monomial values of native term queries -/

@[expose] public section
namespace LeanCanny.Algebra.IntegralClearedCoefficientBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

noncomputable def exponentVector (S : Source) (p : List Bool) : Fin (S.arity (pairFst p)) →₀ ℕ :=
  RationalSubstitution.Indexed.exponentVector (S.arity (pairFst p))
    (FixedWidthPolynomial.entry (S.sourceWidth (pairFst p)) (Nat.fromBitsLE (pairSnd p)))

theorem term_exponent (S : Source) (p : List Bool) (i : ℕ) (hi : i < S.arity (pairFst p)) :
    (termSource S).exponent p i = FixedWidthPolynomial.entry (S.sourceWidth (pairFst p)) (Nat.fromBitsLE (pairSnd p)) i := by
  change FixedWidthQuery.entry (fun z => S.arity (pairFst z)) (fun z => S.sourceWidth (pairFst z)) pairSnd p i = _
  rw [FixedWidthQuery.entry, ite_eq_left hi, FixedWidthQuery.coordinate_eq_entry]

theorem term_degree (S : Source) (p : List Bool) :
    IntegralMonomialTermBits.degree (termSource S) p = (exponentVector S p).degree := by
  change (∑ i ∈ Finset.range (S.arity (pairFst p)), (termSource S).exponent p i) = _
  rw [Finset.sum_range, Finsupp.degree_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact term_exponent S p i.val i.isLt

theorem term_scalar (S : Source) (p : List Bool) :
    letI := S.ring (pairFst p)
    (termSource S).scalar p = ClearedCoordinateBlock.monomialScalar (S.allowance (pairFst p))
      (S.denominator (pairFst p) : S.carrier (pairFst p)) (S.height (pairFst p)) (S.offset (pairFst p)) (S.free (pairFst p))
      (exponentVector S p) ((S.polynomial (pairFst p)).coeff (exponentVector S p)) := by
  let := S.ring (pairFst p)
  change (S.polynomial (pairFst p)).coeff (exponentVector S p) *
    (S.denominator (pairFst p) : S.carrier (pairFst p)) ^ (S.allowance (pairFst p) - IntegralMonomialTermBits.degree (termSource S) p) *
      (∏ i : Fin (S.arity (pairFst p)), ClearedCoordinateBlock.scalarAtom (S.denominator (pairFst p) : S.carrier (pairFst p))
        (S.height (pairFst p)) (S.offset (pairFst p)) (S.free (pairFst p)) i.val ((termSource S).exponent p i.val)) = _
  rw [term_degree]
  unfold ClearedCoordinateBlock.monomialScalar
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [term_exponent S p i.val i.isLt]
  rfl

theorem term_value (S : Source) (p : List Bool) :
    letI := S.ring (pairFst p)
    (termSource S).value p = residueBits ((Algebra.leftMulMatrix (S.basis (pairFst p))
      (ClearedCoordinateBlock.monomialScalar (S.allowance (pairFst p))
        (S.denominator (pairFst p) : S.carrier (pairFst p)) (S.height (pairFst p)) (S.offset (pairFst p)) (S.free (pairFst p))
        (exponentVector S p) ((S.polynomial (pairFst p)).coeff (exponentVector S p)))
      (S.row (pairFst p)) (S.col (pairFst p)) : ℤ) : ZMod (S.modulus (pairFst p))) := by
  let := S.ring (pairFst p)
  have H := congrArg (fun x : S.carrier (pairFst p) => residueBits
    ((Algebra.leftMulMatrix (S.basis (pairFst p)) x (S.row (pairFst p)) (S.col (pairFst p)) : ℤ) : ZMod (S.modulus (pairFst p))))
    (term_scalar S p)
  exact H

def maskLayout (S : Source) : ClearedCoordinateExponentBits.Layout where
  arity p := S.arity (pairFst p)
  free p := S.free (pairFst p)
  offset p := S.offset (pairFst p)
  sourceWidth p := S.sourceWidth (pairFst p)
  targetWidth p := S.targetWidth (pairFst p)
  sourceWord := pairSnd
  targetWord p := BinaryNatCode.encode (S.target (pairFst p))

theorem mask_controls (S : Source) (a : Access S) : ClearedCoordinateExponentBits.Controls (maskLayout S) := by
  have HT : BinaryFn (fun p => S.target (pairFst p)) := a.target.comp pairFst_mem_FP
  exact ⟨a.arity.comp pairFst_mem_FP, a.free.comp pairFst_mem_FP, a.offset.comp pairFst_mem_FP,
    a.sourceWidth.comp pairFst_mem_FP, a.targetWidth.comp pairFst_mem_FP, pairSnd_mem_FP, HT.bits_mem_FP⟩

noncomputable def maskedProgram (S : Source) (p : List Bool) : List Bool :=
  if ClearedCoordinateExponentBits.mask (maskLayout S) p then (termSource S).value p else []

theorem masked_evaluator (S : Source) (a : Access S) (EC : SpaceFunction a.coefficient)
    (EH : SpaceFunction a.height) (EQ : SpaceFunction a.denominator) : SpaceFunction (maskedProgram S) :=
  (SpaceFunction.branch (fun p => decide (ClearedCoordinateExponentBits.mask (maskLayout S) p))
    (ClearedCoordinateExponentBits.mask_fppred (maskLayout S) (mask_controls S a)).flag_mem_FP
    (term_evaluator S a EC EH EQ) (SpaceFunction.ofFP _ (constFn_mem_FP []))).congr
      (funext fun _ => by simp only [maskedProgram, decide_eq_true_eq])

end LeanCanny.Algebra.IntegralClearedCoefficientBits
