/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMonomialTermSpace
public import LeanCanny.Algebra.ClearedCoordinateExponentControl
public import LeanCanny.Algebra.FixedWidthCoordinateBinary

/-! # Original coefficient sources for integral frozen-coordinate clearing

The original spatial polynomial and retained heights take values in the
actual old parameter algebra. Source and target exponent words describe
spatial coordinates only. The old algebra rank is a separate binary field.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralClearedCoefficientBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false
universe u

structure Source where
  arity : List Bool → ℕ
  free : List Bool → ℕ
  offset : List Bool → ℕ
  fit : ∀ c, offset c + free c ≤ arity c
  sourceWidth : List Bool → ℕ
  targetWidth : List Bool → ℕ
  rank : List Bool → ℕ
  carrier : List Bool → Type u
  ring : ∀ c, CommRing (carrier c)
  basis : ∀ c, @Module.Basis (Fin (rank c)) ℤ (carrier c) _ _ ((ring c).toIntAlgebra.toModule)
  polynomial : ∀ c, MvPolynomial (Fin (arity c)) (carrier c)
  support : ∀ c, letI := ring c
    ∀ e ∈ (polynomial c).support, ∀ i, e i < 2 ^ sourceWidth c
  denominator : List Bool → ℤ
  height : ∀ c, ℕ → carrier c
  allowance : List Bool → ℕ
  target : List Bool → ℕ
  row : ∀ c, Fin (rank c)
  col : ∀ c, Fin (rank c)
  modulus : List Bool → ℕ
  modulus_ne_zero : ∀ c, modulus c ≠ 0

def context (c : List Bool) (r t : ℕ) : List Bool := pair c (pair (BinaryNatCode.encode r) (BinaryNatCode.encode t))

structure Access (S : Source) where
  arity : UnaryFn S.arity
  free : UnaryFn S.free
  offset : UnaryFn S.offset
  sourceWidth : UnaryFn S.sourceWidth
  targetWidth : UnaryFn S.targetWidth
  rank : BinaryFn S.rank
  allowance : BinaryFn S.allowance
  target : BinaryFn S.target
  row : BinaryFn (fun c => (S.row c).val)
  col : BinaryFn (fun c => (S.col c).val)
  modulus : BinaryFn S.modulus
  coefficient : List Bool → List Bool
  height : List Bool → List Bool
  denominator : List Bool → List Bool
  coefficient_eq : ∀ c k (r t : Fin (S.rank c)),
    letI := S.ring c
    coefficient (pair (context c r.val t.val) (BinaryNatCode.encode k)) = residueBits
      ((Algebra.leftMulMatrix (S.basis c) ((S.polynomial c).coeff
        (RationalSubstitution.Indexed.exponentVector (S.arity c) (FixedWidthPolynomial.entry (S.sourceWidth c) k))) r t : ℤ) : ZMod (S.modulus c))
  height_eq : ∀ c i (r t : Fin (S.rank c)),
    letI := S.ring c
    height (pair c (pair (BinaryNatCode.encode i) (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))) =
      residueBits ((Algebra.leftMulMatrix (S.basis c) (S.height c i) r t : ℤ) : ZMod (S.modulus c))
  denominator_eq : ∀ c, denominator c = residueBits (S.denominator c : ZMod (S.modulus c))

noncomputable def termSource (S : Source) : IntegralMonomialTermBits.Source where
  arity p := S.arity (pairFst p)
  rank p := S.rank (pairFst p)
  carrier p := S.carrier (pairFst p)
  ring p := S.ring (pairFst p)
  basis p := S.basis (pairFst p)
  coefficient p := by
    letI := S.ring (pairFst p)
    exact (S.polynomial (pairFst p)).coeff (RationalSubstitution.Indexed.exponentVector (S.arity (pairFst p))
      (FixedWidthPolynomial.entry (S.sourceWidth (pairFst p)) (Nat.fromBitsLE (pairSnd p))))
  denominator p := S.denominator (pairFst p)
  height p := S.height (pairFst p)
  exponent p := FixedWidthQuery.entry (fun z => S.arity (pairFst z)) (fun z => S.sourceWidth (pairFst z)) pairSnd p
  allowance p := S.allowance (pairFst p)
  offset p := S.offset (pairFst p)
  free p := S.free (pairFst p)
  row p := S.row (pairFst p)
  col p := S.col (pairFst p)
  modulus p := S.modulus (pairFst p)
  modulus_ne_zero p := S.modulus_ne_zero (pairFst p)

def coefficientQuery (q : List Bool) : List Bool :=
  pair (pair (pairFst (pairFst q)) (pairSnd q)) (BinaryNat.normalize (pairSnd (pairFst q)))

def heightQuery (q : List Bool) : List Bool := pair (pairFst (pairFst q)) (pairSnd q)

theorem coefficientQuery_FP : coefficientQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP)
    (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) BinaryNat.normalize_mem_FP)
theorem heightQuery_FP : heightQuery ∈ FP := mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP

theorem coefficientQuery_packet (p : List Bool) (r t : ℕ) :
    coefficientQuery (pair p (pair (BinaryNatCode.encode r) (BinaryNatCode.encode t))) =
      pair (context (pairFst p) r t) (BinaryNatCode.encode (Nat.fromBitsLE (pairSnd p))) := by
  simp only [coefficientQuery, context, pairFst_pair, pairSnd_pair, BinaryNat.normalize_eq_bits, BinaryNatCode.encode]

theorem heightQuery_packet (p : List Bool) (i r t : ℕ) :
    heightQuery (pair p (pair (BinaryNatCode.encode i) (pair (BinaryNatCode.encode r) (BinaryNatCode.encode t)))) =
      pair (pairFst p) (pair (BinaryNatCode.encode i) (pair (BinaryNatCode.encode r) (BinaryNatCode.encode t))) := by
  simp only [heightQuery, pairFst_pair, pairSnd_pair]

noncomputable def termAccess (S : Source) (a : Access S) : IntegralMonomialTermBits.Access (termSource S) where
  arity := a.arity.comp pairFst_mem_FP
  rank := a.rank.comp pairFst_mem_FP
  modulus := a.modulus.comp pairFst_mem_FP
  row := a.row.comp pairFst_mem_FP
  col := a.col.comp pairFst_mem_FP
  allowance := a.allowance.comp pairFst_mem_FP
  offset := (BinaryFn.ofUnary a.offset).comp pairFst_mem_FP
  free := (BinaryFn.ofUnary a.free).comp pairFst_mem_FP
  exponent := FixedWidthQuery.entry_binary _ _ pairSnd (a.arity.comp pairFst_mem_FP) (a.sourceWidth.comp pairFst_mem_FP) pairSnd_mem_FP
  coefficient := a.coefficient ∘ coefficientQuery
  height := a.height ∘ heightQuery
  denominator := a.denominator ∘ pairFst
  coefficient_eq p r t := by
    rw [Function.comp_apply, coefficientQuery_packet]
    exact a.coefficient_eq (pairFst p) (Nat.fromBitsLE (pairSnd p)) r t
  height_eq p i r t := by
    rw [Function.comp_apply, heightQuery_packet]
    exact a.height_eq (pairFst p) i r t
  denominator_eq p := a.denominator_eq (pairFst p)

theorem term_evaluator (S : Source) (a : Access S) (EC : SpaceFunction a.coefficient)
    (EH : SpaceFunction a.height) (EQ : SpaceFunction a.denominator) : SpaceFunction (termSource S).value :=
  IntegralMonomialTermBits.evaluator (termSource S) (termAccess S a)
    (EC.precompose coefficientQuery coefficientQuery_FP) (EH.precompose heightQuery heightQuery_FP)
    (EQ.precompose pairFst pairFst_mem_FP)

end LeanCanny.Algebra.IntegralClearedCoefficientBits
