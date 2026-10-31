/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CommonDenominatorIndexed
public import LeanCanny.Algebra.CommonDenominatorCoordinateSpace
public import LeanCanny.Algebra.FixedWidthRationalSubstitutionSpace
public import LeanCanny.Algebra.FixedWidthKronecker
public import LeanCanny.Algebra.FixedWidthRowArithmetic

/-! # Native coefficients of multivariate common-denominator clearing

Fixed-width Kronecker substitution transfers the existing streamed integer
substitution reader to multivariate output. Every source and numerator
coefficient program remains charged. A common integer denominator uses only
multiplication and powers, including for noninvertible modular residues.
-/

@[expose] public section
namespace LeanCanny.Algebra.FixedWidthCommonDenominatorBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Family where
  sourceArity : List Bool → ℕ
  sourceWidth : List Bool → ℕ
  targetArity : List Bool → ℕ
  targetWidth : List Bool → ℕ
  source : (c : List Bool) → MvPolynomial (Fin (sourceArity c)) ℤ
  denominator : List Bool → ℤ
  numerator : (c : List Bool) → ℕ → MvPolynomial (Fin (targetArity c)) ℤ
  source_fit : ∀ c i, (source c).degreeOf i < 2 ^ sourceWidth c

def Family.allowance (F : Family) (c : List Bool) : ℕ := F.sourceArity c * (2 * 2 ^ F.sourceWidth c)

theorem Family.allowance_binary (F : Family) (hA : UnaryFn F.sourceArity) (hW : UnaryFn F.sourceWidth) :
    BinaryFn F.allowance :=
  (BinaryFn.ofUnary hA).mul ((BinaryFn.const 2).mul ((BinaryFn.const 2).powUnary hW))

noncomputable def Family.polynomial (F : Family) (c : List Bool) : MvPolynomial (Fin (F.targetArity c)) ℤ :=
  CommonDenominatorSpecialization.clear (F.allowance c) (F.denominator c)
    (fun i : Fin (F.sourceArity c) => F.numerator c i.val) (F.source c)

theorem Family.support_fit (F : Family) (D E : List Bool → ℕ)
    (hsource : ∀ c, (F.source c).totalDegree ≤ D c)
    (hnum : ∀ c i, (F.numerator c i).totalDegree ≤ E c)
    (hwidth : ∀ c, D c * E c < 2 ^ F.targetWidth c) :
    ∀ c, ∀ e ∈ (F.polynomial c).support, ∀ i, e i < 2 ^ F.targetWidth c := by
  intro c e he i
  have HP := CommonDenominatorSpecialization.degree_mul (F.allowance c) (F.denominator c)
    (fun i : Fin (F.sourceArity c) => F.numerator c i.val) (E c) (fun i => hnum c i.val) (F.source c)
  exact ((MvPolynomial.monomial_le_degreeOf i he).trans (MvPolynomial.degreeOf_le_totalDegree _ i)).trans_lt
    ((HP.trans (Nat.mul_le_mul_right (E c) (hsource c))).trans_lt (hwidth c))

noncomputable def Family.univariate (F : Family) : FixedWidthRationalSubstitutionBits.Family where
  arity := F.sourceArity
  width := F.sourceWidth
  source := F.source
  numerator c i := FixedWidthKronecker.encode (F.targetArity c) (F.targetWidth c) (F.numerator c i)
  denominator c _ := Polynomial.C (F.denominator c)
  degree_fit := F.source_fit

noncomputable def access (F : Family) (hA : UnaryFn F.sourceArity) (hW : UnaryFn F.sourceWidth)
    (source num scalar : List Bool → List Bool) (S : SpaceFunction source) (N : SpaceFunction num) (Q : SpaceFunction scalar)
    (hs : ∀ c r, r < F.univariate.terms c → ∀ m, 0 < m →
      source (pair (pair c (BinaryNatCode.encode r)) (BinaryNatCode.encode (m - 1))) =
        residueBits ((F.univariate.coefficient c r : ℤ) : ZMod m))
    (hn : ∀ c i, i < F.sourceArity c → ∀ k m, 0 < m →
      num (pair (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) (BinaryNatCode.encode (m - 1))) =
        residueBits (((F.univariate.numerator c i).coeff k : ℤ) : ZMod m))
    (hq : ∀ c m, 0 < m → scalar (pair c (BinaryNatCode.encode (m - 1))) =
      residueBits ((F.denominator c : ℤ) : ZMod m)) :
    FixedWidthRationalSubstitutionBits.Access F.univariate where
  arity := hA
  width := hW
  coefficient := source
  evaluator := S
  coefficient_eq := hs
  coordinates := CommonDenominatorCoordinateBits.readers F.sourceArity F.univariate.numerator F.denominator num scalar N Q hn hq

theorem Family.encoded (F : Family) (c : List Bool) :
    FixedWidthKronecker.encode (F.targetArity c) (F.targetWidth c) (F.polynomial c) = F.univariate.polynomial c := by
  rw [← FixedWidthRationalSubstitutionBits.Family.polynomial_eq]
  have H := CommonDenominatorSpecialization.indexed (F.sourceArity c)
    (F.univariate.terms c) (2 * 2 ^ F.sourceWidth c) (F.denominator c) (F.univariate.coefficient c)
    (entry (F.sourceWidth c)) (fun i : Fin (F.sourceArity c) => F.numerator c i.val)
    (FixedWidthKronecker.encode (F.targetArity c) (F.targetWidth c))
    (by intro a; simp [FixedWidthKronecker.encode])
    (fun i => F.univariate.numerator c i) (fun _ => rfl)
    (fun _ _ i _ => (entry_lt (F.sourceWidth c) _ i).le.trans (by omega))
  have HS := FixedWidthRationalSubstitutionBits.Family.source_eq F.univariate c
  change RationalSubstitution.Indexed.source (F.sourceArity c) (F.univariate.terms c)
    (F.univariate.coefficient c) (entry (F.sourceWidth c)) = F.source c at HS
  rw [HS] at H
  exact H

def prepared (F : Family) (target modulus : List Bool → List Bool) (c : List Bool) : List Bool :=
  pair (pair c (BinaryNat.normalize (FixedWidthQuery.repack F.targetArity F.targetWidth F.targetArity F.targetWidth target c)))
    (modulus c)

theorem prepared_FP (F : Family) (target modulus : List Bool → List Bool)
    (hA : UnaryFn F.targetArity) (hW : UnaryFn F.targetWidth) (ht : target ∈ FP) (hm : modulus ∈ FP) :
    prepared F target modulus ∈ FP :=
  mem_FP_pair (mem_FP_pair id_mem_FP (mem_FP_comp (FixedWidthQuery.repack_mem_FP hA hW hA hW ht)
    BinaryNat.normalize_mem_FP)) hm

theorem primitive_packet (p : List Bool → Polynomial ℤ) (c degree modulus : List Bool) :
    PrimitivePairBits.coefficient p (pair (pair c degree) modulus) =
      residueBits (((p c).coeff (Nat.fromBitsLE degree) : ℤ) : ZMod (Nat.fromBitsLE modulus + 1)) := by
  generalize hz : pair (pair c degree) modulus = z
  have HC : RationalSubstitution.IntegerBits.context z = c := by
    rw [← hz, RationalSubstitution.IntegerBits.context, pairFst_pair, pairFst_pair]
  have HD : RationalSubstitution.IntegerBits.selectedDegree z = degree := by
    rw [← hz, RationalSubstitution.IntegerBits.selectedDegree, pairFst_pair, pairSnd_pair]
  have HM : pairSnd z = modulus := by rw [← hz, pairSnd_pair]
  subst c
  subst degree
  subst modulus
  rfl

theorem coefficient_packet (F : Family) (target modulus : List Bool → List Bool)
    (hfit : ∀ c, ∀ e ∈ (F.polynomial c).support, ∀ i, e i < 2 ^ F.targetWidth c) (c : List Bool) :
    PrimitivePairBits.coefficient F.univariate.polynomial (prepared F target modulus c) =
      FixedWidthRowBits.value F.targetArity F.targetWidth F.polynomial target modulus c := by
  let word := FixedWidthQuery.repack F.targetArity F.targetWidth F.targetArity F.targetWidth target c
  let rank := Nat.fromBitsLE word
  have HR : rank < count (F.targetArity c) (F.targetWidth c) := by
    have H := Nat.fromBitsLE_lt_pow_length word
    rw [FixedWidthQuery.repack_length] at H
    simpa only [count, ← pow_mul, Nat.mul_comm (F.targetWidth c)] using H
  have HV : vector (F.targetArity c) (F.targetWidth c) ⟨rank, HR⟩ =
      nativeExponent (Equiv.refl _) (F.targetWidth c) (Nat.fromBitsLE (target c)) := by
    calc
      _ = nativeExponent (Equiv.refl _) (F.targetWidth c) rank :=
        ((nativeExponent_refl _ _ _).trans (entry_vector _ _ ⟨rank, HR⟩)).symm
      _ = _ := nativeExponent_repack (Equiv.refl _) F.targetWidth F.targetWidth target c le_rfl
  have HC := FixedWidthKronecker.coefficient (F.targetArity c) (F.targetWidth c) (F.polynomial c) (hfit c) ⟨rank, HR⟩
  rw [F.encoded c, HV] at HC
  rw [prepared, primitive_packet, BinaryNat.normalize_eq_bits, Nat.fromBitsLE_bits]
  exact congrArg (fun a : ℤ => residueBits (a : ZMod (Nat.fromBitsLE (modulus c) + 1))) HC

theorem evaluator (F : Family) (A : FixedWidthRationalSubstitutionBits.Access F.univariate)
    (target modulus : List Bool → List Bool) (hA : UnaryFn F.targetArity) (hW : UnaryFn F.targetWidth)
    (ht : target ∈ FP) (hm : modulus ∈ FP)
    (hfit : ∀ c, ∀ e ∈ (F.polynomial c).support, ∀ i, e i < 2 ^ F.targetWidth c) :
    SpaceFunction (FixedWidthRowBits.value F.targetArity F.targetWidth F.polynomial target modulus) := by
  exact (A.polynomialEvaluator.precompose _ (prepared_FP F target modulus hA hW ht hm)).congr
    (funext fun c => coefficient_packet F target modulus hfit c)

end LeanCanny.Algebra.FixedWidthCommonDenominatorBits
