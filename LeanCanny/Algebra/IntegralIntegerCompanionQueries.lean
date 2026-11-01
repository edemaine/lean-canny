/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralIntegerCompanionSource
/-! # Charged integer coefficient and leading queries for companion leaves -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralIntegerCompanionBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
universe u

def scalarQuery (F : PaddedIntegralGeneratorFinBits.Family.{u}) (z : List Bool) : List Bool :=
  pair (pair (pairFst z) (IntegralPowerProductBits.factorWord z)) (BinaryNatCode.encode (F.modulus (pairFst z) - 1))

def sameIndex (z : List Bool) : Prop :=
  Nat.fromBitsLE (IntegralPowerProductBits.rowWord z) = Nat.fromBitsLE (IntegralPowerProductBits.colWord z)
instance (z : List Bool) : Decidable (sameIndex z) := inferInstanceAs (Decidable (_ = _))

noncomputable def entry (F : PaddedIntegralGeneratorFinBits.Family.{u}) (p : List Bool → Polynomial ℤ) (z : List Bool) : List Bool :=
  if sameIndex z then PrimitivePairBits.coefficient p (scalarQuery F z) else []

theorem scalarQuery_FP (F : PaddedIntegralGeneratorFinBits.Family.{u}) (a : Controls F) : scalarQuery F ∈ FP := by
  have HM : BinaryFn (fun z => F.modulus (pairFst z)) := a.modulus.comp pairFst_mem_FP
  exact mem_FP_pair (mem_FP_pair pairFst_mem_FP IntegralPowerProductBits.factorWord_FP)
    (HM.sub (BinaryFn.const 1)).bits_mem_FP

theorem sameIndex_FP : FPPred sameIndex :=
  (BinaryFn.fromBits IntegralPowerProductBits.rowWord_FP).eq (BinaryFn.fromBits IntegralPowerProductBits.colWord_FP)

theorem entry_evaluator (F : PaddedIntegralGeneratorFinBits.Family.{u}) (p : List Bool → Polynomial ℤ)
    (a : Controls F) (EC : SpaceFunction (PrimitivePairBits.coefficient p)) : SpaceFunction (entry F p) :=
  (SpaceFunction.branch (fun z => decide (sameIndex z)) sameIndex_FP.flag_mem_FP
    (EC.precompose (scalarQuery F) (scalarQuery_FP F a)) (SpaceFunction.ofFP _ (constFn_mem_FP []))).congr
      (funext fun z => by simp only [entry, decide_eq_true_eq, Function.comp_apply])

theorem entry_packet (F : PaddedIntegralGeneratorFinBits.Family.{u}) (p : List Bool → Polynomial ℤ)
    (hp : ∀ q, letI := F.ring q; F.polynomial q = (p q).map (Int.castRingHom (F.carrier q)))
    (q : List Bool) (k : ℕ) (r t : Fin (count (F.arity q) (F.width q))) :
    entry F p (pair q (pair (BinaryNatCode.encode k) (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))) =
      residueBits (F.coefficient q k r t) := by
  rw [coefficient_eq F p hp]
  unfold entry scalarQuery sameIndex
  simp only [IntegralPowerProductBits.factorWord, IntegralPowerProductBits.rowWord, IntegralPowerProductBits.colWord,
    pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  have HM : 0 < F.modulus q := Nat.pos_of_ne_zero (F.modulus_ne_zero q)
  have HC := IntegerPolynomialRootQueriesBits.coefficient_packet p q k (F.modulus q) HM
  by_cases h : r = t
  · subst t
    rw [ite_eq_left rfl, ite_eq_left rfl, mul_one]
    exact HC
  · rw [ite_eq_right (fun he => h (Fin.ext he)), ite_eq_right h, mul_zero]
    exact ArithmeticBits.zero_residueBits _

def leadingQuery (F : PaddedIntegralGeneratorFinBits.Family.{u}) (z : List Bool) : List Bool :=
  pair z (BinaryNatCode.encode (F.modulus (pairFst z) - 1))

theorem leadingQuery_FP (F : PaddedIntegralGeneratorFinBits.Family.{u}) (a : Controls F) : leadingQuery F ∈ FP := by
  have HM : BinaryFn (fun z => F.modulus (pairFst z)) := a.modulus.comp pairFst_mem_FP
  exact mem_FP_pair id_mem_FP (HM.sub (BinaryFn.const 1)).bits_mem_FP

noncomputable def leadingReader (F : PaddedIntegralGeneratorFinBits.Family.{u}) (p : List Bool → Polynomial ℤ)
    (degree : List Bool → List Bool) (q : List Bool) : List Bool :=
  PrimitivePairBits.coefficient p (leadingQuery F (pair q (degree q)))

theorem leading_evaluator (F : PaddedIntegralGeneratorFinBits.Family.{u}) (p : List Bool → Polynomial ℤ)
    (a : Controls F) (degree : List Bool → List Bool)
    (ED : SpaceFunction degree) (EC : SpaceFunction (PrimitivePairBits.coefficient p)) : SpaceFunction (leadingReader F p degree) :=
  (ED.withInput.postcompose (leadingQuery F) (leadingQuery_FP F a)).chain EC

theorem leadingReader_eq (F : PaddedIntegralGeneratorFinBits.Family.{u}) (p : List Bool → Polynomial ℤ)
    (hd : ∀ q, F.degree q = (p q).natDegree) (degree : List Bool → List Bool)
    (hdegree : ∀ q, degree q = BinaryNatCode.encode (F.degree q)) (q : List Bool) :
    leadingReader F p degree q = residueBits (leading F p q : ZMod (F.modulus q)) := by
  unfold leadingReader leadingQuery
  rw [hdegree q]
  rw [pairFst_pair, IntegerPolynomialRootQueriesBits.coefficient_packet p q (F.degree q) (F.modulus q)
    (Nat.pos_of_ne_zero (F.modulus_ne_zero q)), hd q, Polynomial.coeff_natDegree]
  rfl
end LeanCanny.Algebra.IntegralIntegerCompanionBits
