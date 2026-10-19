/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ShiftCoefficientFP
public import LeanCanny.Algebra.ShiftCoefficients

/-!
# Certified evaluation of shifted-polynomial coefficient residues

The composed routine returns the coefficient of `x^i θ^j` in `p(θ-c*x)` modulo
a positive binary modulus. Only the original coefficient routine and direction
writer require FP certificates. The binomial factor runs through its certified
space evaluator, with the original query retained and included in the bound.
-/

@[expose] public section

namespace LeanCanny.Algebra.ShiftCoefficientBits
open Complexity
open LeanCanny.Encoding
open LeanCanny.Computation
open LeanCanny.Encoding.Brackets
open MatrixPower

def iValue (p : List Bool) : ℕ := Nat.fromBitsLE (leftIndex p)
def jValue (p : List Bool) : ℕ := Nat.fromBitsLE (rightIndex p)
def mValue (p : List Bool) : ℕ := Nat.fromBitsLE (modulusMinusOne p) + 1

theorem code_value (k : ℕ) : Nat.fromBitsLE (BinaryNatCode.encode k) = k := Nat.fromBitsLE_bits k

theorem modulus_code (p : List Bool) : modulus p = BinaryNatCode.encode (mValue p) := by
  simp only [modulus, mValue, BinaryNat.succ_eq_bits, BinaryNatCode.encode]

theorem sumIndex_code (p : List Bool) : sumIndex p = BinaryNatCode.encode (iValue p + jValue p) := by
  simp only [sumIndex, BinaryNat.add_pair, iValue, jValue, BinaryNatCode.encode]

theorem negativeDirection_correct (a : Access) (p : List Bool) (c : ℕ)
    (hd : a.direction (original p) = BinaryNatCode.encode c) :
    negativeDirection a p = residueBits (-(c : ZMod (mValue p))) := by
  let : NeZero (mValue p) := ⟨by simp only [mValue]; omega⟩
  rw [negativeDirection, modulus_code, hd]
  exact ArithmeticBits.negate_nat (mValue p) c

theorem power_correct (a : Access) (p : List Bool) (c : ℕ)
    (hd : a.direction (original p) = BinaryNatCode.encode c) :
    BinaryNat.powMod (powerInput a p) = residueBits ((-(c : ZMod (mValue p))) ^ iValue p) := by
  rw [powerInput, negativeDirection_correct a p c hd]
  exact ArithmeticBits.powMod_residueBits (modulusMinusOne p) (leftIndex p) (-(c : ZMod (mValue p)))

theorem binomial_correct (p : List Bool) : BinomialResidue.value (binomialInput p) =
    residueBits (((iValue p + jValue p).choose (iValue p) : ℕ) : ZMod (mValue p)) := by
  have hn (n : ℕ) : residueBits (n : ZMod (mValue p)) = BinaryNatCode.encode (n % mValue p) := by
    simp only [residueBits, ZMod.val_natCast]
  rw [hn]
  simp only [BinomialResidue.value, binomialInput, BinomialResidue.nWord, BinomialResidue.kWord,
    BinomialResidue.mWord, pairFst_pair, pairSnd_pair, sumIndex_code, code_value, iValue, mValue]

theorem factor_correct (a : Access) (p : List Bool) (f : Polynomial ℤ) (c : ℕ)
    (hd : a.direction (original p) = BinaryNatCode.encode c)
    (hc : ∀ k, a.coefficient (pair (pairFst p) (BinaryNatCode.encode k)) =
      residueBits ((f.coeff k : ℤ) : ZMod (mValue p))) :
    factor a p = residueBits (((f.coeff (iValue p + jValue p) : ℤ) : ZMod (mValue p)) *
      (-(c : ZMod (mValue p))) ^ iValue p) := by
  have hread : a.coefficient (coefficientInput p) =
      residueBits ((f.coeff (iValue p + jValue p) : ℤ) : ZMod (mValue p)) := by
    rw [coefficientInput, sumIndex_code]
    exact hc _
  rw [factor, modulus_code, hread, power_correct a p c hd, ArithmeticBits.mulMod_residueBits]

theorem computed_correct (a : Access) (p : List Bool) (f : Polynomial ℤ) (c : ℕ)
    (hd : a.direction (original p) = BinaryNatCode.encode c)
    (hc : ∀ k, a.coefficient (pair (pairFst p) (BinaryNatCode.encode k)) =
      residueBits ((f.coeff k : ℤ) : ZMod (mValue p))) :
    computed a p = residueBits
      ((((shiftFamily f c).coeff (iValue p)).coeff (jValue p) : ℤ) : ZMod (mValue p)) := by
  rw [computed, finish, pairFst_pair, pairSnd_pair, modulus_code, binomial_correct,
    factor_correct a p f c hd hc, ArithmeticBits.mulMod_residueBits, shiftFamily_coeff_coeff]
  simp only [Int.cast_mul, Int.cast_natCast, Int.cast_pow, Int.cast_neg, mul_assoc]

structure Family where
  polynomial : List Bool → Polynomial ℤ
  direction : List Bool → ℕ

noncomputable def Family.value (F : Family) (p : List Bool) : List Bool :=
  residueBits (((((shiftFamily (F.polynomial (original p)) (F.direction (original p))).coeff (iValue p)).coeff
    (jValue p) : ℤ) : ZMod (mValue p)))

structure Represents (a : Access) (F : Family) : Prop where
  direction : ∀ c, a.direction c = BinaryNatCode.encode (F.direction c)
  coefficient : ∀ q k, a.coefficient (pair q (BinaryNatCode.encode k)) =
    residueBits (((F.polynomial (pairFst q)).coeff k : ℤ) : ZMod (Nat.fromBitsLE (pairSnd q) + 1))

noncomputable def certified (a : Access) (ha : a.PolyTime) (F : Family) (h : Represents a F) :
    SpaceFunction F.value := by
  have heq : computed a = F.value := by
    funext p
    exact computed_correct a p (F.polynomial (original p)) (F.direction (original p)) (h.direction _)
      (by
        intro k
        change a.coefficient (pair (pairFst p) (BinaryNatCode.encode k)) =
          residueBits (((F.polynomial (pairFst (pairFst p))).coeff k : ℤ) :
            ZMod (Nat.fromBitsLE (pairSnd (pairFst p)) + 1))
        exact h.coefficient (pairFst p) k)
  rw [← heq]
  exact evaluator a ha

def Family.zeroLanguage (F : Family) : Language :=
  {p | ((((shiftFamily (F.polynomial (original p)) (F.direction (original p))).coeff (iValue p)).coeff
    (jValue p) : ℤ) : ZMod (mValue p)) = 0}

theorem zeroLanguage_mem_PSPACE (a : Access) (ha : a.PolyTime) (F : Family) (h : Represents a F) :
    F.zeroLanguage ∈ PSPACE := by
  let accept := fun bits : List Bool => decide (bits = [])
  have hacc : (fun bits => [accept bits]) ∈ FP :=
    (stringEq_fppred id_mem_FP (constFn_mem_FP [])).flag_mem_FP
  apply ((certified a ha F h).decider accept hacc ?_).mem_PSPACE
  intro p
  let : NeZero (mValue p) := ⟨by simp only [mValue]; omega⟩
  have hz : residueBits (0 : ZMod (mValue p)) = [] := by simp [residueBits, BinaryNatCode.encode]
  change _ ↔ decide (F.value p = []) = true
  rw [decide_eq_true_eq, Family.value, ← hz, (residueBits_injective (mValue p)).eq_iff]
  rfl

end LeanCanny.Algebra.ShiftCoefficientBits
