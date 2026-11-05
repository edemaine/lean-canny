/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.PolynomialFamilyProductSpace
public import LeanCanny.Algebra.BivariateProductSpace
/-! # Native binary powers of the identity-padding factor

The exponent stays binary. The product evaluator streams the constant factor
`1-X`; it never stores its binomial expansion or divides by a residue.
-/
@[expose] public section
namespace LeanCanny.Algebra.PaddedCharacteristicFactorBits
open Polynomial LeanCanny.Encoding LeanCanny.Computation MatrixPower
open RationalSubstitution.IntegerBits (context selectedDegree mValue)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ArithmeticBits.one ArithmeticBits.negate BinaryNat.succ

def baseValue (q : List Bool) : List Bool :=
  if Nat.fromBitsLE (selectedDegree q) = 0 then ArithmeticBits.one (BinaryNat.succ (pairSnd q))
  else if Nat.fromBitsLE (selectedDegree q) = 1 then ArithmeticBits.negate
    (pair (BinaryNat.succ (pairSnd q)) (ArithmeticBits.one (BinaryNat.succ (pairSnd q)))) else []

theorem baseValue_FP : baseValue ∈ FP := by
  have HK := BinaryFn.fromBits RationalSubstitution.IntegerBits.selectedDegree_mem_FP
  have HM := mem_FP_comp pairSnd_mem_FP BinaryNat.succ_mem_FP
  have HO := mem_FP_comp HM ArithmeticBits.one_mem_FP
  have HN := mem_FP_comp (mem_FP_pair HM HO) ArithmeticBits.negate_mem_FP
  have H := (HK.eq (BinaryFn.const 0)).ite_mem_FP HO
    ((HK.eq (BinaryFn.const 1)).ite_mem_FP HN (constFn_mem_FP []))
  exact mem_FP_of_eq H (fun _ => rfl)

theorem baseValue_eq (q : List Bool) :
    baseValue q = PrimitivePairBits.coefficient (fun _ => (1 - X : Polynomial ℤ)) q := by
  change baseValue q = residueBits ((((1 - X : Polynomial ℤ).coeff
    (Nat.fromBitsLE (selectedDegree q))) : ℤ) : ZMod (Nat.fromBitsLE (pairSnd q) + 1))
  unfold baseValue
  split_ifs with H0 H1
  · rw [H0]
    simp only [Polynomial.coeff_sub, Polynomial.coeff_one_zero, Polynomial.coeff_X_zero,
      sub_zero, Int.cast_one, BinaryNat.succ_eq_bits]
    exact ArithmeticBits.one_residueBits _
  · rw [H1]
    simp only [Polynomial.coeff_sub, Polynomial.coeff_one, Nat.one_ne_zero, ite_false, Polynomial.coeff_X_one,
      zero_sub, Int.cast_neg, Int.cast_one, BinaryNat.succ_eq_bits]
    change ArithmeticBits.negate (pair (BinaryNatCode.encode (Nat.fromBitsLE (pairSnd q) + 1))
      (ArithmeticBits.one (BinaryNatCode.encode (Nat.fromBitsLE (pairSnd q) + 1)))) =
        residueBits (-1 : ZMod (Nat.fromBitsLE (pairSnd q) + 1))
    rw [ArithmeticBits.one_residueBits, ArithmeticBits.negate_residueBits]
  · rw [Polynomial.coeff_sub, Polynomial.coeff_one, ite_eq_right H0,
      Polynomial.coeff_X, ite_eq_right (Ne.symm H1), sub_self, Int.cast_zero]
    rfl

theorem evaluator (r : List Bool → ℕ) (hr : BinaryFn r) :
    SpaceFunction (PrimitivePairBits.coefficient (fun c => (1 - X : Polynomial ℤ) ^ r c)) := by
  have E : SpaceFunction (PrimitivePairBits.coefficient (fun _ => (1 - X : Polynomial ℤ))) :=
    (SpaceFunction.ofFP _ baseValue_FP).congr (funext baseValue_eq)
  have H := PolynomialFamilyProductBits.evaluator (fun _ => (1 - X : Polynomial ℤ)) r hr E
  have HP : PolynomialFamilyProductBits.polynomial (fun _ => (1 - X : Polynomial ℤ)) r =
      (fun c => (1 - X : Polynomial ℤ) ^ r c) := by
    funext c
    simp only [PolynomialFamilyProductBits.polynomial, Finset.prod_const, Finset.card_range]
  rw [HP] at H
  exact H

def query (q : List Bool) : List Bool := pair
  (pair (pairFst (pairFst q)) (pairSnd (pairSnd q))) (pairSnd (pairFst q))
theorem query_FP : query ∈ FP := by polytime [query]

noncomputable def value (r : List Bool → ℕ) (q : List Bool) : List Bool :=
  if Nat.fromBitsLE (pairFst (pairSnd q)) = 0 then
    PrimitivePairBits.coefficient (fun c => (1 - X : Polynomial ℤ) ^ r c) (query q) else []

theorem value_evaluator (r : List Bool → ℕ) (hr : BinaryFn r) : SpaceFunction (value r) := by
  have HI := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
  have E := SpaceFunction.branch (fun q => decide (Nat.fromBitsLE (pairFst (pairSnd q)) = 0))
    (HI.eq (BinaryFn.const 0)).flag_mem_FP ((evaluator r hr).precompose query query_FP)
    (SpaceFunction.ofFP _ (constFn_mem_FP []))
  exact E.congr (funext fun q => by simp only [value, decide_eq_true_eq, Function.comp_apply])

noncomputable def reader (r : List Bool → ℕ) (hr : BinaryFn r) :
    CertifiedPolynomial.BivariateReader (fun c => (1 - X : Polynomial (Polynomial ℤ)) ^ r c) where
  coefficient := value r
  evaluator := value_evaluator r hr
  coefficient_eq q u v := by
    have HM : (1 - X : Polynomial (Polynomial ℤ)) ^ r (pairFst q) =
        ((1 - X : Polynomial ℤ) ^ r (pairFst q)).map Polynomial.C := by simp
    rw [HM, Polynomial.coeff_map, Polynomial.coeff_C]
    simp only [value, query, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
      PrimitivePairBits.coefficient, context, selectedDegree, mValue]
    by_cases HU : u = 0
    · simp only [HU, ite_true]
      rfl
    · simp only [HU, ite_false, Int.cast_zero]
      rfl

end LeanCanny.Algebra.PaddedCharacteristicFactorBits
