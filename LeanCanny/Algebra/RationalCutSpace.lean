/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegerTarskiSeedSpace
public import LeanCanny.Algebra.ModularAddFP
public import LeanCanny.Algebra.CoefficientMass

/-! # Native linear sign queries at rational cuts

Contexts have shape `pair source (pair positive (pair negative denominatorMinusOne))`.
The threshold is `(positive - negative) / denominator`. Every bitstring has a
positive denominator, and neither signed numerators nor unary magnitudes need
to be serialized.
-/

@[expose] public section
namespace LeanCanny.Algebra.RationalCutBits
open LeanCanny.Encoding LeanCanny.Computation Brackets MatrixPower
open scoped Classical

def positive (c : List Bool) : List Bool := pairFst (pairSnd c)
def negative (c : List Bool) : List Bool := pairFst (pairSnd (pairSnd c))
def denominatorMinusOne (c : List Bool) : List Bool := pairSnd (pairSnd (pairSnd c))
def denominator (c : List Bool) : List Bool := BinaryNat.succ (denominatorMinusOne c)

theorem positive_FP : positive ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem negative_FP : negative ∈ FP := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairFst_mem_FP
theorem denominatorMinusOne_FP : denominatorMinusOne ∈ FP :=
  mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairSnd_mem_FP
theorem denominator_FP : denominator ∈ FP := mem_FP_comp denominatorMinusOne_FP BinaryNat.succ_mem_FP

def numerator (c : List Bool) : ℤ := (Nat.fromBitsLE (positive c) : ℤ) - Nat.fromBitsLE (negative c)
def divisor (c : List Bool) : ℕ := Nat.fromBitsLE (denominatorMinusOne c) + 1

noncomputable def threshold (c : List Bool) : ℝ := (numerator c : ℝ) / divisor c

noncomputable def polynomial (c : List Bool) : Polynomial ℤ :=
  Polynomial.monomial 1 (divisor c : ℤ) + Polynomial.C (Nat.fromBitsLE (negative c) : ℤ) -
    Polynomial.C (Nat.fromBitsLE (positive c) : ℤ)

theorem polynomial_degree (c : List Bool) : (polynomial c).natDegree ≤ 1 := by
  apply (Polynomial.natDegree_sub_le _ _).trans
  apply max_le
  · apply (Polynomial.natDegree_add_le _ _).trans
    exact max_le (Polynomial.natDegree_monomial_le _) (by simp)
  · simp

def massExponent (c : List Bool) : ℕ :=
  (positive c).length + (negative c).length + (denominatorMinusOne c).length + 2

theorem massExponent_unary : UnaryFn massExponent :=
  (((UnaryFn.length positive_FP).add (UnaryFn.length negative_FP)).add
    (UnaryFn.length denominatorMinusOne_FP)).add (UnaryFn.const 2)

theorem polynomial_mass (c : List Bool) : coefficientMass (polynomial c) ≤ 2 ^ massExponent c := by
  let S := (positive c).length + (negative c).length + (denominatorMinusOne c).length
  have hp : Nat.fromBitsLE (positive c) ≤ 2 ^ S :=
    (Nat.fromBitsLE_lt_pow_length _).le.trans (Nat.pow_le_pow_right (by decide) (by dsimp [S]; omega))
  have hn : Nat.fromBitsLE (negative c) ≤ 2 ^ S :=
    (Nat.fromBitsLE_lt_pow_length _).le.trans (Nat.pow_le_pow_right (by decide) (by dsimp [S]; omega))
  have hd : divisor c ≤ 2 ^ S :=
    (Nat.fromBitsLE_lt_pow_length _).trans_le (Nat.pow_le_pow_right (by decide) (by dsimp [S]; omega))
  have h := (coefficientMass_sub_le
    (Polynomial.monomial 1 (divisor c : ℤ) + Polynomial.C (Nat.fromBitsLE (negative c) : ℤ))
    (Polynomial.C (Nat.fromBitsLE (positive c) : ℤ))).trans
    (Nat.add_le_add_right (coefficientMass_add_le _ _) _)
  change coefficientMass (polynomial c) ≤ _ at h
  simp only [coefficientMass_monomial, coefficientMass_C, Int.natAbs_natCast] at h
  apply h.trans
  change _ ≤ 2 ^ (S + 2)
  rw [pow_add]
  norm_num
  omega

theorem polynomial_coeff (c : List Bool) (k : ℕ) :
    (polynomial c).coeff k = if k = 0 then -numerator c else if k = 1 then (divisor c : ℤ) else 0 := by
  by_cases hk : k = 0 <;> by_cases hk' : k = 1 <;>
    simp [polynomial, Polynomial.coeff_monomial, hk, hk', numerator, eq_comm]

def original (q : List Bool) : List Bool := pairFst (pairFst q)
def index (q : List Bool) : List Bool := pairSnd (pairFst q)
def modulus (q : List Bool) : List Bool := BinaryNat.succ (pairSnd q)
def modulusValue (q : List Bool) : ℕ := Nat.fromBitsLE (pairSnd q) + 1

theorem original_FP : original ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem index_FP : index ∈ FP := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
theorem modulus_FP : modulus ∈ FP := mem_FP_comp pairSnd_mem_FP BinaryNat.succ_mem_FP

def positiveResidue (q : List Bool) : List Bool := BinaryNat.mod (pair (positive (original q)) (modulus q))
def negativeResidue (q : List Bool) : List Bool := BinaryNat.mod (pair (negative (original q)) (modulus q))
def slope (q : List Bool) : List Bool := BinaryNat.mod (pair (denominator (original q)) (modulus q))
def opposite (q : List Bool) : List Bool := ArithmeticBits.negate (pair (modulus q) (positiveResidue q))
def constant (q : List Bool) : List Bool := ArithmeticBits.addMod (pair (modulus q) (pair (negativeResidue q) (opposite q)))

theorem positiveResidue_FP : positiveResidue ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair (mem_FP_comp original_FP positive_FP) modulus_FP) BinaryNat.mod_mem_FP
  exact mem_FP_of_eq h (fun _ => by simp only [positiveResidue, Function.comp_apply])
theorem negativeResidue_FP : negativeResidue ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair (mem_FP_comp original_FP negative_FP) modulus_FP) BinaryNat.mod_mem_FP
  exact mem_FP_of_eq h (fun _ => by simp only [negativeResidue, Function.comp_apply])
theorem slope_FP : slope ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair (mem_FP_comp original_FP denominator_FP) modulus_FP) BinaryNat.mod_mem_FP
  exact mem_FP_of_eq h (fun _ => by simp only [slope, Function.comp_apply])
theorem opposite_FP : opposite ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair modulus_FP positiveResidue_FP) ArithmeticBits.negate_mem_FP
  exact mem_FP_of_eq h (fun _ => by simp only [opposite, Function.comp_apply])
theorem constant_FP : constant ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair modulus_FP (mem_FP_pair negativeResidue_FP opposite_FP)) ArithmeticBits.addMod_mem_FP
  exact mem_FP_of_eq h (fun _ => by simp only [constant, Function.comp_apply])

def coefficient (q : List Bool) : List Bool :=
  if Nat.fromBitsLE (index q) = 0 then constant q else if Nat.fromBitsLE (index q) = 1 then slope q else []

theorem coefficient_FP : coefficient ∈ FP := by
  have hi := BinaryFn.fromBits index_FP
  have h := (hi.eq (BinaryFn.const 0)).ite_mem_FP constant_FP
    ((hi.eq (BinaryFn.const 1)).ite_mem_FP slope_FP (constFn_mem_FP []))
  exact mem_FP_of_eq h (fun _ => by simp only [coefficient])

theorem modulus_code (q : List Bool) : modulus q = BinaryNatCode.encode (modulusValue q) :=
  BinaryNat.succ_eq_bits _

private theorem natural_residue (word : List Bool) (m : ℕ) :
    BinaryNat.mod (pair word (BinaryNatCode.encode m)) = residueBits (Nat.fromBitsLE word : ZMod m) := by
  simp only [BinaryNat.mod_pair, residueBits, ZMod.val_natCast, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem constant_eq (q : List Bool) :
    constant q = residueBits ((-numerator (original q) : ℤ) : ZMod (modulusValue q)) := by
  let : NeZero (modulusValue q) := ⟨by unfold modulusValue; omega⟩
  unfold constant opposite negativeResidue positiveResidue
  rw [modulus_code, natural_residue, natural_residue, ArithmeticBits.negate_residueBits,
    ArithmeticBits.addMod_residueBits]
  congr 1
  simp only [numerator, Int.cast_neg, Int.cast_sub, Int.cast_natCast]
  ring

theorem slope_eq (q : List Bool) : slope q = residueBits ((divisor (original q) : ℤ) : ZMod (modulusValue q)) := by
  unfold slope
  rw [modulus_code, natural_residue]
  simp only [denominator, BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits, divisor, Int.cast_natCast]

theorem coefficient_eq (q : List Bool) : coefficient q =
    residueBits (((polynomial (original q)).coeff (Nat.fromBitsLE (index q)) : ℤ) : ZMod (modulusValue q)) := by
  rw [coefficient, polynomial_coeff]
  split_ifs
  · exact constant_eq q
  · exact slope_eq q
  · simp [residueBits, BinaryNatCode.encode]

theorem coefficient_packet (c : List Bool) (k m : ℕ) (hm : 0 < m) :
    coefficient (pair (pair c (BinaryNatCode.encode k)) (BinaryNatCode.encode (m - 1))) =
      IntegerTarskiSeedBits.integerResidue ((polynomial c).coeff k) m := by
  generalize hz : pair (pair c (BinaryNatCode.encode k)) (BinaryNatCode.encode (m - 1)) = z
  have hc : original z = c := by rw [original, ← hz, pairFst_pair, pairFst_pair]
  have hk : Nat.fromBitsLE (index z) = k := by rw [index, ← hz, pairFst_pair, pairSnd_pair]; exact Nat.fromBitsLE_bits k
  have hmod : modulusValue z = m := by
    rw [modulusValue, ← hz, pairSnd_pair]
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    omega
  subst c
  subst k
  subst m
  exact coefficient_eq z

theorem eval_real (c : List Bool) (x : ℝ) :
    ((polynomial c).map (algebraMap ℤ ℝ)).eval x = (divisor c : ℝ) * x - (numerator c : ℝ) := by
  simp [polynomial, numerator]
  ring

theorem sign_neg_iff (c : List Bool) (x : ℝ) :
    SignType.sign (((polynomial c).map (algebraMap ℤ ℝ)).eval x) = .neg ↔ x < threshold c := by
  rw [SignType.neg_eq_neg_one, sign_eq_neg_one_iff, eval_real]
  have hd : (0 : ℝ) < divisor c := by unfold divisor; positivity
  rw [threshold, lt_div_iff₀ hd]
  constructor <;> intro h <;> linarith

end LeanCanny.Algebra.RationalCutBits
