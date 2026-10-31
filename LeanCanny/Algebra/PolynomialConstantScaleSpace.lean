/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PrimitivePairReaders
public import LeanCanny.Algebra.ModularPowFP
public import LeanCanny.Computation.SpaceFunctionComposition
public import Mathlib.Algebra.Polynomial.Eval.Degree

/-! # Native coefficient access after scaling a variable by an integer power

The integer itself need not have a short encoding. Its original modular
reader is composed with binary modular powering and the original polynomial
coefficient reader. No modular inverse or materialized integer is required.
-/

@[expose] public section
namespace LeanCanny.Algebra.PolynomialConstantScaleBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open RationalSubstitution.IntegerBits (context selectedDegree mValue coefficientResidue)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BinaryNat.powMod BinaryNat.mulMod

noncomputable def constantValue (C : List Bool → ℤ) (q : List Bool) : List Bool :=
  residueBits ((C (LeanCanny.pairFst q) : ℤ) : ZMod (Nat.fromBitsLE (LeanCanny.pairSnd q) + 1))

theorem constant_packet (C : List Bool → ℤ) (c m : List Bool) :
    constantValue C (LeanCanny.pair c m) =
      residueBits ((C c : ℤ) : ZMod (Nat.fromBitsLE m + 1)) := by
  generalize hz : LeanCanny.pair c m = z
  have hc : LeanCanny.pairFst z = c := by rw [← hz, LeanCanny.pairFst_pair]
  have hm : LeanCanny.pairSnd z = m := by rw [← hz, LeanCanny.pairSnd_pair]
  subst c
  subst m
  rfl

def constantQuery (q : List Bool) : List Bool := LeanCanny.pair (context q) (LeanCanny.pairSnd q)

theorem constantQuery_FP : constantQuery ∈ FP :=
  mem_FP_pair RationalSubstitution.IntegerBits.context_mem_FP pairSnd_mem_FP

def exponent (e : List Bool → ℕ) (q : List Bool) : ℕ := e (context q) * Nat.fromBitsLE (selectedDegree q)

theorem exponent_binary {e : List Bool → ℕ} (he : BinaryFn e) : BinaryFn (exponent e) := by
  have hE : BinaryFn (fun q => e (context q)) := he.comp RationalSubstitution.IntegerBits.context_mem_FP
  exact hE.mul (BinaryFn.fromBits RationalSubstitution.IntegerBits.selectedDegree_mem_FP)

def powerQuery (e : List Bool → ℕ) (r : List Bool) : List Bool :=
  LeanCanny.pair (LeanCanny.pairSnd r) (LeanCanny.pair
    (BinaryNatCode.encode (exponent e (LeanCanny.pairFst r))) (LeanCanny.pairSnd (LeanCanny.pairFst r)))

theorem powerQuery_FP {e : List Bool → ℕ} (he : BinaryFn e) : powerQuery e ∈ FP := by
  have hP : BinaryFn (fun r => exponent e (LeanCanny.pairFst r)) := (exponent_binary he).comp pairFst_mem_FP
  exact mem_FP_pair pairSnd_mem_FP (mem_FP_pair hP.bits_mem_FP
    (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP))

noncomputable def powerValue (C : List Bool → ℤ) (e : List Bool → ℕ) (q : List Bool) : List Bool :=
  residueBits (((C (context q) : ℤ) : ZMod (Nat.fromBitsLE (LeanCanny.pairSnd q) + 1)) ^ exponent e q)

theorem power_evaluator (C : List Bool → ℤ) {e : List Bool → ℕ} (he : BinaryFn e)
    (EC : SpaceFunction (constantValue C)) : SpaceFunction (powerValue C e) := by
  have H := ((EC.precompose constantQuery constantQuery_FP).withInput.postcompose
    (powerQuery e) (powerQuery_FP he)).postcompose BinaryNat.powMod BinaryNat.powMod_mem_FP
  apply H.congr
  funext q
  change BinaryNat.powMod (powerQuery e (LeanCanny.pair q (constantValue C (constantQuery q)))) = powerValue C e q
  simp only [powerQuery, LeanCanny.pairFst_pair, LeanCanny.pairSnd_pair]
  unfold constantQuery
  rw [constant_packet C (context q) (LeanCanny.pairSnd q)]
  rw [ArithmeticBits.powMod_residueBits]
  simp only [powerValue, BinaryNatCode.encode, Nat.fromBitsLE_bits]

def finish (r : List Bool) : List Bool :=
  LeanCanny.pair (BinaryNatCode.encode (Nat.fromBitsLE (LeanCanny.pairSnd (LeanCanny.pairFst r)) + 1))
    (LeanCanny.pairSnd r)

theorem finish_FP : finish ∈ FP := by
  have hm : BinaryFn (fun r => Nat.fromBitsLE (LeanCanny.pairSnd (LeanCanny.pairFst r))) :=
    (BinaryFn.fromBits pairSnd_mem_FP).comp pairFst_mem_FP
  exact mem_FP_pair (hm.add (BinaryFn.const 1)).bits_mem_FP pairSnd_mem_FP

noncomputable def scaled (p : List Bool → Polynomial ℤ) (C : List Bool → ℤ) (e : List Bool → ℕ)
    (c : List Bool) : Polynomial ℤ := (p c).comp (Polynomial.C (C c ^ e c) * Polynomial.X)

theorem evaluator (p : List Bool → Polynomial ℤ) (C : List Bool → ℤ) {e : List Bool → ℕ} (he : BinaryFn e)
    (EP : SpaceFunction (PrimitivePairBits.coefficient p)) (EC : SpaceFunction (constantValue C)) :
    SpaceFunction (PrimitivePairBits.coefficient (scaled p C e)) := by
  have H := ((EP.pairOutputs (power_evaluator C he EC)).withInput.postcompose finish finish_FP).postcompose
    BinaryNat.mulMod BinaryNat.mulMod_mem_FP
  apply H.congr
  funext q
  change BinaryNat.mulMod (finish (LeanCanny.pair q
    (LeanCanny.pair (PrimitivePairBits.coefficient p q) (powerValue C e q)))) =
      PrimitivePairBits.coefficient (scaled p C e) q
  simp only [finish, LeanCanny.pairFst_pair, LeanCanny.pairSnd_pair]
  change BinaryNat.mulMod (LeanCanny.pair (BinaryNatCode.encode (Nat.fromBitsLE (LeanCanny.pairSnd q) + 1))
    (LeanCanny.pair
      (residueBits (((p (context q)).coeff (Nat.fromBitsLE (selectedDegree q)) : ℤ) : ZMod (Nat.fromBitsLE (LeanCanny.pairSnd q) + 1)))
      (residueBits (((C (context q) : ℤ) : ZMod (Nat.fromBitsLE (LeanCanny.pairSnd q) + 1)) ^ exponent e q)))) =
      residueBits (((scaled p C e (context q)).coeff (Nat.fromBitsLE (selectedDegree q)) : ℤ) : ZMod (Nat.fromBitsLE (LeanCanny.pairSnd q) + 1))
  rw [ArithmeticBits.mulMod_residueBits, scaled, Polynomial.comp_C_mul_X_coeff]
  simp only [Int.cast_mul, Int.cast_pow, ← pow_mul, exponent]

end LeanCanny.Algebra.PolynomialConstantScaleBits
