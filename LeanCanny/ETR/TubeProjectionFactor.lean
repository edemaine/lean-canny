/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeProjectionRestriction
public import LeanCanny.Algebra.ModularNatMulFP

/-! # Certified modular derivative factors for projection queries

The exponent factor is read in binary and incremented in FP. Multiplication
uses the positive query modulus and retains canonical residues, including at
modulus one. The tube child and all retained context are counted in space.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeProjectionQuery
open Complexity
open LeanCanny.Encoding LeanCanny.Computation
open Geometry TubeEncoding TubeProjectionEncoding
open Algebra.MatrixPower

attribute [local irreducible] BinaryNat.succ BinaryNat.mulMod child

def factorWord (n W r : List Bool → ℕ) (target : List Bool → List Bool) (c : List Bool) : List Bool :=
  BinaryNat.succ (block n W target (pair c (BinaryNatCode.encode (r c))))

theorem factorWord_mem_FP {n W r : List Bool → ℕ} {target : List Bool → List Bool}
    (hn : UnaryFn n) (hW : UnaryFn W) (hr : UnaryFn r) (ht : target ∈ FP) : factorWord n W r target ∈ FP := by
  have hq := mem_FP_pair id_mem_FP (bits_mem_FP hr)
  have h := mem_FP_comp (mem_FP_comp hq (block_mem_FP hn hW ht)) BinaryNat.succ_mem_FP
  exact mem_FP_of_eq h (fun _ => rfl)

theorem factorWord_correct (n W r : List Bool → ℕ) (target : List Bool → List Bool) (c : List Bool)
    (j : Coordinate (n c)) (hr : r c = (coordinateEquiv (n c) j).val) :
    factorWord n W r target c = BinaryNatCode.encode (restriction n W target c j + 1) := by
  unfold factorWord
  rw [block_packet n W target c (r c) (by rw [hr]; exact (coordinateEquiv (n c) j).isLt)]
  rw [BinaryNat.succ_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits, restriction_apply, hr]
  rfl

def finish (n W r : List Bool → ℕ) (target modulus : List Bool → List Bool) (derivative : Bool) (z : List Bool) : List Bool :=
  if derivative then BinaryNat.mulMod (pair (TubeCombine.modulus modulus z)
    (pair (pairSnd z) (factorWord n W r target (pairFst z)))) else pairSnd z

theorem finish_mem_FP {n W r : List Bool → ℕ} {target modulus : List Bool → List Bool}
    (hn : UnaryFn n) (hW : UnaryFn W) (hr : UnaryFn r) (ht : target ∈ FP) (hm : modulus ∈ FP) (derivative : Bool) :
    finish n W r target modulus derivative ∈ FP := by
  cases derivative with
  | false => exact pairSnd_mem_FP
  | true =>
    have hf := mem_FP_comp pairFst_mem_FP (factorWord_mem_FP hn hW hr ht)
    have h := mem_FP_comp (mem_FP_pair (TubeCombine.modulus_mem_FP hm) (mem_FP_pair pairSnd_mem_FP hf)) BinaryNat.mulMod_mem_FP
    exact mem_FP_of_eq h (fun _ => rfl)

theorem finish_residueBits (n W r : List Bool → ℕ) (target modulus : List Bool → List Bool)
    (derivative : Bool) (c : List Bool) (j : Coordinate (n c)) (hr : r c = (coordinateEquiv (n c) j).val)
    (A : ZMod (Nat.fromBitsLE (modulus c) + 1)) :
    finish n W r target modulus derivative (pair c (residueBits A)) =
      residueBits (A * ((if derivative then restriction n W target c j + 1 else 1 : ℕ) : ZMod (Nat.fromBitsLE (modulus c) + 1))) := by
  cases derivative with
  | false => simp only [finish, Bool.false_eq_true, ite_false, pairSnd_pair, Nat.cast_one, mul_one]
  | true =>
    simp only [finish, ite_true, TubeCombine.modulus, pairFst_pair, pairSnd_pair]
    rw [factorWord_correct n W r target c j hr, BinaryNat.succ_eq_bits]
    exact ArithmeticBits.mulMod_nat_residueBits _ _ _

noncomputable def productValue (base : List Bool → List Bool) (W r : List Bool → ℕ)
    (active target modulus : List Bool → List Bool) (derivative : Bool) (c : List Bool) : List Bool :=
  finish (TubeDense.arity base) W r target modulus derivative (pair c (child base W r active target modulus derivative c))

noncomputable def productEvaluator (base : List Bool → List Bool) (W r : List Bool → ℕ)
    (active target modulus : List Bool → List Bool) (derivative : Bool)
    (hb : base ∈ FP) (hW : UnaryFn W) (hr : UnaryFn r) (ha : active ∈ FP) (ht : target ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (productValue base W r active target modulus derivative) := by
  let R := childEvaluator base W r active target modulus derivative hb hW hr ha ht hm
  let E := R.withInput.postcompose (finish (TubeDense.arity base) W r target modulus derivative)
    (finish_mem_FP (TubeDense.arity_unary hb) hW hr ht hm derivative)
  exact E.congr (funext fun _ => rfl)

theorem productValue_correct (base : List Bool → List Bool) (W r : List Bool → ℕ)
    (active target modulus : List Bool → List Bool) (derivative : Bool) (c : List Bool)
    (j : Coordinate (TubeDense.arity base c)) (hr : r c = (coordinateEquiv (TubeDense.arity base c) j).val) :
    productValue base W r active target modulus derivative c = residueBits
      (((TubePolynomial.integerPolynomial (TubeDense.polynomial base c) (activeSet (TubeDense.arity base c) (active c))).coeff
        (restriction (TubeDense.arity base) W target c + (if derivative then Finsupp.single j 1 else 0)) : ZMod (Nat.fromBitsLE (modulus c) + 1)) *
          ((if derivative then restriction (TubeDense.arity base) W target c j + 1 else 1 : ℕ) : ZMod (Nat.fromBitsLE (modulus c) + 1))) := by
  unfold productValue
  rw [child_correct base W r active target modulus derivative c j hr,
    finish_residueBits (TubeDense.arity base) W r target modulus derivative c j hr]

end LeanCanny.ETR.TubeProjectionQuery
