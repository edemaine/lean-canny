/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CoordinateReaders
public import LeanCanny.Computation.SpaceFunctionBranch

/-! # Native constant-denominator coordinate readers

One original integer residue reader supplies the common denominator at
every coordinate. Only coefficient zero calls it; all other coefficients
return zero. The caller's modulus is retained, including modulus one.
-/

@[expose] public section
namespace LeanCanny.Algebra.CommonDenominatorCoordinateBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def degreeWord (p : List Bool) : List Bool := pairSnd (pairSnd (pairFst p))
def scalarQuery (p : List Bool) : List Bool := pair (pairFst (pairFst p)) (pairSnd p)

theorem degreeWord_FP : degreeWord ∈ FP :=
  mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairSnd_mem_FP

theorem scalarQuery_FP : scalarQuery ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP

def value (scalar : List Bool → List Bool) (p : List Bool) : List Bool :=
  if Nat.fromBitsLE (degreeWord p) = 0 then scalar (scalarQuery p) else []

theorem evaluator {scalar : List Bool → List Bool} (E : SpaceFunction scalar) : SpaceFunction (value scalar) := by
  have HP := (BinaryFn.fromBits degreeWord_FP).eq (BinaryFn.const 0)
  exact (SpaceFunction.branch (fun p => decide (Nat.fromBitsLE (degreeWord p) = 0)) HP.flag_mem_FP
    (E.precompose scalarQuery scalarQuery_FP) (SpaceFunction.ofFP _ (constFn_mem_FP []))).congr
      (funext fun p => by simp only [value, decide_eq_true_eq, Function.comp_apply])

theorem packet (q : List Bool → ℤ) (scalar : List Bool → List Bool)
    (hs : ∀ c m, 0 < m → scalar (pair c (BinaryNatCode.encode (m - 1))) = residueBits ((q c : ℤ) : ZMod m))
    (c : List Bool) (i k m : ℕ) (hm : 0 < m) :
    value scalar (pair (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) (BinaryNatCode.encode (m - 1))) =
      residueBits (((Polynomial.C (q c) : Polynomial ℤ).coeff k : ℤ) : ZMod m) := by
  simp only [value, degreeWord, scalarQuery, pairFst_pair, pairSnd_pair, BinaryNatCode.encode,
    Nat.fromBitsLE_bits, Polynomial.coeff_C]
  by_cases hk : k = 0
  · simp only [ite_eq_left hk]
    exact hs c m hm
  · simp only [ite_eq_right hk, Int.cast_zero, residueBits, ZMod.val_zero]
    rfl

def readers (arity : List Bool → ℕ) (numerator : List Bool → ℕ → Polynomial ℤ) (q : List Bool → ℤ)
    (num scalar : List Bool → List Bool) (N : SpaceFunction num) (Q : SpaceFunction scalar)
    (hn : ∀ c i, i < arity c → ∀ k m, 0 < m →
      num (pair (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) (BinaryNatCode.encode (m - 1))) =
        residueBits (((numerator c i).coeff k : ℤ) : ZMod m))
    (hq : ∀ c m, 0 < m → scalar (pair c (BinaryNatCode.encode (m - 1))) = residueBits ((q c : ℤ) : ZMod m)) :
    RationalSubstitution.IntegerBits.CoordinateReaders arity numerator (fun c _ => Polynomial.C (q c)) where
  numerator := num
  denominator := value scalar
  numeratorEvaluator := N
  denominatorEvaluator := evaluator Q
  numerator_eq := hn
  denominator_eq c i _ k m hm := packet q scalar hq c i k m hm

end LeanCanny.Algebra.CommonDenominatorCoordinateBits
