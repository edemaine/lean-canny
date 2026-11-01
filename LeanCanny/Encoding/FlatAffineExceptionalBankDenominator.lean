/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineExceptionalParentBank

/-! # Native exact leading coefficients and common bank denominator

Each factor uses the actual degree of its original integer polynomial.
A streamed modular product computes the common integer denominator of
the constructed integral bank, charging every original coefficient call.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalBankSource
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineLastHeightRow (parentCone)
open scoped Classical BigOperators

theorem actualDegree_evaluator {F : Inputs} (hF : F.Access)
    (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (hh : UnaryFn (fun u => (h u).val)) :
    SpaceFunction (fun w => BinaryNatCode.encode (polynomial F C h w).natDegree) := by
  have A := access hF C h hh
  exact IntegerPolynomialBits.degreeEvaluator _ A.coefficient _ _ A.degree A.mass
    (source F C h).degree_bound (source F C h).mass_bound

noncomputable def leading (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (q : List Bool) : List Bool :=
  PrimitivePairBits.coefficient (polynomial F C h)
    (pair (pair (pairFst q) (BinaryNatCode.encode (polynomial F C h (pairFst q)).natDegree)) (pairSnd q))

theorem leading_evaluator {F : Inputs} (hF : F.Access)
    (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (hh : UnaryFn (fun u => (h u).val)) : SpaceFunction (leading F C h) := by
  have E := (((actualDegree_evaluator hF C h hh).precompose pairFst pairFst_mem_FP).withInput.postcompose
    FlatAffineExceptionalIntegralPrefix.leadingQuery FlatAffineExceptionalIntegralPrefix.leadingQuery_FP).chain
      (coefficient_evaluator hF C h hh)
  exact E.congr (funext fun q => by
    simp only [leading, FlatAffineExceptionalIntegralPrefix.leadingQuery, Function.comp_apply, pairFst_pair, pairSnd_pair])

theorem leading_packet (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (w m : List Bool) :
    leading F C h (pair w m) = residueBits ((polynomial F C h w).leadingCoeff : ZMod (Nat.fromBitsLE m + 1)) := by
  simp only [leading, PrimitivePairBits.coefficient, RationalSubstitution.IntegerBits.context,
    RationalSubstitution.IntegerBits.selectedDegree, RationalSubstitution.IntegerBits.mValue,
    pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, Polynomial.coeff_natDegree]
  rfl

noncomputable def denominator (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (u : List Bool) : ℤ :=
  ∏ i : Fin (births F u), (finitePolynomial F C h u i).leadingCoeff

theorem denominator_bank (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u : List Bool) (hm : births F u ≤ S + 1) :
    FlatAffineExceptionalParentBank.denominator F C h S u hm = denominator F C h u := by
  unfold FlatAffineExceptionalParentBank.denominator CommonIntegerDenominator.denominator denominator
  apply Finset.prod_congr rfl
  intro i _
  exact FlatAffineExceptionalParentBank.denominator_eq F C h S u hm i

noncomputable def denominatorValue (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (q : List Bool) : List Bool :=
  residueBits (denominator F C h (pairFst q) : ZMod (Nat.fromBitsLE (pairSnd q) + 1))

theorem denominator_evaluator {F : Inputs} (hF : F.Access)
    (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (hh : UnaryFn (fun u => (h u).val)) :
    SpaceFunction (denominatorValue F C h) := by
  have E := (leading_evaluator hF C h hh).precompose FlatAffineExceptionalIntegralPrefix.leadingQuery
    FlatAffineExceptionalIntegralPrefix.leadingQuery_FP
  have HC := (BinaryFn.ofUnary ((births_unary hF).comp pairFst_mem_FP)).bits_mem_FP
  have HM := ((BinaryFn.fromBits pairSnd_mem_FP).add (BinaryFn.const 1)).bits_mem_FP
  have HE : (fun c => Nat.fromBitsLE (BinaryNatCode.encode (Nat.fromBitsLE (pairSnd c) + 1))) =
      (fun c => Nat.fromBitsLE (pairSnd c) + 1) := funext (fun _ => Nat.fromBitsLE_bits _)
  have H := ModularProduct.evaluatorWithModulus E
    (fun q => BinaryNatCode.encode (births F (pairFst q)))
    (fun q => BinaryNatCode.encode (Nat.fromBitsLE (pairSnd q) + 1)) HC HM _ HE
    (fun q i => ((polynomial F C h (pair (pairFst q) (BinaryNatCode.encode i))).leadingCoeff :
      ZMod (Nat.fromBitsLE (pairSnd q) + 1)))
    (fun _ => Nat.succ_pos _) (fun q i _ => by
      simpa only [Function.comp_apply, FlatAffineExceptionalIntegralPrefix.leadingQuery, pairFst_pair, pairSnd_pair]
        using leading_packet F C h (pair (pairFst q) (BinaryNatCode.encode i)) (pairSnd q))
  exact H.congr (funext fun q => by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    unfold denominatorValue denominator
    rw [Int.cast_prod]
    congr 1
    exact (Fin.prod_univ_eq_prod_range _ _).symm)

end LeanCanny.Encoding.FlatAffineExceptionalBankSource
