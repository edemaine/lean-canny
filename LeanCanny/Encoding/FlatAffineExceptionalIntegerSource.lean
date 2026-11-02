/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalIntegerCommands
/-! # The actual initial bank source with literal X padding -/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalIntegerSource
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open scoped Classical
attribute [local irreducible] ArithmeticBits.one

def padded (w : List Bool) : Prop := Nat.fromBitsLE (pairFst w) = 0
instance (w : List Bool) : Decidable (padded w) := inferInstanceAs (Decidable (_ = _))
theorem padded_FP : FPPred padded := (BinaryFn.fromBits pairFst_mem_FP).eq (BinaryFn.const 0)

noncomputable def source (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) : IntegerPolynomialRootQueriesBits.Source where
  polynomial w := if padded w then Polynomial.X else (FlatAffineExceptionalBankSource.source F C h).polynomial (pairSnd w)
  degree w := if padded w then 1 else (FlatAffineExceptionalBankSource.source F C h).degree (pairSnd w)
  mass w := if padded w then 3 else (FlatAffineExceptionalBankSource.source F C h).mass (pairSnd w)
  degree_bound w := by
    split_ifs
    · simp only [Polynomial.natDegree_X, le_refl]
    · exact (FlatAffineExceptionalBankSource.source F C h).degree_bound _
  mass_bound w := by
    split_ifs
    · change coefficientMass (Polynomial.X : Polynomial ℤ) ≤ 2 ^ (1 + (1 + 1).size)
      apply coefficientMass_le_pow_of_degree_coeff _ 1 1 (by simp)
      intro k
      rw [Polynomial.coeff_X]
      split_ifs <;> norm_num
    · exact (FlatAffineExceptionalBankSource.source F C h).mass_bound _

def xCoefficient (z : List Bool) : List Bool :=
  if Nat.fromBitsLE (RationalSubstitution.IntegerBits.selectedDegree z) = 1 then
    ArithmeticBits.one (BinaryNatCode.encode (RationalSubstitution.IntegerBits.mValue z)) else []
theorem xCoefficient_FP : xCoefficient ∈ FP := by
  have HD := (BinaryFn.fromBits RationalSubstitution.IntegerBits.selectedDegree_mem_FP).eq (BinaryFn.const 1)
  have HM : BinaryFn RationalSubstitution.IntegerBits.mValue := (BinaryFn.fromBits pairSnd_mem_FP).add (BinaryFn.const 1)
  exact HD.ite_mem_FP (mem_FP_comp (f := fun z => BinaryNatCode.encode (RationalSubstitution.IntegerBits.mValue z))
    (g := ArithmeticBits.one) HM.bits_mem_FP ArithmeticBits.one_mem_FP) (constFn_mem_FP [])
theorem xCoefficient_eq (z : List Bool) :
    xCoefficient z = PrimitivePairBits.coefficient (fun _ => (Polynomial.X : Polynomial ℤ)) z := by
  unfold xCoefficient
  by_cases hk : Nat.fromBitsLE (RationalSubstitution.IntegerBits.selectedDegree z) = 1
  · rw [ite_eq_left hk]
    unfold PrimitivePairBits.coefficient
    rw [Polynomial.coeff_X, ite_eq_left hk.symm]
    exact ArithmeticBits.one_residueBits _
  · rw [ite_eq_right hk]
    unfold PrimitivePairBits.coefficient
    rw [Polynomial.coeff_X, ite_eq_right (Ne.symm hk)]
    exact ArithmeticBits.zero_residueBits _

def bankCoefficientQuery (z : List Bool) : List Bool :=
  IntegralMixedIntegerProducerSpaceBits.coefficientPullback pairSnd z
theorem bankCoefficientQuery_FP : bankCoefficientQuery ∈ FP :=
  IntegralMixedIntegerProducerSpaceBits.coefficientPullback_FP pairSnd pairSnd_mem_FP

theorem coefficient_evaluator {F : Inputs} (hF : F.Access)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (h : (u : List Bool) → Fin (arity F u))
    (hh : UnaryFn (fun u => (h u).val)) :
    SpaceFunction (PrimitivePairBits.coefficient (source F C h).polynomial) := by
  have HP := padded_FP.comp RationalSubstitution.IntegerBits.context_mem_FP
  have EX := SpaceFunction.ofFP _ xCoefficient_FP
  have EB := (FlatAffineExceptionalBankSource.coefficient_evaluator hF C h hh).precompose bankCoefficientQuery bankCoefficientQuery_FP
  refine (SpaceFunction.branch _ HP.flag_mem_FP EX EB).congr (funext fun z => ?_)
  simp only [Function.comp_apply]
  by_cases hz : padded (RationalSubstitution.IntegerBits.context z)
  · rw [show decide (padded (RationalSubstitution.IntegerBits.context z)) = true from decide_eq_true hz]
    simp only [ite_true]
    rw [xCoefficient_eq]
    simp only [PrimitivePairBits.coefficient, source, hz, ite_true]
  · rw [show decide (padded (RationalSubstitution.IntegerBits.context z)) = false from decide_eq_false hz]
    simp only [Bool.false_eq_true, ite_false]
    change ¬padded (pairFst (pairFst z)) at hz
    simp only [PrimitivePairBits.coefficient, source, bankCoefficientQuery,
      IntegralMixedIntegerProducerSpaceBits.coefficientPullback, RationalSubstitution.IntegerBits.context,
      RationalSubstitution.IntegerBits.selectedDegree, RationalSubstitution.IntegerBits.mValue, pairFst_pair, pairSnd_pair, hz, ite_false]
    rfl

theorem access {F : Inputs} (hF : F.Access)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (h : (u : List Bool) → Fin (arity F u))
    (hh : UnaryFn (fun u => (h u).val)) : IntegerPolynomialRootQueriesBits.Access (source F C h) where
  coefficient := coefficient_evaluator hF C h hh
  degree := BinaryFn.ite padded_FP (BinaryFn.const 1)
    (((FlatAffineExceptionalBankSource.access hF C h hh).degree).comp pairSnd_mem_FP)
  mass := BinaryFn.ite padded_FP (BinaryFn.const 3)
    (((FlatAffineExceptionalBankSource.access hF C h hh).mass).comp pairSnd_mem_FP)

end LeanCanny.Encoding.FlatAffineExceptionalIntegerSource
