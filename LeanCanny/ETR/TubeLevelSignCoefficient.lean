/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeLevelSignReaders

/-! # Sign-query coefficient computation from native coordinate readers

An FP mask lookup selects constant one on active rows. Inactive rows use the
complete native constraint-substitution computation. Only root and coordinate
coefficient readers remain as hypotheses of the sample-counting endpoint.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeLevelSign
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open TubeLevelPacket TubeEncoding MatrixPower RationalSubstitution
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm

def coefficientRow (q : List Bool) : List Bool := pairFst (IntegerBits.selectedDegree q)
def coefficientDegree (q : List Bool) : List Bool := pairSnd (IntegerBits.selectedDegree q)

theorem coefficientRow_FP : coefficientRow ∈ FP := mem_FP_comp IntegerBits.selectedDegree_mem_FP pairFst_mem_FP
theorem coefficientDegree_FP : coefficientDegree ∈ FP := mem_FP_comp IntegerBits.selectedDegree_mem_FP pairSnd_mem_FP

noncomputable def UseOne (S : Source) (q : List Bool) : Prop :=
  (S.mask (IntegerBits.context q))[TubeConstraintCoefficient.cappedRow
    (S.packet ∘ IntegerBits.context) coefficientRow q]?.getD false = true

theorem useOne_fppred (S : Source) (hp : S.packet ∈ FP) (hm : S.mask ∈ FP) : FPPred (UseOne S) := by
  have hn := TubeSampleCoefficient.n_unary (S.packet ∘ IntegerBits.context) (mem_FP_comp IntegerBits.context_mem_FP hp)
  have hc := (TubeZero.constraintCount_unary hn).sub (UnaryFn.const 1)
  exact FPPred.getBit (mem_FP_comp IntegerBits.context_mem_FP hm) (UnaryFn.fromBitsLE_min coefficientRow_FP hc)

noncomputable def oneValue (q : List Bool) : List Bool :=
  if Nat.fromBitsLE (coefficientDegree q) = 0 then IntegerBits.coefficientResidue 1 (IntegerBits.mValue q) else []

theorem oneEvaluator : SpaceFunction oneValue := by
  have hzero := BinaryNat.le_fppred coefficientDegree_FP (constFn_mem_FP [])
  have hone := mem_FP_comp (mem_FP_comp pairSnd_mem_FP BinaryNat.succ_mem_FP) ArithmeticBits.one_mem_FP
  have he := hzero.ite_mem_FP hone (constFn_mem_FP [])
  apply SpaceFunction.ofFP
  apply mem_FP_of_eq he
  intro q
  have hn : Nat.fromBitsLE ([] : List Bool) = 0 := rfl
  simp only [hn, Nat.le_zero, oneValue]
  by_cases hz : Nat.fromBitsLE (coefficientDegree q) = 0
  · simp only [hz, ite_true, Function.comp_apply, BinaryNat.succ_eq_bits]
    exact ArithmeticBits.one_residueBits (IntegerBits.mValue q)
  · simp only [hz, ite_false]

attribute [local irreducible] IntegerBits.coefficientResidue

theorem oneValue_packet (c : List Bool) (i k m : ℕ) (hm : 0 < m) :
    oneValue (pair (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k)))
      (BinaryNatCode.encode (m - 1))) = IntegerBits.coefficientResidue ((1 : Polynomial ℤ).coeff k) m := by
  simp only [oneValue, coefficientDegree, IntegerBits.selectedDegree, IntegerBits.mValue,
    pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.sub_add_cancel hm]
  by_cases hk : k = 0
  · simp only [hk, ite_true, Polynomial.coeff_one_zero]
  · simp only [hk, ite_false, Polynomial.coeff_one]
    unfold IntegerBits.coefficientResidue residueBits
    simp only [Int.cast_zero, ZMod.val_zero, BinaryNatCode.encode]
    rfl

noncomputable def polynomialValue (S : Source) (q : List Bool) : List Bool :=
  if UseOne S q then oneValue q else substitutedValue S q

theorem polynomialEvaluator (S : Source) (C : CoefficientReaders S)
    (hp : S.packet ∈ FP) (hm : S.mask ∈ FP) : SpaceFunction (polynomialValue S) := by
  let E := SpaceFunction.branch (fun q => decide (UseOne S q)) (useOne_fppred S hp hm).flag_mem_FP
    oneEvaluator (substitutedEvaluator S C hp)
  exact E.congr (funext fun q => by by_cases h : UseOne S q <;> simp [polynomialValue, h])

set_option backward.isDefEq.respectTransparency false in
theorem useOne_packet (S : Source) (c : List Bool)
    (i : PerturbedSource.Index (pairFst (S.packet c))) (k m : ℕ) :
    UseOne S (pair (pair c (pair
      (BinaryNatCode.encode (constraintEquiv (TubeIndexed.arity (pairFst (S.packet c))) i).val)
      (BinaryNatCode.encode k))) (BinaryNatCode.encode (m - 1))) ↔
      i ∈ activeSet (TubeIndexed.arity (pairFst (S.packet c))) (S.mask c) := by
  have hi := (constraintEquiv (TubeIndexed.arity (pairFst (S.packet c))) i).isLt
  have hle : (constraintEquiv (TubeIndexed.arity (pairFst (S.packet c))) i).val ≤
      constraintCount (TubeIndexed.arity (pairFst (S.packet c))) - 1 := by omega
  simp only [UseOne, coefficientRow, IntegerBits.context, IntegerBits.selectedDegree,
    TubeConstraintCoefficient.cappedRow, TubeSampleCoefficient.n, Function.comp_apply, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [min_eq_left hle]
  simp only [activeSet, Finset.mem_filter, Finset.mem_univ, true_and]

set_option backward.isDefEq.respectTransparency false in
theorem polynomialValue_packet (S : Source) (c : List Bool)
    (i : PerturbedSource.Index (pairFst (S.packet c))) (k m : ℕ) (hm : 0 < m) :
    polynomialValue S (pair (pair c (pair
      (BinaryNatCode.encode (constraintEquiv (TubeIndexed.arity (pairFst (S.packet c))) i).val)
      (BinaryNatCode.encode k))) (BinaryNatCode.encode (m - 1))) =
      IntegerBits.coefficientResidue
        ((signQuery (S.packet c) (S.mask c) (S.projection c) (S.level c) (S.coordinates c) i).coeff k) m := by
  have hu := useOne_packet S c i k m
  unfold polynomialValue signQuery
  by_cases hi : i ∈ activeSet (TubeIndexed.arity (pairFst (S.packet c))) (S.mask c)
  · rw [ite_eq_left (hu.mpr hi), ite_eq_left hi]
    exact oneValue_packet c _ k m hm
  · rw [ite_eq_right (fun h => hi (hu.mp h)), ite_eq_right hi]
    exact substitutedValue_packet S c i k m hm

end LeanCanny.ETR.TubeLevelSign
