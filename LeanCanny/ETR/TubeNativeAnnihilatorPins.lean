/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeCoordinateAnnihilatorDyadic

/-! # Native linear annihilators for pinned rational parameters -/

@[expose] public section

namespace LeanCanny.ETR.TubeNativeAnnihilatorPins
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra Polynomial MatrixPower
open RationalSubstitution.IntegerBits (context selectedDegree mValue coefficientResidue)
open scoped Classical
attribute [local irreducible] ArithmeticBits.negate BinaryNat.succ

noncomputable def polynomial (n d : ℤ) : Polynomial ℤ := C d * X - C n

theorem coeff (n d : ℤ) (k : ℕ) :
    (polynomial n d).coeff k = if k = 1 then d else if k = 0 then -n else 0 := by
  unfold polynomial
  simp only [coeff_sub, coeff_C_mul, coeff_X, coeff_C]
  split_ifs <;> simp_all

theorem degree (n d : ℤ) : (polynomial n d).natDegree ≤ 1 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [coeff, ite_eq_right (by omega), ite_eq_right (by omega)]

theorem ne_zero (n d : ℤ) (hd : d ≠ 0) : polynomial n d ≠ 0 := by
  intro h
  have h1 := congrArg (fun p : Polynomial ℤ => p.coeff 1) h
  apply hd
  simpa only [coeff, ite_true, coeff_zero] using h1

theorem mass (n d : ℤ) : coefficientMass (polynomial n d) ≤ d.natAbs + n.natAbs := by
  apply (coefficientMass_sub_le _ _).trans
  rw [show C d * X = monomial 1 d by simp [← C_mul_X_pow_eq_monomial],
    coefficientMass_monomial, coefficientMass_C]

theorem eval {K : Type*} [Field K] (n d : ℤ) (x : K) :
    (polynomial n d).eval₂ (Int.castRingHom K) x = (d : K) * x - n := by
  simp only [polynomial, eval₂_sub, eval₂_mul, eval₂_C, eval₂_X, Int.coe_castRingHom]

theorem root_iff {K : Type*} [Field K] (n d : ℤ) (x : K) (hd : (d : K) ≠ 0) :
    (polynomial n d).eval₂ (Int.castRingHom K) x = 0 ↔ x = (n : K) / d := by
  rw [eval, sub_eq_zero, eq_div_iff hd]
  constructor <;> intro h <;> simpa [mul_comm] using h

def zeroQuery (q : List Bool) : List Bool := pair (pair (context q) []) (pairSnd q)

theorem zeroQuery_FP : zeroQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair RationalSubstitution.IntegerBits.context_mem_FP (constFn_mem_FP [])) pairSnd_mem_FP

def negateFinish (q : List Bool) : List Bool :=
  ArithmeticBits.negate (pair (BinaryNat.succ (pairSnd (pairFst q))) (pairSnd q))

theorem negateFinish_FP : negateFinish ∈ FP := by
  have hp : (fun q => pairSnd (pairFst q)) ∈ FP := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have hs := mem_FP_comp hp BinaryNat.succ_mem_FP
  have h := mem_FP_comp (mem_FP_pair hs pairSnd_mem_FP) ArithmeticBits.negate_mem_FP
  exact mem_FP_of_eq (g := negateFinish) h (fun _ => rfl)

noncomputable def value (n d : List Bool → ℤ) (q : List Bool) : List Bool :=
  if Nat.fromBitsLE (selectedDegree q) = 1 then
    PrimitivePairBits.coefficient (fun c => C (d c)) (zeroQuery q)
  else if Nat.fromBitsLE (selectedDegree q) = 0 then
    negateFinish (pair q (PrimitivePairBits.coefficient (fun c => C (n c)) (zeroQuery q)))
  else []

theorem valueEvaluator (n d : List Bool → ℤ)
    (N : SpaceFunction (PrimitivePairBits.coefficient (fun c => C (n c))))
    (D : SpaceFunction (PrimitivePairBits.coefficient (fun c => C (d c)))) : SpaceFunction (value n d) := by
  have hlo := BinaryNat.le_fppred RationalSubstitution.IntegerBits.selectedDegree_mem_FP (constFn_mem_FP [true])
  have hhi := BinaryNat.le_fppred (constFn_mem_FP [true]) RationalSubstitution.IntegerBits.selectedDegree_mem_FP
  have hone : FPPred (fun q => Nat.fromBitsLE (selectedDegree q) = 1) :=
    (hlo.and hhi).of_iff (fun _ => le_antisymm_iff.symm)
  have EN := ((N.precompose zeroQuery zeroQuery_FP).withInput).postcompose negateFinish negateFinish_FP
  have EZ := SpaceFunction.branch (fun q => decide (Nat.fromBitsLE (selectedDegree q) = 0))
    DyadicConstantBits.degreeZero_pred.flag_mem_FP EN (SpaceFunction.ofFP _ (constFn_mem_FP []))
  have E := SpaceFunction.branch (fun q => decide (Nat.fromBitsLE (selectedDegree q) = 1))
    hone.flag_mem_FP (D.precompose zeroQuery zeroQuery_FP) EZ
  refine E.congr (funext fun q => ?_)
  simp only [value, Function.comp_apply, decide_eq_true_eq]

set_option maxHeartbeats 100000 in
theorem value_eq (n d : List Bool → ℤ) (q : List Bool) :
    value n d q = PrimitivePairBits.coefficient (fun c => polynomial (n c) (d c)) q := by
  let : NeZero (mValue q) := ⟨by dsimp [mValue]; omega⟩
  have hz : Nat.fromBitsLE ([] : List Bool) = 0 := rfl
  have hm : BinaryNat.succ (pairSnd q) = BinaryNatCode.encode (mValue q) := by
    simp only [BinaryNat.succ_eq_bits, mValue, BinaryNatCode.encode]
  unfold value PrimitivePairBits.coefficient
  simp only [zeroQuery, context, selectedDegree, mValue, pairFst_pair, pairSnd_pair, hz, Polynomial.coeff_C, ite_true, coeff]
  split_ifs with h1 h0
  · rfl
  · rw [negateFinish, pairFst_pair, pairSnd_pair, hm]
    unfold coefficientResidue
    change ArithmeticBits.negate (pair (BinaryNatCode.encode (mValue q))
      (residueBits ((n (pairFst (pairFst q)) : ℤ) : ZMod (mValue q)))) = _
    rw [ArithmeticBits.negate_residueBits]
    simp only [Int.cast_neg]
  · rfl

theorem coefficientEvaluator (n d : List Bool → ℤ)
    (N : SpaceFunction (PrimitivePairBits.coefficient (fun c => C (n c))))
    (D : SpaceFunction (PrimitivePairBits.coefficient (fun c => C (d c)))) :
    SpaceFunction (PrimitivePairBits.coefficient (fun c => polynomial (n c) (d c))) :=
  (valueEvaluator n d N D).congr (funext (value_eq n d))

end LeanCanny.ETR.TubeNativeAnnihilatorPins
