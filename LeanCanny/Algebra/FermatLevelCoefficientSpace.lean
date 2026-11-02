/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.FermatLevelCoefficientGuards
public import LeanCanny.Algebra.IntegralOriginalTermCoefficientSpace
public import LeanCanny.Algebra.FixedWidthRowArithmetic
/-! # Original level coefficients need only the old reader and one charged integer

The large original coefficient A is consumed modulo the requested positive
modulus. It is never serialized as a literal term. The old packet keeps its
exact exponent word; the old arity ignores the appended last block.
-/
@[expose] public section
namespace LeanCanny.Algebra.FermatLevelCoefficientBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower MvPolynomial
open scoped Classical

noncomputable def polynomial (N : List Bool → ℕ)
    (old : (q : List Bool) → MvPolynomial (Fin (N q)) ℤ) (A : List Bool → ℤ) (q : List Bool) :
    MvPolynomial (Fin (N q+1)) ℤ := rename Fin.castSucc (old q) - C (A q)*X (Fin.last (N q))

def finish (M : List Bool → ℕ) (z : List Bool) : List Bool :=
  ArithmeticBits.addMod (pair (BinaryNatCode.encode (M (pairFst (pairFst z))))
    (pair (pairFst (pairSnd z))
      (ArithmeticBits.negate (pair (BinaryNatCode.encode (M (pairFst (pairFst z)))) (pairSnd (pairSnd z))))))

attribute [local irreducible] ArithmeticBits.addMod ArithmeticBits.negate

theorem finish_FP {M : List Bool → ℕ} (hM : BinaryFn M) : finish M ∈ FP := by
  have HM : BinaryFn (fun z => M (pairFst (pairFst z))) := hM.comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  have HN := mem_FP_comp (mem_FP_pair HM.bits_mem_FP (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)) ArithmeticBits.negate_mem_FP
  exact mem_FP_comp (mem_FP_pair HM.bits_mem_FP (mem_FP_pair (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) HN)) ArithmeticBits.addMod_mem_FP

theorem finish_packet (M : List Bool → ℕ) (p : List Bool) (x y : ℤ) (hM : M (pairFst p) ≠ 0) :
    finish M (pair p (pair (residueBits (x : ZMod (M (pairFst p)))) (residueBits (y : ZMod (M (pairFst p)))))) =
      residueBits ((x-y : ℤ) : ZMod (M (pairFst p))) := by
  let : NeZero (M (pairFst p)) := ⟨hM⟩
  unfold finish
  simp only [pairFst_pair, pairSnd_pair]
  rw [ArithmeticBits.negate_residueBits, ArithmeticBits.addMod_residueBits]
  apply congrArg residueBits
  simp only [sub_eq_add_neg, Int.cast_add, Int.cast_neg]

theorem evaluator (N W M : List Bool → ℕ) (hN : UnaryFn N) (hW : UnaryFn W) (hM : BinaryFn M)
    (hpos : ∀ q, M q ≠ 0) (old : (q : List Bool) → MvPolynomial (Fin (N q)) ℤ) (A : List Bool → ℤ)
    (EO : SpaceFunction (IntegralOriginalTermCoefficientBits.scalar N W M old))
    (EA : SpaceFunction (fun q => residueBits (A q : ZMod (M q)))) :
    SpaceFunction (IntegralOriginalTermCoefficientBits.scalar (fun q => N q+1) W M (polynomial N old A)) := by
  have EZ : SpaceFunction (fun _ : List Bool => ([] : List Bool)) := SpaceFunction.ofFP _ (constFn_mem_FP [])
  have EL := SpaceFunction.branch (fun p => decide (lastExponent N W p = 0))
    ((lastExponent_binary hN hW).eq (BinaryFn.const 0)).flag_mem_FP EO EZ
  have ER := SpaceFunction.branch (fun p => decide (IsLast N W p)) (isLast_fppred hN hW).flag_mem_FP
    (EA.precompose pairFst pairFst_mem_FP) EZ
  have H := (EL.pairOutputs ER).withInput.postcompose (finish M) (finish_FP hM)
  apply H.congr
  funext p
  let q := pairFst p
  let k := Nat.fromBitsLE (pairSnd p)
  have HL : (if decide (lastExponent N W p = 0) then IntegralOriginalTermCoefficientBits.scalar N W M old p else []) =
      residueBits ((if FixedWidthPolynomial.entry (W q) k (N q) = 0 then
        (old q).coeff (RationalSubstitution.Indexed.exponentVector (N q) (FixedWidthPolynomial.entry (W q) k)) else 0 : ℤ) : ZMod (M q)) := by
    by_cases hz : lastExponent N W p = 0
    · rw [ite_eq_left (decide_eq_true hz)]
      change FixedWidthPolynomial.entry (W q) k (N q) = 0 at hz
      rw [ite_eq_left hz]
      rfl
    · rw [ite_eq_right (by simpa only [decide_eq_true_eq] using hz)]
      change FixedWidthPolynomial.entry (W q) k (N q) ≠ 0 at hz
      rw [ite_eq_right hz]
      simp [residueBits]
  have HR : (if decide (IsLast N W p) then (fun q => residueBits (A q : ZMod (M q))) (pairFst p) else []) =
      residueBits ((if FermatLevelCoefficient.IsLast (N q) (W q) k then A q else 0 : ℤ) : ZMod (M q)) := by
    by_cases hz : IsLast N W p
    · rw [ite_eq_left (decide_eq_true hz)]
      change FermatLevelCoefficient.IsLast (N q) (W q) k at hz
      rw [ite_eq_left hz]
    · rw [ite_eq_right (by simpa only [decide_eq_true_eq] using hz)]
      change ¬FermatLevelCoefficient.IsLast (N q) (W q) k at hz
      rw [ite_eq_right hz]
      simp [residueBits]
  change finish M (pair p (pair _ _)) = _
  simp only [Function.comp_apply]
  rw [HL, HR, finish_packet M p _ _ (hpos q)]
  unfold IntegralOriginalTermCoefficientBits.scalar polynomial
  rw [FermatLevelCoefficient.coefficient]

theorem value_length (N W M : List Bool → ℕ) (old : (q : List Bool) → MvPolynomial (Fin (N q)) ℤ)
    (A : List Bool → ℤ) (p : List Bool) (hpos : M (pairFst p) ≠ 0) :
    (IntegralOriginalTermCoefficientBits.scalar (fun q => N q+1) W M (polynomial N old A) p).length ≤
      (M (pairFst p)).size := by
  let : NeZero (M (pairFst p)) := ⟨hpos⟩
  exact residueBits_length_le _ _

end LeanCanny.Algebra.FermatLevelCoefficientBits
