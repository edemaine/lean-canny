/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalCoordinateProductSpace
public import LeanCanny.Algebra.ModularSumSpace

/-! # Native sums of actual cleared Euler gradient terms

The original free-coordinate ranks are scanned once and the objective
coordinate is omitted. Each remaining X_j*g_j coefficient is computed
from the original source, retained heights, and common denominator.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralEulerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

structure Source extends toGradient : IntegralCriticalGradientBits.Source where
  objective : ∀ c, Fin (free c)

structure Access (S : Source) extends toGradient : IntegralCriticalGradientBits.Access S.toGradient where
  objective : BinaryFn (fun c => (S.objective c).val)

def termQuery (S : Source) (p : List Bool) : List Bool :=
  pair (pairFst p) (pair (pairSnd p) (BinaryNatCode.encode (S.target (pairFst p))))

theorem termQuery_FP (S : Source) (a : Access S) : termQuery S ∈ FP := by
  have HT : BinaryFn (fun p => S.target (pairFst p)) := a.target.comp pairFst_mem_FP
  exact mem_FP_pair pairFst_mem_FP (mem_FP_pair pairSnd_mem_FP HT.bits_mem_FP)

def objectiveRank (S : Source) (c : List Bool) : ℕ := (S.objective c).val

def excluded (S : Source) (p : List Bool) : Prop := Nat.fromBitsLE (pairSnd p) = objectiveRank S (pairFst p)
instance (S : Source) (p : List Bool) : Decidable (excluded S p) := inferInstanceAs (Decidable (_ = _))

theorem excluded_fppred (S : Source) (a : Access S) : FPPred (excluded S) :=
  (BinaryFn.fromBits pairSnd_mem_FP).eq (a.objective.comp pairFst_mem_FP)

noncomputable def termProgram (S : Source) (p : List Bool) : List Bool :=
  if excluded S p then [] else IntegralCriticalCoordinateProductBits.value S.toGradient (termQuery S p)

theorem term_evaluator (S : Source) (a : Access S) (EC : SpaceFunction a.coefficient)
    (EH : SpaceFunction a.height) (EQ : SpaceFunction a.denominator) : SpaceFunction (termProgram S) :=
  (SpaceFunction.branch (fun p => decide (excluded S p)) (excluded_fppred S a).flag_mem_FP
    (SpaceFunction.ofFP _ (constFn_mem_FP []))
    ((IntegralCriticalCoordinateProductBits.evaluator S.toGradient a.toGradient EC EH EQ).precompose
      (termQuery S) (termQuery_FP S a))).congr
        (funext fun _ => by simp only [termProgram, Function.comp_apply, decide_eq_true_eq])

noncomputable def Source.targetExponent (S : Source) (c : List Bool) : Fin (S.free c) →₀ ℕ :=
  RationalSubstitution.Indexed.exponentVector (S.free c) (FixedWidthPolynomial.entry (S.targetWidth c) (S.target c))

noncomputable def Source.sumPolynomial (S : Source) (c : List Bool) :
    letI := S.ring c
    MvPolynomial (Fin (S.free c)) (S.carrier c) := by
  letI := S.ring c
  exact ∑ j : Fin (S.free c), if j = S.objective c then 0
    else MvPolynomial.X j * IntegralCriticalGradientBits.polynomial S.toGradient c j

noncomputable def Source.summand (S : Source) (c : List Bool) (i : ℕ) : ℤ := by
  letI := S.ring c
  exact if hi : i < S.free c then Algebra.leftMulMatrix (S.basis c)
    ((if i = objectiveRank S c then 0 else MvPolynomial.X (⟨i, hi⟩ : Fin (S.free c)) *
      IntegralCriticalGradientBits.polynomial S.toGradient c ⟨i, hi⟩).coeff (S.targetExponent c)) (S.row c) (S.col c)
    else 0

noncomputable def Source.sumValue (S : Source) (c : List Bool) : List Bool := by
  letI := S.ring c
  exact residueBits ((Algebra.leftMulMatrix (S.basis c)
    ((S.sumPolynomial c).coeff (S.targetExponent c)) (S.row c) (S.col c) : ℤ) : ZMod (S.modulus c))

theorem term_packet (S : Source) (c : List Bool) (i : Fin (S.free c)) :
    termProgram S (pair c (BinaryNatCode.encode i.val)) = residueBits (S.summand c i.val : ZMod (S.modulus c)) := by
  let := S.ring c
  unfold termProgram Source.summand
  simp only [excluded, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [dite_eq_left i.isLt]
  by_cases h : i.val = objectiveRank S c
  · rw [ite_eq_left h, ite_eq_left h]
    simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, map_zero, Matrix.zero_apply,
      Int.cast_zero, residueBits, ZMod.val_zero, BinaryNatCode.encode, Nat.zero_bits]
  · rw [ite_eq_right h, ite_eq_right h]
    simp only [termQuery, pairFst_pair, pairSnd_pair]
    exact IntegralCriticalCoordinateProductBits.packet S.toGradient c i (S.target c)

theorem sum_summands (S : Source) (c : List Bool) :
    letI := S.ring c
    (∑ i ∈ Finset.range (S.free c), S.summand c i) =
      Algebra.leftMulMatrix (S.basis c) ((S.sumPolynomial c).coeff (S.targetExponent c)) (S.row c) (S.col c) := by
  let := S.ring c
  rw [Finset.sum_range, Source.sumPolynomial, MvPolynomial.coeff_sum, map_sum, Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  unfold Source.summand
  rw [dite_eq_left j.isLt]
  have HE : (j.val = objectiveRank S c) ↔ j = S.objective c := Fin.ext_iff.symm
  simp only [HE]

theorem sum_value (S : Source) (c : List Bool) :
    residueBits (∑ i ∈ Finset.range (S.free c), (S.summand c i : ZMod (S.modulus c))) = S.sumValue c := by
  let := S.ring c
  rw [← Int.cast_sum, sum_summands]
  rfl

attribute [local irreducible] Source.sumValue termProgram

theorem sum_evaluator (S : Source) (a : Access S) (EC : SpaceFunction a.coefficient)
    (EH : SpaceFunction a.height) (EQ : SpaceFunction a.denominator) : SpaceFunction S.sumValue := by
  have E := term_evaluator S a EC EH EQ
  have HM : (fun c => BinaryNatCode.encode (S.modulus c)) ∈ FP := a.modulus.bits_mem_FP
  have HV : (fun c => Nat.fromBitsLE (BinaryNatCode.encode (S.modulus c))) = S.modulus :=
    funext (fun c => Nat.fromBitsLE_bits _)
  have H := ModularSum.evaluatorWithModulus E (fun c => BinaryNatCode.encode (S.free c))
    (fun c => BinaryNatCode.encode (S.modulus c)) (bits_mem_FP a.free) HM S.modulus HV
    (fun c i => (S.summand c i : ZMod (S.modulus c)))
    (fun c => Nat.pos_of_ne_zero (S.modulus_ne_zero c)) (fun c i hi => term_packet S c ⟨i, by simpa only [BinaryNatCode.encode, Nat.fromBitsLE_bits] using hi⟩)
  refine H.congr (funext fun c => ?_)
  rw [BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact sum_value S c

end LeanCanny.Algebra.IntegralEulerBits
