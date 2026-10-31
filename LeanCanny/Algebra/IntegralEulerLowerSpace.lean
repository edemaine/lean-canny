/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralEulerObjectiveSpace

/-! # Native selection of actual cleared Euler lower rows

The objective row uses the constructed Euler objective; every other row
uses its original-coordinate derivative cleared at the original allowance.
Both branches retain the same original source and all original reader costs.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralEulerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

theorem sumPolynomial_eq_erase (S : Source) (c : List Bool) :
    letI := S.ring c
    S.sumPolynomial c = ∑ j ∈ Finset.univ.erase (S.objective c),
      MvPolynomial.X j * IntegralCriticalGradientBits.polynomial S.toGradient c j := by
  let := S.ring c
  let f := fun j : Fin (S.free c) => if j = S.objective c then 0
    else MvPolynomial.X j * IntegralCriticalGradientBits.polynomial S.toGradient c j
  have H : (∑ j ∈ Finset.univ.erase (S.objective c), f j) + f (S.objective c) = ∑ j, f j :=
    Finset.sum_erase_add _ _ (Finset.mem_univ (S.objective c))
  change (∑ j, f j) = _
  rw [← H, show f (S.objective c) = 0 from ite_eq_left rfl, add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  exact ite_eq_right (Finset.mem_erase.mp hj).1

noncomputable def Source.lowerPolynomial (S : Source) (c : List Bool) (i : Fin (S.free c)) :
    letI := S.ring c
    MvPolynomial (Fin (S.free c)) (S.carrier c) := by
  letI := S.ring c
  exact if i = S.objective c then S.objectivePolynomial c else IntegralCriticalGradientBits.polynomial S.toGradient c i

noncomputable def Source.lowerValue (S : Source) (i : ∀ c, Fin (S.free c)) (c : List Bool) : List Bool := by
  letI := S.ring c
  exact residueBits ((Algebra.leftMulMatrix (S.basis c)
    ((S.lowerPolynomial c (i c)).coeff (S.targetExponent c)) (S.row c) (S.col c) : ℤ) : ZMod (S.modulus c))

def lowerGradientQuery (S : Source) (i : ∀ c, Fin (S.free c)) (c : List Bool) : List Bool :=
  pair c (pair (BinaryNatCode.encode (i c).val) (BinaryNatCode.encode (S.target c)))

theorem lowerGradientQuery_FP (S : Source) (a : Access S) (i : ∀ c, Fin (S.free c))
    (hi : BinaryFn (fun c => (i c).val)) : lowerGradientQuery S i ∈ FP :=
  mem_FP_pair id_mem_FP (mem_FP_pair hi.bits_mem_FP a.target.bits_mem_FP)

theorem lower_value (S : Source) (i : ∀ c, Fin (S.free c)) (c : List Bool) :
    (if (i c).val = objectiveRank S c then S.objectiveValue c
      else (IntegralCriticalGradientBits.family S.toGradient).value (lowerGradientQuery S i c)) = S.lowerValue i c := by
  let := S.ring c
  have HE : ((i c).val = objectiveRank S c) ↔ i c = S.objective c := Fin.ext_iff.symm
  simp only [HE]
  by_cases h : i c = S.objective c
  · rw [ite_eq_left h]
    unfold Source.lowerValue Source.lowerPolynomial
    rw [ite_eq_left h]
    rfl
  · rw [ite_eq_right h]
    unfold lowerGradientQuery
    rw [IntegralCriticalGradientBits.packet]
    unfold Source.lowerValue Source.lowerPolynomial
    rw [ite_eq_right h]
    rfl

attribute [local irreducible] Source.lowerValue Source.objectiveValue

theorem lower_evaluator (S : Source) (a : Access S) (i : ∀ c, Fin (S.free c))
    (hi : BinaryFn (fun c => (i c).val)) (EC : SpaceFunction a.coefficient)
    (EH : SpaceFunction a.height) (EQ : SpaceFunction a.denominator) (EA : SpaceFunction a.leading) :
    SpaceFunction (S.lowerValue i) := by
  have EO := objective_evaluator S a EC EH EQ EA
  have EG := (IntegralCriticalGradientBits.evaluator S.toGradient a.toGradient EC EH EQ).precompose
    (lowerGradientQuery S i) (lowerGradientQuery_FP S a i hi)
  have HB : FPPred (fun c => (i c).val = objectiveRank S c) := hi.eq a.objective
  refine (SpaceFunction.branch (fun c => decide ((i c).val = objectiveRank S c)) HB.flag_mem_FP EO EG).congr ?_
  funext c
  simp only [decide_eq_true_eq]
  exact lower_value S i c

end LeanCanny.Algebra.IntegralEulerBits
