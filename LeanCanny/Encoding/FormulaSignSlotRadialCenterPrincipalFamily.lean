/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialCenterSquarefreeSelection
public import LeanCanny.Algebra.MultivariateTarskiDegreeBounds
/-! # The actual formal-center principal family and its original degree box

The first coefficient variable is radius, followed by the unchanged center
variables. Context contains the original eliminant context, tau and the
declared degree; the degree need not equal its symbolic value.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialCenterPrincipalFamily
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation Polynomial PrincipalSubresultant
open FormulaSignSlotCenteredRadialGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotRadialFormalEliminant.eliminant

def original (c : List Bool) := pairFst c
def tau (c : List Bool) := Nat.fromBitsLE (pairFst (pairSnd c))
def degree (c : List Bool) := Nat.fromBitsLE (pairSnd (pairSnd c))
noncomputable def arity (c : List Bool) := d (pairFst (original c)) + 1
noncomputable def inputBound (c : List Bool) := FormulaSignSlotRadialCenterSelection.bound (original c)
noncomputable def degreeBound (c : List Bool) := (degree c + (degree c - 1) + 1) * inputBound c
noncomputable def width (c : List Bool) := (degreeBound c + inputBound c).size

local instance centerPrincipalFamilyArityNeZero (c : List Bool) : NeZero (arity c) :=
  ⟨by unfold arity; omega⟩

theorem original_FP : original ∈ FP := pairFst_mem_FP
theorem tau_binary : BinaryFn tau := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
theorem degree_binary : BinaryFn degree := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
theorem arity_unary : UnaryFn arity :=
  ((FormulaSignSlotSource.dimension_unary.comp (mem_FP_comp original_FP pairFst_mem_FP)).add (UnaryFn.const 1))
theorem inputBound_binary : BinaryFn inputBound := FormulaSignSlotRadialEliminantFormalMass.degree_binary.comp original_FP
theorem degreeBound_binary : BinaryFn degreeBound :=
  ((degree_binary.add (degree_binary.sub (BinaryFn.const 1))).add (BinaryFn.const 1)).mul inputBound_binary
theorem width_unary : UnaryFn width :=
  (UnaryFn.length (degreeBound_binary.add inputBound_binary).bits_mem_FP).of_eq (fun _ => BinaryNatCode.length_encode _)

noncomputable def polynomial (c : List Bool) : Polynomial (MvPolynomial (Fin (arity c)) ℤ) :=
  (FormulaSignSlotRadialCenterSquarefreeSelection.polynomial (original c) (tau c) (degree c)).map
    TriplePolynomialParameterFlatten.one

theorem coefficient (c : List Bool) (j r : ℕ) (v : Fin (d (pairFst (original c))) →₀ ℕ) :
    ((polynomial c).coeff j).coeff (v.cons r) =
      if j ≤ degree c then (FormulaSignSlotRadialCenterCoefficient.polynomial (original c) (tau c) j r).coeff v else 0 := by
  dsimp only [polynomial, arity]
  rw [Polynomial.coeff_map, TriplePolynomialParameterFlatten.one_coefficient,
    FormulaSignSlotRadialCenterSquarefreeSelection.polynomial,
    FormulaSignSlotRadialCenterSquarefreeSelection.truncate_coefficient]
  split_ifs
  · rfl
  · simp

theorem polynomial_degree (c : List Bool) (j : ℕ) : ((polynomial c).coeff j).totalDegree ≤ inputBound c := by
  rw [MvPolynomial.totalDegree]
  apply Finset.sup_le
  intro e he
  have HC := MvPolynomial.mem_support_iff.mp he
  dsimp only [arity] at e
  have HE := coefficient c j (e 0) e.tail
  simp only [Finsupp.cons_tail] at HE
  rw [HE] at HC
  by_cases hj : j ≤ degree c
  · rw [ite_eq_left hj] at HC
    have HH := FormulaSignSlotRadialCenterCoefficient.coefficient_weight (original c) (tau c) j (e 0) e.tail HC
    have HS : e.sum (fun _ x => x) = e 0 + e.tail.sum (fun _ x => x) := by
      simpa only [Finsupp.cons_tail] using (Finsupp.sum_cons _ e.tail (e 0))
    change e.sum (fun _ x => x) ≤ inputBound c
    rw [HS]
    change _ ≤ FormulaSignSlotRadialEliminantPacked.resultDegree (original c)
    omega
  · rw [ite_eq_right hj] at HC
    exact (HC rfl).elim

theorem input_fit (c : List Bool) : inputBound c < 2 ^ width c :=
  (Nat.le_add_left _ _).trans_lt (Nat.lt_size_self _)

noncomputable def principal (c : List Bool) (j : ℕ) : MvPolynomial (Fin (arity c)) ℤ :=
  signedPsc (polynomial c) (polynomial c).derivative (degree c) (degree c - 1) j

theorem principal_degree (c : List Bool) (j : ℕ) : (principal c j).totalDegree ≤ degreeBound c :=
  MultivariateTarskiDegreeBounds.principal _ _ _ _ _ _ (polynomial_degree c)
    (MultivariateTarskiDegreeBounds.derivative_coefficient _ _ (polynomial_degree c))

theorem principal_fit (c : List Bool) (j : ℕ) : (principal c j).totalDegree < 2 ^ width c :=
  (principal_degree c j).trans_lt ((Nat.le_add_right _ _).trans_lt (Nat.lt_size_self _))

theorem principal_map (c : List Bool) (j : ℕ) :
    principal c j = TriplePolynomialParameterFlatten.one
      (signedPsc (FormulaSignSlotRadialCenterSquarefreeSelection.polynomial (original c) (tau c) (degree c))
        (FormulaSignSlotRadialCenterSquarefreeSelection.polynomial (original c) (tau c) (degree c)).derivative
          (degree c) (degree c - 1) j) := by
  dsimp only [principal, polynomial, arity]
  rw [Polynomial.derivative_map, signedPsc_map_map]

end LeanCanny.Encoding.FormulaSignSlotRadialCenterPrincipalFamily
