/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CoerciveBoxBounds
public import LeanCanny.ETR.CoerciveSourceControls

/-! # Native source budgets for canonical symbolic coordinate annihilants

The bounds have FP binary writers; the actual annihilator coefficient readers
are separate. Out-of-range coordinates select the nonzero constant one.
-/

@[expose] public section
namespace LeanCanny.ETR.CoerciveAnnihilatorControls
open LeanCanny.Encoding LeanCanny.Algebra
open CoerciveSourceSampling CoerciveSourceControls
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def degreeBound (bits : List Bool) : ℕ :=
  CoerciveBoxGramEliminant.blockDimension (dimension bits) (degreeAllowance bits)
noncomputable def massExponent (bits : List Bool) : ℕ :=
  CoerciveBoxGramEliminant.massExponent (dimension bits) (degreeAllowance bits) (massAllowance bits)

theorem degreeBound_binary : BinaryFn degreeBound :=
  (BinaryFn.of_bits (bits_mem_FP (dimension_unary.add (UnaryFn.const 3)))).mul sourceColumnBound_binary

theorem massExponent_binary : BinaryFn massExponent :=
  (degreeBound_binary.mul
    (((BinaryFn.const 2).mul degreeBound_binary.size).add
      ((BinaryFn.const 2).mul (BinaryFn.of_bits (bits_mem_FP sourceBudgetExponent_unary))))).add
        (BinaryFn.const 1)

noncomputable def degreeCode (bits : List Bool) : List Bool := BinaryNatCode.encode (degreeBound bits)
noncomputable def massCode (bits : List Bool) : List Bool := BinaryNatCode.encode (massExponent bits)

theorem degreeCode_mem_FP : degreeCode ∈ FP := degreeBound_binary.bits_mem_FP
theorem massCode_mem_FP : massCode ∈ FP := massExponent_binary.bits_mem_FP

noncomputable def original (bits : List Bool) (i : ℕ) : Polynomial (Polynomial ℤ) :=
  if hi : i < dimension bits then CoerciveBoxGramEliminant.symbolic (polynomial bits)
    (degreeAllowance bits) ⟨i, hi⟩ else 1

theorem original_ne_zero (bits : List Bool) (i : ℕ) : original bits i ≠ 0 := by
  unfold original
  split_ifs with hi
  · exact CoerciveBoxGramEliminant.symbolic_ne_zero _ _ (polynomial_degree bits) _
  · exact one_ne_zero

theorem original_mass (bits : List Bool) (i : ℕ) :
    NestedMass.mass (original bits i) ≤ 2 ^ massExponent bits := by
  unfold original
  split_ifs
  · exact CoerciveBoxGramEliminant.symbolic_mass _ _ _ (polynomial_degree bits) (polynomial_mass bits) _
  · change NestedMass.mass (Polynomial.C (Polynomial.C 1)) ≤ _
    simpa only [NestedMass.C, coefficientMass_C, show (1 : ℤ).natAbs = 1 from rfl] using Nat.one_le_two_pow (n := massExponent bits)

theorem original_coefficient_mass (bits : List Bool) (i k : ℕ) :
    coefficientMass ((original bits i).coeff k) ≤ 2 ^ massExponent bits :=
  (NestedMass.coeff_le _ _).trans (original_mass bits i)

theorem original_degree (bits : List Bool) (i : ℕ) : (original bits i).natDegree ≤ degreeBound bits := by
  unfold original
  split_ifs
  · exact CoerciveBoxGramEliminant.symbolic_degree _ _ (polynomial_degree bits) _
  · simp only [Polynomial.natDegree_one, Nat.zero_le]

theorem original_inner_degree (bits : List Bool) (i k : ℕ) :
    ((original bits i).coeff k).natDegree ≤ degreeBound bits := by
  unfold original
  split_ifs
  · exact CoerciveBoxGramEliminant.symbolic_inner_degree _ _ (polynomial_degree bits) _ _
  · rw [Polynomial.coeff_one]
    split_ifs <;> simp only [Polynomial.natDegree_one, Polynomial.natDegree_zero, Nat.zero_le]

end LeanCanny.ETR.CoerciveAnnihilatorControls
