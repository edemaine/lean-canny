/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.CoerciveNativeAnnihilators
public import LeanCanny.Algebra.SymbolicFixedTableFinite

/-! # A native FP reference exponent for the actual coercive originals -/

@[expose] public section
namespace LeanCanny.ETR.CoercivePreparationControls
open LeanCanny.Encoding LeanCanny.Algebra
open CoerciveSourceSampling
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] RationalSubstitutionBits.compiledTerm

noncomputable def budget (bits : List Bool) : SymbolicFixedTable.Budget :=
  ⟨CoerciveNativeAnnihilators.degreeBound bits, CoerciveNativeAnnihilators.degreeBound bits,
    CoerciveNativeAnnihilators.massExponent bits⟩

theorem budget_controls (bits : List Bool) (i : ℕ) :
    (budget bits).Controls (CoerciveNativeAnnihilators.original bits i) :=
  ⟨CoerciveNativeAnnihilators.original_degree bits i,
    CoerciveNativeAnnihilators.original_inner_degree bits i,
    CoerciveNativeAnnihilators.original_coefficient_mass bits i⟩

/-- The actual finite original family, including the perturbation pin.
The verified finite wrapper supplies X padding beyond its count. -/
noncomputable def family (bits : List Bool) : SymbolicFixedTableFinite.Family where
  count := dimension bits + 1
  polynomial := CoerciveNativeAnnihilators.original bits
  budget := budget bits
  controls i _ := budget_controls bits i
  nonzero i _ := CoerciveNativeAnnihilators.original_ne_zero bits i

noncomputable def referenceExponent (bits : List Bool) : ℕ := (family bits).exponent

theorem referenceExponent_binary : BinaryFn referenceExponent := by
  have h := SymbolicFixedTable.sourceExponent_binary
    (CoerciveNativeAnnihilators.degreeBound_binary.add (BinaryFn.const 1))
    CoerciveNativeAnnihilators.degreeBound_binary CoerciveNativeAnnihilators.massExponent_binary
    (dimension_unary.add (UnaryFn.const 1))
  apply BinaryFn.of_bits
  apply mem_FP_of_eq h.bits_mem_FP
  intro bits
  rw [referenceExponent, SymbolicFixedTableFinite.Family.exponent_eq]
  rfl

noncomputable def referenceCode (bits : List Bool) : List Bool := BinaryNatCode.encode (referenceExponent bits)
theorem referenceCode_mem_FP : referenceCode ∈ FP := referenceExponent_binary.bits_mem_FP

theorem preparation_le_reference (bits : List Bool) :
    SymbolicFixedTable.preparationExponent (family bits).paddedBudget (dimension bits + 1).size ≤ referenceExponent bits :=
  SymbolicFixedTable.preparationExponent_le_source (family bits).paddedBudget (dimension bits + 1)

end LeanCanny.ETR.CoercivePreparationControls
