/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerPlan
public import LeanCanny.Encoding.BoundedRegularLowHeight
public import LeanCanny.Algebra.IntegralMixedSourceIntegerBounds
/-! # Native original-only height inputs for the actual marked integer plan -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerPlan
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFramedStepHeight
open IntegralMixedAuxiliaryMarkedIntegerSource (number original)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def readers (n : List Bool → ℕ) (t : List Bool → Term) (R : List Bool → ℕ) :=
  BoundedRegularLowCoefficient.readers (number n) (t∘original) R

theorem readers_native {n : List Bool → ℕ} {t : List Bool → Term} {R : List Bool → ℕ}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (hR : BinaryFn R) : (readers n t R).PolyTime :=
  BoundedRegularLowCoefficient.readers_native (IntegralMixedAuxiliaryMarkedIntegerSource.number_unary hn)
    (mem_FP_comp original_FP ht) hR

noncomputable def integerMass {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool → ℕ} (hR : BinaryFn R) :=
  IntegerPolynomialFiniteMassEnvelope.height (IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R)
    (IntegralMixedAuxiliaryMarkedIntegerSource.access hn ht ha hR) (fun c=>number n c+8)
    ((IntegralMixedAuxiliaryMarkedIntegerSource.number_unary hn).add (UnaryFn.const 8))

noncomputable def seed {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool → ℕ} (hR : BinaryFn R) (root : List Bool) :=
  integerMass hn ht ha hR root+BoundedRegularLowHeight.height (readers n t R) root

theorem seed_binary {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool → ℕ} (hR : BinaryFn R) : BinaryFn (seed hn ht ha hR) :=
  (IntegerPolynomialFiniteMassEnvelope.height_binary _ _ _ _).add
    (BoundedRegularLowHeight.height_binary (readers_native hn ht hR))

theorem default_height {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool → ℕ} (hR : BinaryFn R) (root : List Bool) :
    InstructionBounds (seed hn ht ha hR root+1) 1 ((parameters hn ht ha).sourceWidth root)
      ((parameters hn ht ha).degree root) 1
      (IntegralMixedFramedHistoryFamilyBits.defaultInstruction (parameters hn ht ha) (plan hn ht ha R) root) := by
  dsimp only [IntegralMixedFramedHistoryFamilyBits.defaultInstruction,plan,IntegralMixedSourceIntegerPrelude.plan]
  have HS : BoundedRegularLowHeight.height (readers n t R) root≤seed hn ht ha hR root := Nat.le_add_left _ _
  constructor
  · intro e
    exact (BoundedRegularLowHeight.coefficient (readers n t R) root e).trans
      (Nat.pow_le_pow_right (by decide) (by omega))
  · change (BoundedRegularLowModularTerm.source (readers n t R) root).leading.natAbs.size≤_
    rw [BoundedRegularLowHeight.leading (readers n t R)]
    have HL : BoundedFullWriter.regularizationExponent (readers n t R) root+1≤BoundedRegularLowHeight.height (readers n t R) root := by
      unfold BoundedRegularLowHeight.height
      omega
    omega
  · rw [spatial_degree]
    exact le_rfl
  · rw [spatial_degree]
    exact le_rfl
  · rw [spatial_degree]
    exact IntegralMixedSourceIntegerPrelude.source_cap _ _ _ _ root
  · intro k
    rw [Polynomial.coeff_X]
    split_ifs
    · simpa only [Int.natAbs_one] using (Nat.one_le_two_pow (n:=1*(seed hn ht ha hR root+1)+1))
    · exact Nat.zero_le _

theorem familyInputs {n : List Bool → ℕ} {t : List Bool → Term}
    (hn : UnaryFn n) (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
    {R : List Bool → ℕ} (hR : BinaryFn R) :
    FamilyInputs (parameters hn ht ha) (plan hn ht ha R) (fun _=>1) (fun _=>1) (seed hn ht ha hR) := by
  apply IntegralMixedSourceIntegerPrelude.family_inputs
  · exact default_height hn ht ha hR
  · intro root j hj
    have H:=IntegerPolynomialFiniteMassEnvelope.mass_le
      (IntegralMixedAuxiliaryMarkedIntegerSource.source hn ht ha R)
      (IntegralMixedAuxiliaryMarkedIntegerSource.access hn ht ha hR)
      (fun c=>number n c+8) ((IntegralMixedAuxiliaryMarkedIntegerSource.number_unary hn).add (UnaryFn.const 8)) root j hj
    change _≤ integerMass hn ht ha hR root at H
    unfold seed
    omega

end LeanCanny.Encoding.IntegralMixedAuxiliaryMarkedIntegerPlan
