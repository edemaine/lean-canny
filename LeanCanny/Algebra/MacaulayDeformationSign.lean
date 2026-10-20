/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayDeformationResidue
public import LeanCanny.Algebra.IntegerSignumSpace
public import LeanCanny.Algebra.IntegerZeroSpace

/-! # Integer signs of deformation determinant coefficients in polynomial space

The concrete residue evaluator and the proved determinant coefficient budget
supply three-way signs and integer zero/strict-sign tests. The only source
coefficient oracle is the certified original integer polynomial residue reader.
Identifying the required eliminant coefficient remains a separate obligation.
-/

@[expose] public section

namespace LeanCanny.Algebra.MacaulayDeformationBits
open Complexity
open LeanCanny.Encoding LeanCanny.Computation
open LeanCanny.Encoding.Brackets

theorem Family.polynomial_ne_zero (F : Family) (c : List Bool) : F.polynomial c ≠ 0 :=
  Macaulay.det_deformation_ne_zero _ _ _

def Family.budget (F : Family) (c : List Bool) : ℕ :=
  (FixedWidthPolynomial.count (F.source.layout.arity c) (F.source.layout.width c)).size *
    FixedWidthPolynomial.count (F.source.layout.arity c) (F.source.layout.width c) +
    FixedWidthPolynomial.count (F.source.layout.arity c) (F.source.layout.width c) * (F.source.coefficientBits c + 2) + 1

theorem Family.coefficient_bits (F : Family) (c : List Bool) :
    (F.coefficient c).natAbs.size ≤ F.budget c :=
  Macaulay.det_deformation_coefficient_size_le _ _ _ _ (F.source.bound c) _

noncomputable def Family.signValue (F : Family) (c : List Bool) : List Bool :=
  if F.coefficient c = 0 then [] else if F.coefficient c < 0 then [true] else [false, true]

def Family.zeroLanguage (F : Family) : Language := {c | F.coefficient c = 0}
def Family.negativeLanguage (F : Family) : Language := {c | F.coefficient c < 0}
def Family.positiveLanguage (F : Family) : Language := {c | 0 < F.coefficient c}

def Access.sourceBudget {F : Family} (a : Access F) (c : List Bool) : List Bool :=
  BinaryNat.add (pair (a.original.bits c) (BinaryNatCode.encode 2))

def Access.budget {F : Family} (a : Access F) : List Bool → List Bool :=
  MacaulayBits.budgetCode F.source.layout a.sourceBudget

theorem Access.sourceBudget_mem_FP {F : Family} (a : Access F) (hb : a.original.bits ∈ FP) : a.sourceBudget ∈ FP := by
  have hq := mem_FP_pair hb (constFn_mem_FP (BinaryNatCode.encode 2))
  have hf := mem_FP_comp hq BinaryNat.add_mem_FP
  exact mem_FP_of_eq (g := a.sourceBudget) hf (fun _ => rfl)

theorem Access.budget_mem_FP {F : Family} (a : Access F) (h : F.source.layout.PolyTime)
    (hb : a.original.bits ∈ FP) : a.budget ∈ FP :=
  MacaulayBits.budgetCode_mem_FP h (a.sourceBudget_mem_FP hb)

theorem Access.budget_code {F : Family} (a : Access F) (c : List Bool) :
    a.budget c = BinaryNatCode.encode (F.budget c) := by
  apply MacaulayBits.budgetCode_code F.source.layout a.sourceBudget (fun c => F.source.coefficientBits c + 2)
  intro z
  simp only [Access.sourceBudget, BinaryNat.add_pair, a.original.bits_eq, MacaulayBits.fromBits_encode]
  rfl

theorem Access.coefficient_bit_bound {F : Family} (a : Access F) (c : List Bool) :
    (F.coefficient c).natAbs.size ≤ Nat.fromBitsLE (a.budget c) := by
  rw [a.budget_code, MacaulayBits.fromBits_encode]
  exact F.coefficient_bits c

noncomputable def Access.signumEvaluator {F : Family} (a : Access F) (h : F.source.layout.PolyTime)
    (hd : a.degree ∈ FP) (hb : a.original.bits ∈ FP) (E : SpaceFunction a.original.coefficient) :
    SpaceFunction F.signValue :=
  IntegerSignumBits.evaluator (a.evaluator h hd E) a.budget (a.budget_mem_FP h hb)
    F.coefficient a.coefficient_bit_bound F.value_packet

noncomputable def Access.zeroDecider {F : Family} (a : Access F) (h : F.source.layout.PolyTime)
    (hd : a.degree ∈ FP) (hb : a.original.bits ∈ FP) (E : SpaceFunction a.original.coefficient) :
    SpaceDecider F.zeroLanguage :=
  IntegerZeroBits.zeroDecider (a.evaluator h hd E) a.budget (a.budget_mem_FP h hb)
    F.coefficient a.coefficient_bit_bound F.value_packet

theorem Access.zeroLanguage_mem_PSPACE {F : Family} (a : Access F) (h : F.source.layout.PolyTime)
    (hd : a.degree ∈ FP) (hb : a.original.bits ∈ FP) (E : SpaceFunction a.original.coefficient) :
    F.zeroLanguage ∈ PSPACE := (a.zeroDecider h hd hb E).mem_PSPACE

theorem Access.negativeLanguage_mem_PSPACE {F : Family} (a : Access F) (h : F.source.layout.PolyTime)
    (hd : a.degree ∈ FP) (hb : a.original.bits ∈ FP) (E : SpaceFunction a.original.coefficient) :
    F.negativeLanguage ∈ PSPACE := by
  have hf := (stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  apply ((a.signumEvaluator h hd hb E).decider (fun w => decide (w = [true])) hf ?_).mem_PSPACE
  intro c
  by_cases hz : F.coefficient c = 0 <;> by_cases hn : F.coefficient c < 0 <;>
    simp [Family.negativeLanguage, Family.signValue, hz, hn]

theorem Access.positiveLanguage_mem_PSPACE {F : Family} (a : Access F) (h : F.source.layout.PolyTime)
    (hd : a.degree ∈ FP) (hb : a.original.bits ∈ FP) (E : SpaceFunction a.original.coefficient) :
    F.positiveLanguage ∈ PSPACE := by
  have hf := (stringEq_fppred id_mem_FP (constFn_mem_FP [false, true])).flag_mem_FP
  apply ((a.signumEvaluator h hd hb E).decider (fun w => decide (w = [false, true])) hf ?_).mem_PSPACE
  intro c
  by_cases hz : F.coefficient c = 0 <;> by_cases hn : F.coefficient c < 0 <;>
    simp [Family.positiveLanguage, Family.signValue, hz, hn] <;> omega

end LeanCanny.Algebra.MacaulayDeformationBits
