/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.DenominatorClearingSpace
public import LeanCanny.Algebra.IntegerSignumSpace
public import LeanCanny.Algebra.IntegerZeroSpace

/-! # Integer signs and zero tests for constructively cleared coefficients

Canonical rational numerator/denominator residues and binary source bit/count
bounds give a complete space-certified integer normalization pipeline. The
integer magnitude budget is B*N+1. CRT sign recovery includes the modular
product computation and all numerator/denominator child work.
-/

@[expose] public section

namespace LeanCanny.Algebra.DenominatorClearing
open Complexity
open LeanCanny.Encoding LeanCanny.Computation
open MatrixPower

structure Source where
  count : List Bool → ℕ
  index : (c : List Bool) → Fin (count c)
  coefficient : (c : List Bool) → Fin (count c) → ℚ

def Source.integer (S : Source) (c : List Bool) : ℤ :=
  FiniteDenominatorClearing.cleared (S.coefficient c) (S.index c)

def Source.modularFamily (S : Source) : Family where
  count := fun p => S.count (pairFst p)
  modulus := fun p => Nat.fromBitsLE (pairSnd p) + 1
  index := fun p => S.index (pairFst p)
  coefficient := fun p => S.coefficient (pairFst p)
  modulus_ne_zero := fun _ => by omega

theorem Source.residue_packet (S : Source) (c : List Bool) (m : ℕ) (hm : 0 < m) :
    S.modularFamily.value (pair c (BinaryNatCode.encode (m - 1))) = residueBits (S.integer c : ZMod m) := by
  change residueBits (S.integer (pairFst (pair c (BinaryNatCode.encode (m - 1)))) :
    ZMod (Nat.fromBitsLE (pairSnd (pair c (BinaryNatCode.encode (m - 1)))) + 1)) = _
  rw [pairFst_pair, pairSnd_pair]
  rw [show Nat.fromBitsLE (BinaryNatCode.encode (m - 1)) + 1 = m by
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.sub_add_cancel (show 1 ≤ m by omega)]]

structure SourceAccess (S : Source) where
  count : List Bool → List Bool
  selected : List Bool → List Bool
  bound : List Bool → List Bool
  numerator : List Bool → List Bool
  denominator : List Bool → List Bool
  count_eq : ∀ c, count c = BinaryNatCode.encode (S.count c)
  selected_eq : ∀ c, selected c = BinaryNatCode.encode (S.index c).val
  parts_bound : ∀ c (j : Fin (S.count c)), (S.coefficient c j).num.natAbs.size ≤ Nat.fromBitsLE (bound c) ∧
    (S.coefficient c j).den.size ≤ Nat.fromBitsLE (bound c)
  numerator_eq : ∀ p, numerator p = residueBits
    ((S.coefficient (pairFst p) (S.index (pairFst p))).num : ZMod (Nat.fromBitsLE (pairSnd p) + 1))
  denominator_eq : ∀ p (j : Fin (S.count (pairFst p))), denominator (pair p (BinaryNatCode.encode j.val)) =
    residueBits ((S.coefficient (pairFst p) j).den : ZMod (Nat.fromBitsLE (pairSnd p) + 1))

namespace SourceAccess
variable {S : Source}

def modularAccess (a : SourceAccess S) : Access S.modularFamily where
  count := a.count ∘ pairFst
  modulus := BinaryNat.succ ∘ pairSnd
  selected := a.selected ∘ pairFst
  numerator := a.numerator
  denominator := a.denominator
  count_eq := fun p => a.count_eq (pairFst p)
  modulus_eq := fun p => by simp only [Function.comp_apply, BinaryNat.succ_eq_bits, BinaryNatCode.encode, Source.modularFamily]
  selected_eq := fun p => a.selected_eq (pairFst p)
  numerator_eq := a.numerator_eq
  denominator_eq := a.denominator_eq

def budget (a : SourceAccess S) (c : List Bool) : List Bool :=
  BinaryNat.succ (BinaryNat.mul (pair (a.bound c) (a.count c)))

theorem budget_mem_FP (a : SourceAccess S) (hb : a.bound ∈ FP) (hc : a.count ∈ FP) : a.budget ∈ FP := by
  have hmul := mem_FP_comp (mem_FP_pair hb hc) BinaryNat.mul_mem_FP
  have h := mem_FP_comp hmul BinaryNat.succ_mem_FP
  exact mem_FP_of_eq h (fun _ => rfl)

theorem budget_code (a : SourceAccess S) (c : List Bool) :
    a.budget c = BinaryNatCode.encode (Nat.fromBitsLE (a.bound c) * S.count c + 1) := by
  simp only [budget, BinaryNat.succ_eq_bits, BinaryNat.mul_pair, a.count_eq,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem integer_size_le (a : SourceAccess S) (c : List Bool) :
    (S.integer c).natAbs.size ≤ Nat.fromBitsLE (a.budget c) := by
  rw [a.budget_code]
  simpa only [Source.integer, BinaryNatCode.encode, Nat.fromBitsLE_bits, Fintype.card_fin] using
    FiniteDenominatorClearing.cleared_size_le (S.coefficient c) _ (a.parts_bound c) (S.index c)

noncomputable def residueEvaluator (a : SourceAccess S) (hc : a.count ∈ FP) (hs : a.selected ∈ FP)
    (N : SpaceFunction a.numerator) (D : SpaceFunction a.denominator) : SpaceFunction S.modularFamily.value := by
  have hcount := mem_FP_comp pairFst_mem_FP hc
  have hmod := mem_FP_comp pairSnd_mem_FP BinaryNat.succ_mem_FP
  have hselected := mem_FP_comp pairFst_mem_FP hs
  exact a.modularAccess.evaluator hcount hmod hselected N D

noncomputable def signumEvaluator (a : SourceAccess S)
    (hc : a.count ∈ FP) (hs : a.selected ∈ FP) (hb : a.bound ∈ FP)
    (N : SpaceFunction a.numerator) (D : SpaceFunction a.denominator) :
    SpaceFunction (fun c => if S.integer c = 0 then [] else if S.integer c < 0 then [true] else [false, true]) :=
  IntegerSignumBits.evaluator (a.residueEvaluator hc hs N D) a.budget (a.budget_mem_FP hb hc)
    S.integer a.integer_size_le S.residue_packet

noncomputable def zeroDecider (a : SourceAccess S)
    (hc : a.count ∈ FP) (hs : a.selected ∈ FP) (hb : a.bound ∈ FP)
    (N : SpaceFunction a.numerator) (D : SpaceFunction a.denominator) : SpaceDecider {c | S.integer c = 0} :=
  IntegerZeroBits.zeroDecider (a.residueEvaluator hc hs N D) a.budget (a.budget_mem_FP hb hc)
    S.integer a.integer_size_le S.residue_packet

theorem zeroLanguage_mem_PSPACE (a : SourceAccess S)
    (hc : a.count ∈ FP) (hs : a.selected ∈ FP) (hb : a.bound ∈ FP)
    (N : SpaceFunction a.numerator) (D : SpaceFunction a.denominator) : {c | S.integer c = 0} ∈ PSPACE :=
  (a.zeroDecider hc hs hb N D).mem_PSPACE

theorem negativeLanguage_mem_PSPACE (a : SourceAccess S)
    (hc : a.count ∈ FP) (hs : a.selected ∈ FP) (hb : a.bound ∈ FP)
    (N : SpaceFunction a.numerator) (D : SpaceFunction a.denominator) : {c | S.integer c < 0} ∈ PSPACE :=
  IntegerSignBits.negativeLanguage_mem_PSPACE (a.residueEvaluator hc hs N D) a.budget (a.budget_mem_FP hb hc)
    S.integer a.integer_size_le S.residue_packet

theorem positiveLanguage_mem_PSPACE (a : SourceAccess S)
    (hc : a.count ∈ FP) (hs : a.selected ∈ FP) (hb : a.bound ∈ FP)
    (N : SpaceFunction a.numerator) (D : SpaceFunction a.denominator) : {c | 0 < S.integer c} ∈ PSPACE := by
  let E := a.signumEvaluator hc hs hb N D
  have ht : (fun w : List Bool => [decide (w = [false, true])]) ∈ FP :=
    (LeanCanny.Encoding.Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [false, true])).flag_mem_FP
  apply (E.decider (fun w => decide (w = [false, true])) ht ?_).mem_PSPACE
  intro c
  by_cases hz : S.integer c = 0
  · simp [hz]
  · by_cases hn : S.integer c < 0 <;> simp [hz, hn] <;> omega

end SourceAccess
end LeanCanny.Algebra.DenominatorClearing
