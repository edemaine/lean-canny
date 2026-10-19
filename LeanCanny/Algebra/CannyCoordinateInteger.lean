/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CannyCoordinateResidue
public import LeanCanny.Algebra.CannySubresultantInteger
public import LeanCanny.Algebra.CoordinateRecoveryBounds

/-!
# Integer zero testing across every coordinate-recovery branch

Adding the shifted-input and right-input allowances to the full resultant
budget bounds the direct linear branches as well as the subresultant branch.
All writers use certified binary arithmetic, even for exponential bit budgets.
-/

@[expose] public section

namespace LeanCanny.Algebra.CannyCoordinateBits
open Complexity
open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets
open LeanCanny.Computation
open CannySubresultantBits (BoundedFamily IntegerAccess)

def budget (F : BoundedFamily) (c : List Bool) : ℕ :=
  F.source.budget c + shiftBitBudget (F.source.source.left c).natDegree (F.source.source.direction c)
    (2 ^ F.source.leftBits c) + (F.source.rightBits c + 1) + 1

theorem coefficient_bits (F : BoundedFamily) (c : List Bool) :
    (integerCoefficient F.family c).natAbs.size ≤ budget F c := by
  have h := coordinateCoefficient_coeff_size_le (F.source.source.left c) (F.source.source.right c)
    (F.source.source.direction c) (2 ^ F.source.leftBits c) (2 ^ F.source.rightBits c)
    (F.coefficient c) (F.source.source.degree c) (F.source.left_bound c) (F.source.right_bound c)
  have hb := Subresultant.budget_le_full (F.source.source.left c).natDegree (F.source.source.right c).natDegree
    1 (shiftBitBudget (F.source.source.left c).natDegree (F.source.source.direction c) (2 ^ F.source.leftBits c))
    (2 ^ F.source.rightBits c).size
  have hfull : Subresultant.budget (F.source.source.left c).natDegree (F.source.source.right c).natDegree 1
      (shiftBitBudget (F.source.source.left c).natDegree (F.source.source.direction c) (2 ^ F.source.leftBits c))
      (2 ^ F.source.rightBits c).size ≤ F.source.budget c := by
    simpa only [CannyResultantBits.BoundedFamily.budget, shiftBitBudget, Nat.size_pow,
      Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hb
  change ((coordinateCoefficient (F.source.source.left c) (F.source.source.right c)
    (F.source.source.direction c) (F.coefficient c)).coeff (F.source.source.degree c)).natAbs.size ≤ _
  unfold coordinateBitBudget at h
  unfold budget
  simp only [Nat.size_pow] at h hfull
  omega

def integerZeroLanguage (F : BoundedFamily) : Language := {c | integerCoefficient F.family c = 0}

def budgetWord {F : BoundedFamily} (a : IntegerAccess F) (c : List Bool) : List Bool :=
  BinaryNat.succ (BinaryNat.add (pair
    (BinaryNat.add (pair (a.source.budget c) (a.source.shiftBudget c)))
    (BinaryNat.succ (a.source.rightBits c))))

theorem budgetWord_mem_FP {F : BoundedFamily} (a : IntegerAccess F) (ha : a.PolyTime) : budgetWord a ∈ FP := by
  have hs := mem_FP_comp (mem_FP_pair (a.source.budget_mem_FP ha.source) (a.source.shiftBudget_mem_FP ha.source))
    BinaryNat.add_mem_FP
  have hr := mem_FP_comp ha.source.rightBits BinaryNat.succ_mem_FP
  have he := mem_FP_comp (mem_FP_comp (mem_FP_pair hs hr) BinaryNat.add_mem_FP) BinaryNat.succ_mem_FP
  refine mem_FP_of_eq (g := budgetWord a) he ?_
  intro c
  simp only [Function.comp_apply, budgetWord]

theorem budgetWord_code {F : BoundedFamily} (a : IntegerAccess F) (c : List Bool) :
    budgetWord a c = BinaryNatCode.encode (budget F c) := by
  simp only [budgetWord, a.source.budget_code, a.source.shiftBudget_code, a.source.rightBits_eq,
    BinaryNat.succ_eq_bits, BinaryNat.add_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    budget, shiftBitBudget, Nat.size_pow]

def boundWord {F : BoundedFamily} (a : IntegerAccess F) (c : List Bool) : List Bool :=
  BinaryNat.add (pair (BinaryNat.add (pair (budgetWord a c) (budgetWord a c))) (BinaryNatCode.encode 4))

theorem boundWord_mem_FP {F : BoundedFamily} (a : IntegerAccess F) (ha : a.PolyTime) : boundWord a ∈ FP := by
  have hb := budgetWord_mem_FP a ha
  have hd := mem_FP_comp (mem_FP_pair hb hb) BinaryNat.add_mem_FP
  have he := mem_FP_comp (mem_FP_pair hd (constFn_mem_FP (BinaryNatCode.encode 4))) BinaryNat.add_mem_FP
  refine mem_FP_of_eq (g := boundWord a) he ?_
  intro c
  simp only [Function.comp_apply, boundWord]

theorem boundWord_code {F : BoundedFamily} (a : IntegerAccess F) (c : List Bool) :
    boundWord a c = BinaryNatCode.encode (2 * budget F c + 4) := by
  simp only [boundWord, budgetWord_code, BinaryNat.add_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  congr 1
  omega

theorem modular_packet (F : BoundedFamily) (c : List Bool) (k : ℕ) :
    pair c (BinaryNatCode.encode k) ∈ zeroLanguage F.family ↔ (integerCoefficient F.family c : ZMod (k + 1)) = 0 := by
  change (integerCoefficient F.family (pairFst (pair c (BinaryNatCode.encode k))) :
    ZMod (CannyResultantBits.mValue (pair c (BinaryNatCode.encode k)))) = 0 ↔ _
  unfold CannyResultantBits.mValue
  rw [pairFst_pair, pairSnd_pair]
  rw [show Nat.fromBitsLE (BinaryNatCode.encode k) = k from Nat.fromBitsLE_bits k]

theorem scan_language_eq (F : BoundedFamily) :
    BoundedScan.language (zeroLanguage F.family) (fun c => 2 * budget F c + 4) = integerZeroLanguage F := by
  ext c
  change (∀ k < 2 * budget F c + 4, pair c (BinaryNatCode.encode k) ∈ zeroLanguage F.family) ↔
    integerCoefficient F.family c = 0
  rw [IntegerModular.eq_zero_iff_residues (integerCoefficient F.family c) (budget F c) (coefficient_bits F c)]
  constructor
  · intro h m hm hn
    have hr := (modular_packet F c (m - 1)).mp (h (m - 1) (by omega))
    rw [Nat.sub_add_cancel hm] at hr
    exact hr
  · intro h k hk
    exact (modular_packet F c k).mpr (h (k + 1) (by omega) (by omega))

noncomputable def integerDecider {F : BoundedFamily} (a : IntegerAccess F) (ha : a.PolyTime) :
    SpaceDecider (integerZeroLanguage F) := by
  rw [← scan_language_eq F]
  exact BoundedScan.decider (decider a.residue (a.residue_polyTime ha)) (boundWord a)
    (boundWord_mem_FP a ha) (fun c => 2 * budget F c + 4) (boundWord_code a)

theorem integerZeroLanguage_mem_PSPACE {F : BoundedFamily} (a : IntegerAccess F) (ha : a.PolyTime) :
    integerZeroLanguage F ∈ PSPACE := (integerDecider a ha).mem_PSPACE

end LeanCanny.Algebra.CannyCoordinateBits
