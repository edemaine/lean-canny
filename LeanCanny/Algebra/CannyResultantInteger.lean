/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CannyResultantResidue
public import LeanCanny.Algebra.ResultantBounds
public import LeanCanny.Computation.BoundedScanPSPACE

/-!
# Polynomial-space integer zero testing of Canny resultant coefficients

Source coefficient bit budgets give an explicit resultant coefficient budget.
All budget writers use binary arithmetic and word lengths. The bounded modulus
scan consumes the certified Canny residue decider, deciding whether the selected
integer coefficient is zero without storing its complete value.
-/

@[expose] public section

namespace LeanCanny.Algebra.CannyResultantBits
open Complexity
open LeanCanny.Encoding
open LeanCanny.Computation

noncomputable def Family.coefficient (F : Family) (c : List Bool) : ℤ :=
  (cannyResultant (F.left c) (F.right c) (F.direction c)).coeff (F.degree c)

structure BoundedFamily where
  source : Family
  leftBits : List Bool → ℕ
  rightBits : List Bool → ℕ
  left_bound : ∀ c k, ((source.left c).coeff k).natAbs ≤ 2 ^ leftBits c
  right_bound : ∀ c k, ((source.right c).coeff k).natAbs ≤ 2 ^ rightBits c

def BoundedFamily.budget (F : BoundedFamily) (c : List Bool) : ℕ :=
  ((F.source.left c).natDegree + (F.source.right c).natDegree).size *
      ((F.source.left c).natDegree + (F.source.right c).natDegree) +
    (F.source.right c).natDegree * (((F.source.left c).natDegree + 1).size + (F.source.left c).natDegree +
      (F.leftBits c + 1) + (F.source.direction c + 1).size * (F.source.left c).natDegree) +
    (F.source.left c).natDegree * (F.rightBits c + 1) + 1

theorem BoundedFamily.coefficient_bits (F : BoundedFamily) (c : List Bool) :
    (F.source.coefficient c).natAbs.size ≤ F.budget c := by
  have h := cannyResultant_coeff_size_le (F.source.left c) (F.source.right c) (F.source.direction c)
    (2 ^ F.leftBits c) (2 ^ F.rightBits c) (F.source.degree c) (F.left_bound c) (F.right_bound c)
  simpa only [Family.coefficient, BoundedFamily.budget, shiftBitBudget, Nat.size_pow] using h

def BoundedFamily.zeroLanguage (F : BoundedFamily) : Complexity.Language := {c | F.source.coefficient c = 0}

structure IntegerAccess (F : BoundedFamily) where
  residue : Access F.source
  leftBits : List Bool → List Bool
  rightBits : List Bool → List Bool
  leftBits_eq : ∀ c, leftBits c = BinaryNatCode.encode (F.leftBits c)
  rightBits_eq : ∀ c, rightBits c = BinaryNatCode.encode (F.rightBits c)

structure IntegerAccess.PolyTime {F : BoundedFamily} (a : IntegerAccess F) : Prop where
  residue : a.residue.PolyTime
  leftBits : a.leftBits ∈ FP
  rightBits : a.rightBits ∈ FP

namespace IntegerAccess

def dimension {F : BoundedFamily} (a : IntegerAccess F) (c : List Bool) : List Bool :=
  BinaryNat.add (pair (a.residue.leftDegree c) (a.residue.rightDegree c))

def sizeField (f : List Bool → List Bool) (c : List Bool) : List Bool := BinaryNatCode.encode (f c).length

def shiftBudget {F : BoundedFamily} (a : IntegerAccess F) (c : List Bool) : List Bool :=
  BinaryNat.add (pair
    (BinaryNat.add (pair (sizeField (BinaryNat.succ ∘ a.residue.leftDegree) c) (a.residue.leftDegree c)))
    (BinaryNat.add (pair (BinaryNat.succ (a.leftBits c))
      (BinaryNat.mul (pair (sizeField (BinaryNat.succ ∘ a.residue.direction) c) (a.residue.leftDegree c))))))

def budget {F : BoundedFamily} (a : IntegerAccess F) (c : List Bool) : List Bool :=
  BinaryNat.succ (BinaryNat.add (pair
    (BinaryNat.add (pair (BinaryNat.mul (pair (sizeField a.dimension c) (a.dimension c)))
      (BinaryNat.mul (pair (a.residue.rightDegree c) (a.shiftBudget c)))))
    (BinaryNat.mul (pair (a.residue.leftDegree c) (BinaryNat.succ (a.rightBits c))))))

theorem sizeField_mem_FP {f : List Bool → List Bool} (hf : f ∈ FP) : sizeField f ∈ FP :=
  bits_mem_FP (UnaryFn.length hf)

theorem dimension_mem_FP {F : BoundedFamily} (a : IntegerAccess F) (ha : a.PolyTime) : a.dimension ∈ FP := by
  have h := mem_FP_comp (mem_FP_pair ha.residue.leftDegree ha.residue.rightDegree) BinaryNat.add_mem_FP
  refine mem_FP_of_eq (g := a.dimension) h ?_
  intro c
  simp only [Function.comp_apply, dimension]

theorem shiftBudget_mem_FP {F : BoundedFamily} (a : IntegerAccess F) (ha : a.PolyTime) : a.shiftBudget ∈ FP := by
  have hsd := sizeField_mem_FP (mem_FP_comp ha.residue.leftDegree BinaryNat.succ_mem_FP)
  have hsc := sizeField_mem_FP (mem_FP_comp ha.residue.direction BinaryNat.succ_mem_FP)
  have hb := mem_FP_comp ha.leftBits BinaryNat.succ_mem_FP
  have hp := mem_FP_comp (mem_FP_pair hsc ha.residue.leftDegree) BinaryNat.mul_mem_FP
  have hl := mem_FP_comp (mem_FP_pair hsd ha.residue.leftDegree) BinaryNat.add_mem_FP
  have hr := mem_FP_comp (mem_FP_pair hb hp) BinaryNat.add_mem_FP
  have h := mem_FP_comp (mem_FP_pair hl hr) BinaryNat.add_mem_FP
  refine mem_FP_of_eq (g := a.shiftBudget) h ?_
  intro c
  simp only [Function.comp_apply, shiftBudget]

theorem budget_mem_FP {F : BoundedFamily} (a : IntegerAccess F) (ha : a.PolyTime) : a.budget ∈ FP := by
  have hn := dimension_mem_FP a ha
  have hs := sizeField_mem_FP hn
  have hf := mem_FP_comp (mem_FP_pair hs hn) BinaryNat.mul_mem_FP
  have hl := mem_FP_comp (mem_FP_pair ha.residue.rightDegree (shiftBudget_mem_FP a ha)) BinaryNat.mul_mem_FP
  have hb := mem_FP_comp ha.rightBits BinaryNat.succ_mem_FP
  have hr := mem_FP_comp (mem_FP_pair ha.residue.leftDegree hb) BinaryNat.mul_mem_FP
  have hfl := mem_FP_comp (mem_FP_pair hf hl) BinaryNat.add_mem_FP
  have h := mem_FP_comp (mem_FP_comp (mem_FP_pair hfl hr) BinaryNat.add_mem_FP) BinaryNat.succ_mem_FP
  refine mem_FP_of_eq (g := a.budget) h ?_
  intro c
  simp only [Function.comp_apply, budget]

theorem dimension_code {F : BoundedFamily} (a : IntegerAccess F) (c : List Bool) :
    a.dimension c = BinaryNatCode.encode ((F.source.left c).natDegree + (F.source.right c).natDegree) := by
  simp only [dimension, a.residue.leftDegree_eq, a.residue.rightDegree_eq, BinaryNat.add_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem shiftBudget_code {F : BoundedFamily} (a : IntegerAccess F) (c : List Bool) :
    a.shiftBudget c = BinaryNatCode.encode
      (((F.source.left c).natDegree + 1).size + (F.source.left c).natDegree + (F.leftBits c + 1) +
        (F.source.direction c + 1).size * (F.source.left c).natDegree) := by
  simp only [shiftBudget, sizeField, Function.comp_apply, a.residue.leftDegree_eq, a.residue.direction_eq,
    a.leftBits_eq, BinaryNat.succ_eq_bits, BinaryNat.add_pair, BinaryNat.mul_pair, BinaryNatCode.encode,
    Nat.fromBitsLE_bits, ← Nat.size_eq_bits_len, Nat.add_assoc]

theorem budget_code {F : BoundedFamily} (a : IntegerAccess F) (c : List Bool) :
    a.budget c = BinaryNatCode.encode (F.budget c) := by
  simp only [budget, sizeField, dimension_code, shiftBudget_code, a.residue.leftDegree_eq,
    a.residue.rightDegree_eq, a.rightBits_eq, BinaryNat.succ_eq_bits, BinaryNat.add_pair,
    BinaryNat.mul_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, ← Nat.size_eq_bits_len, BoundedFamily.budget]

def bound {F : BoundedFamily} (a : IntegerAccess F) (c : List Bool) : List Bool :=
  BinaryNat.add (pair (BinaryNat.add (pair (a.budget c) (a.budget c))) (BinaryNatCode.encode 4))

theorem bound_mem_FP {F : BoundedFamily} (a : IntegerAccess F) (ha : a.PolyTime) : a.bound ∈ FP := by
  have hb := budget_mem_FP a ha
  have hd := mem_FP_comp (mem_FP_pair hb hb) BinaryNat.add_mem_FP
  have h := mem_FP_comp (mem_FP_pair hd (constFn_mem_FP (BinaryNatCode.encode 4))) BinaryNat.add_mem_FP
  refine mem_FP_of_eq (g := a.bound) h ?_
  intro c
  simp only [Function.comp_apply, bound]

theorem bound_code {F : BoundedFamily} (a : IntegerAccess F) (c : List Bool) :
    a.bound c = BinaryNatCode.encode (2 * F.budget c + 4) := by
  simp only [bound, budget_code, BinaryNat.add_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  congr 1
  omega

theorem modular_packet (F : BoundedFamily) (c : List Bool) (k : ℕ) :
    pair c (BinaryNatCode.encode k) ∈ F.source.zeroLanguage ↔ (F.source.coefficient c : ZMod (k + 1)) = 0 := by
  change (((cannyResultant (F.source.left (pairFst (pair c (BinaryNatCode.encode k))))
    (F.source.right (pairFst (pair c (BinaryNatCode.encode k))))
    (F.source.direction (pairFst (pair c (BinaryNatCode.encode k))))).coeff
    (F.source.degree (pairFst (pair c (BinaryNatCode.encode k)))) : ℤ) :
      ZMod (Nat.fromBitsLE (pairSnd (pair c (BinaryNatCode.encode k))) + 1)) = 0 ↔ _
  rw [pairFst_pair, pairSnd_pair]
  rw [show Nat.fromBitsLE (BinaryNatCode.encode k) = k from Nat.fromBitsLE_bits k]
  rfl

theorem scan_language_eq (F : BoundedFamily) :
    BoundedScan.language F.source.zeroLanguage (fun c => 2 * F.budget c + 4) = F.zeroLanguage := by
  ext c
  change (∀ k < 2 * F.budget c + 4, pair c (BinaryNatCode.encode k) ∈ F.source.zeroLanguage) ↔
    F.source.coefficient c = 0
  rw [IntegerModular.eq_zero_iff_residues (F.source.coefficient c) (F.budget c) (F.coefficient_bits c)]
  constructor
  · intro h m hm hn
    have hr := (modular_packet F c (m - 1)).mp (h (m - 1) (by omega))
    rw [Nat.sub_add_cancel hm] at hr
    exact hr
  · intro h k hk
    apply (modular_packet F c k).mpr
    exact h (k + 1) (by omega) (by omega)

theorem decider {F : BoundedFamily} (a : IntegerAccess F) (ha : a.PolyTime) : SpaceDecider F.zeroLanguage := by
  rw [← scan_language_eq F]
  exact BoundedScan.decider (Access.decider a.residue ha.residue) a.bound (bound_mem_FP a ha)
    (fun c => 2 * F.budget c + 4) (bound_code a)

theorem zeroLanguage_mem_PSPACE {F : BoundedFamily} (a : IntegerAccess F) (ha : a.PolyTime) :
    F.zeroLanguage ∈ PSPACE := (decider a ha).mem_PSPACE

end IntegerAccess
end LeanCanny.Algebra.CannyResultantBits
