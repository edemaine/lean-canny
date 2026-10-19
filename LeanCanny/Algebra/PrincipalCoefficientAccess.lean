/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PrincipalMinorSpace
public import LeanCanny.Algebra.SignStatisticSpace

/-! # Binary source access for signed principal coefficients

The query is an original context paired with a coefficient order. A clamped
minor order gives a valid determinant family on every input word. The signed
coefficient reader uses that determinant only inside the principal range.
-/

@[expose] public section

namespace LeanCanny.Algebra.PrincipalCoefficientBits
open Complexity Polynomial
open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets
open LeanCanny.Computation
open MatrixPower PrincipalSubresultant

noncomputable def integerResidue (z : ℤ) (m : ℕ) : List Bool := residueBits (z : ZMod m)

def minimum (a b : List Bool) : List Bool :=
  if Nat.fromBitsLE a ≤ Nat.fromBitsLE b then BinaryNat.normalize a else BinaryNat.normalize b

theorem minimum_eq (a b : List Bool) : minimum a b =
    BinaryNatCode.encode (min (Nat.fromBitsLE a) (Nat.fromBitsLE b)) := by
  unfold minimum
  split_ifs with h
  · rw [Nat.min_eq_left h, BinaryNat.normalize_eq_bits]
    rfl
  · rw [Nat.min_eq_right (by omega), BinaryNat.normalize_eq_bits]
    rfl

theorem minimum_mem_FP {a b : List Bool → List Bool} (ha : a ∈ FP) (hb : b ∈ FP) :
    (fun c => minimum (a c) (b c)) ∈ FP := by
  have h := (BinaryNat.le_fppred ha hb).ite_mem_FP (mem_FP_comp ha BinaryNat.normalize_mem_FP)
    (mem_FP_comp hb BinaryNat.normalize_mem_FP)
  refine mem_FP_of_eq h ?_
  intro c
  simp only [minimum, Function.comp_apply]

def minorFamily (F : Resultant.Family) : PrincipalMinorBits.Family where
  left r := F.left (pairFst r)
  right r := F.right (pairFst r)
  leftDegree r := F.leftDegree (pairFst r)
  rightDegree r := F.rightDegree (pairFst r)
  order r := min (Nat.fromBitsLE (pairSnd r)) (min (F.leftDegree (pairFst r)) (F.rightDegree (pairFst r)))
  coefficientBits r := F.coefficientBits (pairFst r)
  order_left _ := (Nat.min_le_right _ _).trans (Nat.min_le_left _ _)
  order_right _ := (Nat.min_le_right _ _).trans (Nat.min_le_right _ _)
  left_bound r := F.left_bound (pairFst r)
  right_bound r := F.right_bound (pairFst r)

noncomputable def coefficient (F : Resultant.Family) (r : List Bool) : ℤ :=
  signedPsc (F.left (pairFst r)) (F.right (pairFst r))
    (F.leftDegree (pairFst r)) (F.rightDegree (pairFst r)) (Nat.fromBitsLE (pairSnd r))

def budget (F : Resultant.Family) (r : List Bool) : ℕ :=
  F.integer.budget (pairFst r) + F.coefficientBits (pairFst r) + 1

theorem coefficient_size (F : Resultant.Family) (r : List Bool) :
    (coefficient F r).natAbs.size ≤ budget F r := by
  let c := pairFst r
  let k := Nat.fromBitsLE (pairSnd r)
  change (signedPsc (F.left c) (F.right c) (F.leftDegree c) (F.rightDegree c) k).natAbs.size ≤ _
  by_cases hk : k ≤ min (F.leftDegree c) (F.rightDegree c)
  · have h := (signedPsc_size_le (F.left c) (F.right c) (F.leftDegree c) (F.rightDegree c) k _ _ hk
      (F.left_bound c) (F.right_bound c)).trans (Subresultant.budget_le_full _ _ _ _ _)
    simp only [budget, Resultant.Family.integer]
    dsimp only [c] at h ⊢
    simp only [Nat.add_mul, Nat.add_assoc] at h ⊢
    omega
  · rw [signedPsc_of_lt _ _ (by omega)]
    have hl : ((F.left c).coeff (F.leftDegree c)).natAbs.size ≤ F.coefficientBits c + 1 := by
      simpa only [Nat.size_pow] using Nat.size_le_size (F.left_bound c (F.leftDegree c))
    have hr : ((F.right c).coeff (F.rightDegree c)).natAbs.size ≤ F.coefficientBits c + 1 := by
      simpa only [Nat.size_pow] using Nat.size_le_size (F.right_bound c (F.rightDegree c))
    split_ifs <;> simp only [budget, Resultant.Family.integer, Int.natAbs_zero, Nat.size_zero] <;>
      dsimp only [c] at * <;> omega

/-- Retain the modulus and coefficient index while removing the principal order
from the original polynomial's context. -/
def sourceQuery (s : List Bool) : List Bool :=
  pair (pair (pairFst (pairFst (pairFst s))) (pairSnd (pairFst s))) (pairSnd s)

theorem sourceQuery_mem_FP : sourceQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair
    (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairFst_mem_FP)
    (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)) pairSnd_mem_FP

def minorBits {F : Resultant.Family} (a : Resultant.Access F) : PrincipalMinorBits.Bits where
  base := {
    leftDegree := a.bits.leftDegree ∘ pairFst
    rightDegree := a.bits.rightDegree ∘ pairFst
    coefficientBits := a.bits.coefficientBits ∘ pairFst
    leftCoefficient := a.bits.leftCoefficient ∘ sourceQuery
    rightCoefficient := a.bits.rightCoefficient ∘ sourceQuery }
  order r := minimum (pairSnd r) (minimum (a.bits.leftDegree (pairFst r)) (a.bits.rightDegree (pairFst r)))

def minorAccess {F : Resultant.Family} (a : Resultant.Access F) : PrincipalMinorBits.Access (minorFamily F) where
  bits := minorBits a
  leftDegree_eq r := a.leftDegree (pairFst r)
  rightDegree_eq r := a.rightDegree (pairFst r)
  coefficientBits_eq r := a.coefficientBits (pairFst r)
  order_eq r := by
    simp only [minorBits, minimum_eq, a.leftDegree, a.rightDegree, BinaryNatCode.encode,
      Nat.fromBitsLE_bits, minorFamily]
  left_eq q i := by
    change a.bits.leftCoefficient (sourceQuery (pair q (BinaryNatCode.encode i))) =
      integerResidue ((F.left (pairFst (pairFst q))).coeff i) (Nat.fromBitsLE (pairSnd q) + 1)
    simp only [sourceQuery, pairFst_pair, pairSnd_pair]
    have h := a.leftCoefficient (pair (pairFst (pairFst q)) (pairSnd q)) i
    change _ = integerResidue ((F.left (pairFst (pair (pairFst (pairFst q)) (pairSnd q)))).coeff i)
      (Nat.fromBitsLE (pairSnd (pair (pairFst (pairFst q)) (pairSnd q))) + 1) at h
    rw [pairFst_pair, pairSnd_pair] at h
    exact h
  right_eq q i := by
    change a.bits.rightCoefficient (sourceQuery (pair q (BinaryNatCode.encode i))) =
      integerResidue ((F.right (pairFst (pairFst q))).coeff i) (Nat.fromBitsLE (pairSnd q) + 1)
    simp only [sourceQuery, pairFst_pair, pairSnd_pair]
    have h := a.rightCoefficient (pair (pairFst (pairFst q)) (pairSnd q)) i
    change _ = integerResidue ((F.right (pairFst (pair (pairFst (pairFst q)) (pairSnd q)))).coeff i)
      (Nat.fromBitsLE (pairSnd (pair (pairFst (pairFst q)) (pairSnd q))) + 1) at h
    rw [pairFst_pair, pairSnd_pair] at h
    exact h

theorem minor_controls {F : Resultant.Family} (a : Resultant.Access F) (ha : a.bits.ControlsPolyTime) :
    (minorAccess a).bits.ControlsPolyTime := by
  have hm := mem_FP_comp pairFst_mem_FP ha.leftDegree
  have hn := mem_FP_comp pairFst_mem_FP ha.rightDegree
  have hb := mem_FP_comp pairFst_mem_FP ha.coefficientBits
  exact ⟨⟨hm, hn, hb⟩, minimum_mem_FP pairSnd_mem_FP (minimum_mem_FP hm hn)⟩

noncomputable def minorResidueEvaluator {F : Resultant.Family} (a : Resultant.Access F)
    (ha : a.bits.ControlsPolyTime) (P : SpaceFunction a.bits.leftCoefficient)
    (Q : SpaceFunction a.bits.rightCoefficient) : SpaceFunction (minorFamily F).integer.modular.value :=
  (minorAccess a).residueEvaluator (minor_controls a ha)
    (P.precompose sourceQuery sourceQuery_mem_FP) (Q.precompose sourceQuery sourceQuery_mem_FP)

end LeanCanny.Algebra.PrincipalCoefficientBits
