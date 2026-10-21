/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PrimitivePairReaders
public import LeanCanny.Algebra.CannyResultantHeightSpace
public import LeanCanny.Algebra.SeparableSpace

/-! # Testing a primitive-pair resultant from the original source readers

The coefficient height of the resultant, its derivative, and the final
Sylvester determinant are all derived from source degree and height controls.
No separability oracle or expanded resultant coefficient reader is assumed.
-/

@[expose] public section

namespace LeanCanny.Algebra.PrimitivePairBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open RationalSubstitution.IntegerBits (context selectedDegree mValue coefficientResidue)
attribute [local irreducible] BinaryNat.mul

structure Heights (S : Source) where
  leftBits : List Bool → List Bool
  rightBits : List Bool → List Bool
  leftBitsFP : leftBits ∈ FP
  rightBitsFP : rightBits ∈ FP
  left_bound : ∀ c k, ((S.left c).coeff k).natAbs ≤ 2 ^ Nat.fromBitsLE (leftBits c)
  right_bound : ∀ c k, ((S.right c).coeff k).natAbs ≤ 2 ^ Nat.fromBitsLE (rightBits c)

noncomputable def heightFamily (S : Source) (H : Heights S) : CannyResultantBits.BoundedFamily where
  source := ⟨S.left, S.right, S.direction, fun _ => 0⟩
  leftBits c := Nat.fromBitsLE (H.leftBits c)
  rightBits c := Nat.fromBitsLE (H.rightBits c)
  left_bound := H.left_bound
  right_bound := H.right_bound

def modularCoefficientQuery (q : List Bool) : List Bool :=
  pair (pair (pairFst (pairFst q)) (pairSnd q)) (pairSnd (pairFst q))

theorem modularCoefficientQuery_FP : modularCoefficientQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP)
    (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)

theorem modularCoefficient_packet (p : List Bool → Polynomial ℤ) (q : List Bool) (k : ℕ) :
    coefficient p (modularCoefficientQuery (pair q (BinaryNatCode.encode k))) =
      residueBits (((p (pairFst q)).coeff k : ℤ) : ZMod (Nat.fromBitsLE (pairSnd q) + 1)) := by
  simp only [coefficient, modularCoefficientQuery, context, selectedDegree, mValue,
    pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rfl

noncomputable def heightAccess (S : Source) (A : Readers S) (H : Heights S) :
    CannyResultantBits.IntegerAccess (heightFamily S H) where
  residue := {
    leftDegree := A.leftDegree
    rightDegree := A.rightDegree
    direction := A.direction
    degree := fun _ => []
    leftCoefficient := coefficient S.left ∘ modularCoefficientQuery
    rightCoefficient := coefficient S.right ∘ modularCoefficientQuery
    leftDegree_eq := A.leftDegree_eq
    rightDegree_eq := A.rightDegree_eq
    direction_eq := A.direction_eq
    degree_eq _ := rfl
    leftCoefficient_eq := modularCoefficient_packet S.left
    rightCoefficient_eq := modularCoefficient_packet S.right }
  leftBits := BinaryNat.normalize ∘ H.leftBits
  rightBits := BinaryNat.normalize ∘ H.rightBits
  leftBits_eq _ := BinaryNat.normalize_eq_bits _
  rightBits_eq _ := BinaryNat.normalize_eq_bits _

theorem heightAccess_controls (S : Source) (A : Readers S) (H : Heights S) :
    (heightAccess S A H).ControlsPolyTime := by
  constructor
  · exact ⟨A.leftDegreeFP, A.rightDegreeFP, A.directionFP, constFn_mem_FP []⟩
  · simpa only [heightAccess] using mem_FP_comp H.leftBitsFP BinaryNat.normalize_mem_FP
  · simpa only [heightAccess] using mem_FP_comp H.rightBitsFP BinaryNat.normalize_mem_FP

noncomputable def separableFamily (S : Source) (H : Heights S) : SeparableBits.Family where
  polynomial c := cannyResultant (S.left c) (S.right c) (S.direction c)
  height := (heightFamily S H).budget
  coefficient_bound c k := by
    have hb : ((cannyResultant (S.left c) (S.right c) (S.direction c)).coeff k).natAbs.size ≤
        (heightFamily S H).budget c := by
      have h := cannyResultant_coeff_size_le (S.left c) (S.right c) (S.direction c)
        (2 ^ Nat.fromBitsLE (H.leftBits c)) (2 ^ Nat.fromBitsLE (H.rightBits c)) k
        (H.left_bound c) (H.right_bound c)
      simpa only [heightFamily, CannyResultantBits.BoundedFamily.budget, shiftBitBudget, Nat.size_pow] using h
    exact (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide) hb)

noncomputable def separableReaders (S : Source) (A : Readers S) (H : Heights S)
    (hdegree : ∀ c, (cannyResultant (S.left c) (S.right c) (S.direction c)).natDegree =
      (S.left c).natDegree * (S.right c).natDegree) : SeparableBits.Readers (separableFamily S H) where
  degree c := BinaryNat.mul (pair (A.leftDegree c) (A.rightDegree c))
  height := (heightAccess S A H).budget
  coefficient := coefficient (fun c => cannyResultant (S.left c) (S.right c) (S.direction c)) ∘ modularCoefficientQuery
  degreeFP := by
    have h := mem_FP_comp (mem_FP_pair A.leftDegreeFP A.rightDegreeFP) BinaryNat.mul_mem_FP
    exact mem_FP_of_eq h (fun _ => rfl)
  heightFP := (heightAccess S A H).budget_mem_FP_of_controls (heightAccess_controls S A H)
  degree_eq c := by
    simp only [A.leftDegree_eq, A.rightDegree_eq, BinaryNat.mul_pair, BinaryNatCode.encode,
      Nat.fromBitsLE_bits, separableFamily, hdegree]
  height_eq := (heightAccess S A H).budget_code
  coefficient_eq := modularCoefficient_packet _
  evaluator := (resultantEvaluator S A).precompose modularCoefficientQuery modularCoefficientQuery_FP

theorem separabilityDecider (S : Source) (A : Readers S) (H : Heights S)
    (hdegree : ∀ c, (cannyResultant (S.left c) (S.right c) (S.direction c)).natDegree =
      (S.left c).natDegree * (S.right c).natDegree)
    (hne : ∀ c, cannyResultant (S.left c) (S.right c) (S.direction c) ≠ 0) :
    SpaceDecider {c | ((cannyResultant (S.left c) (S.right c) (S.direction c)).map (Int.castRingHom ℚ)).Separable} := by
  have D := SeparableBits.decider (separableFamily S H) (separableReaders S A H hdegree) hne
  exact D.congr rfl

end LeanCanny.Algebra.PrimitivePairBits
