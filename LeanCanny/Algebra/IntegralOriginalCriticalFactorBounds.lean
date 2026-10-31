/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralOriginalCriticalBounds

/-! # A height-independent factor for every original critical input

A common positive bound on the four original height exponents scales the
whole constructed critical budget by a factor depending only on spatial
metadata and the old rank. The factor has a native binary computation.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralOriginalCriticalFactorBounds
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralClearedCriticalBits IntegralOriginalCriticalBounds
set_option backward.isDefEq.respectTransparency false

theorem coefficient_affine (n M W D C V Q : ℕ) :
    IntegralFrozenCoefficientBounds.coefficientHeight n M W D C V Q =
      C + (n * 2 ^ W) * V + (D + n * 2 ^ W) * Q + (n * 2 ^ W + n + 2) * M.size + W * n := by
  unfold IntegralFrozenCoefficientBounds.coefficientHeight IntegralFrozenCoefficientBounds.termHeight
  ring

theorem coefficient_scaled (n M W D C V Q C0 V0 Q0 T : ℕ) (hT : 1 ≤ T)
    (hC : C ≤ C0 * T) (hV : V ≤ V0 * T) (hQ : Q ≤ Q0 * T) :
    IntegralFrozenCoefficientBounds.coefficientHeight n M W D C V Q ≤
      IntegralFrozenCoefficientBounds.coefficientHeight n M W D C0 V0 Q0 * T := by
  let U := n * 2 ^ W
  let Z := D + U
  let B := (U + n + 2) * M.size + W * n
  have HE (C V Q : ℕ) : IntegralFrozenCoefficientBounds.coefficientHeight n M W D C V Q = C + U * V + Z * Q + B := by
    rw [coefficient_affine]
    dsimp only [U, Z, B]
    omega
  have HB : B ≤ B * T := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left B hT
  rw [HE C V Q, HE C0 V0 Q0]
  calc
    _ ≤ C0 * T + U * (V0 * T) + Z * (Q0 * T) + B * T :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hC (Nat.mul_le_mul_left U hV)) (Nat.mul_le_mul_left Z hQ)) HB
    _ = _ := by ring

theorem constant_scaled (n M D V P V0 P0 T : ℕ) (hT : 1 ≤ T) (hV : V ≤ V0 * T) (hP : P ≤ P0 * T) :
    IntegralFrozenConstantBounds.constantHeight n M D V P ≤ IntegralFrozenConstantBounds.constantHeight n M D V0 P0 * T := by
  let B := D * M.size + n.size
  have HE (V P : ℕ) : IntegralFrozenConstantBounds.constantHeight n M D V P = P + D * V + B := by
    unfold IntegralFrozenConstantBounds.constantHeight IntegralFrozenConstantBounds.sumHeight
    dsimp only [B]
    ring
  have HB : B ≤ B * T := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left B hT
  rw [HE V P, HE V0 P0]
  calc
    _ ≤ P0 * T + D * (V0 * T) + B * T := Nat.add_le_add (Nat.add_le_add hP (Nat.mul_le_mul_left D hV)) HB
    _ = _ := by ring

def sourceTemplate (S : Source) (c : List Bool) : ℕ :=
  IntegralFrozenConstantBounds.lowerHeight (S.arity c) (S.rank c) (S.sourceWidth c) (S.allowance c) 1 1 1 1

def gradientTemplate (S : Source) (c : List Bool) : ℕ :=
  IntegralFrozenCoefficientBounds.coefficientHeight (S.arity c) (S.rank c) (S.sourceWidth c) (S.allowance c)
    (1 + S.sourceWidth c) 1 1

def lowerTemplate (S : Source) (c : List Bool) : ℕ :=
  sourceTemplate S c + (S.allowance c).size + gradientTemplate S c + (S.free c).size + 1

def leadingTemplate (S : Source) (c : List Bool) : ℕ := 1 + S.allowance c + (S.allowance c).size

def factor (S : Source) (c : List Bool) : ℕ :=
  IntegralActionHeightBounds.criticalFactor (IntegralClearedCriticalBounds.dimension S c) (S.rank c) (S.bound c) *
    (lowerTemplate S c + 2 * leadingTemplate S c + 1)

theorem factor_binary (S : Source) (a : Access S) : BinaryFn (factor S) := by
  have HS : BinaryFn (sourceTemplate S) := IntegralFrozenConstantBounds.lowerHeight_binary
    (BinaryFn.ofUnary a.arity) a.rank a.sourceWidth a.allowance (BinaryFn.const 1) (BinaryFn.const 1) (BinaryFn.const 1) (BinaryFn.const 1)
  have HG : BinaryFn (gradientTemplate S) := IntegralFrozenCoefficientBounds.coefficientHeight_binary
    (BinaryFn.ofUnary a.arity) a.rank a.sourceWidth a.allowance
    ((BinaryFn.const 1).add (BinaryFn.ofUnary a.sourceWidth)) (BinaryFn.const 1) (BinaryFn.const 1)
  have HL : BinaryFn (lowerTemplate S) := (((HS.add a.allowance.size).add HG).add (BinaryFn.ofUnary a.free).size).add (BinaryFn.const 1)
  have HP : BinaryFn (leadingTemplate S) := ((BinaryFn.const 1).add a.allowance).add a.allowance.size
  exact (IntegralActionHeightBounds.criticalFactor_binary (IntegralClearedCriticalBounds.dimension_binary S a) a.rank a.bound).mul
    ((HL.add ((BinaryFn.const 2).mul HP)).add (BinaryFn.const 1))

theorem lower_scaled (S : Source) (I : Inputs S) (c : List Bool) (T : ℕ) (hT : 1 ≤ T)
    (hC : I.coefficientHeight c ≤ T) (hV : I.retainedHeight c ≤ T)
    (hQ : I.denominatorHeight c ≤ T) (hP : I.leadingHeight c ≤ T) :
    lowerBudget S I c ≤ lowerTemplate S c * T := by
  have HC := coefficient_scaled (S.arity c) (S.rank c) (S.sourceWidth c) (S.allowance c)
    (I.coefficientHeight c) (I.retainedHeight c) (I.denominatorHeight c) 1 1 1 T hT
    (by simpa only [Nat.one_mul] using hC) (by simpa only [Nat.one_mul] using hV) (by simpa only [Nat.one_mul] using hQ)
  have HP := constant_scaled (S.arity c) (S.rank c) (S.allowance c) (I.retainedHeight c) (I.leadingHeight c) 1 1 T hT
    (by simpa only [Nat.one_mul] using hV) (by simpa only [Nat.one_mul] using hP)
  have HS : sourceBudget S I c ≤ sourceTemplate S c * T := by
    unfold sourceBudget sourceTemplate IntegralFrozenConstantBounds.lowerHeight
    calc
      _ ≤ IntegralFrozenCoefficientBounds.coefficientHeight (S.arity c) (S.rank c) (S.sourceWidth c) (S.allowance c) 1 1 1 * T +
          IntegralFrozenConstantBounds.constantHeight (S.arity c) (S.rank c) (S.allowance c) 1 1 * T + T :=
        Nat.add_le_add (Nat.add_le_add HC HP) hT
      _ = _ := by ring
  have HW : S.sourceWidth c ≤ S.sourceWidth c * T := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (S.sourceWidth c) hT
  have HCG : I.coefficientHeight c + S.sourceWidth c ≤ (1 + S.sourceWidth c) * T := by
    calc
      _ ≤ T + S.sourceWidth c * T := Nat.add_le_add hC HW
      _ = _ := by ring
  have HG : gradientBudget S I c ≤ gradientTemplate S c * T :=
    coefficient_scaled _ _ _ _ _ _ _ _ _ _ T hT HCG
      (by simpa only [Nat.one_mul] using hV) (by simpa only [Nat.one_mul] using hQ)
  have HD : (S.allowance c).size ≤ (S.allowance c).size * T := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (S.allowance c).size hT
  have HF : (S.free c).size ≤ (S.free c).size * T := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (S.free c).size hT
  unfold lowerBudget lowerTemplate
  calc
    _ ≤ sourceTemplate S c * T + (S.allowance c).size * T + gradientTemplate S c * T + (S.free c).size * T + T :=
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add HS HD) HG) HF) hT
    _ = _ := by ring

theorem leading_scaled (S : Source) (I : Inputs S) (c : List Bool) (T : ℕ) (hT : 1 ≤ T)
    (hQ : I.denominatorHeight c ≤ T) (hP : I.leadingHeight c ≤ T) : leadingBudget S I c ≤ leadingTemplate S c * T := by
  have HD : (S.allowance c).size ≤ (S.allowance c).size * T := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (S.allowance c).size hT
  unfold leadingBudget leadingTemplate
  calc
    _ ≤ T + S.allowance c * T + (S.allowance c).size * T := Nat.add_le_add (Nat.add_le_add hP (Nat.mul_le_mul_left _ hQ)) HD
    _ = _ := by ring

theorem budget_scaled (S : Source) (I : Inputs S) (c : List Bool) (T : ℕ) (hT : 1 ≤ T)
    (hC : I.coefficientHeight c ≤ T) (hV : I.retainedHeight c ≤ T)
    (hQ : I.denominatorHeight c ≤ T) (hP : I.leadingHeight c ≤ T) : budget S I c ≤ factor S c * T := by
  have HL := lower_scaled S I c T hT hC hV hQ hP
  have HP := leading_scaled S I c T hT hQ hP
  have H : lowerBudget S I c + 2 * leadingBudget S I c + 1 ≤ (lowerTemplate S c + 2 * leadingTemplate S c + 1) * T := by
    calc
      _ ≤ lowerTemplate S c * T + 2 * (leadingTemplate S c * T) + T :=
        Nat.add_le_add (Nat.add_le_add HL (Nat.mul_le_mul_left 2 HP)) hT
      _ = _ := by ring
  exact (IntegralClearedCriticalBounds.budget_linear_bound S (derived S I) c).trans
    ((Nat.mul_le_mul_left _ H).trans_eq (Nat.mul_assoc _ _ _).symm)

theorem coefficient_height_scaled (S : Source) (I : Inputs S) (c : List Bool) (T : ℕ) (hT : 1 ≤ T)
    (hC : I.coefficientHeight c ≤ T) (hV : I.retainedHeight c ≤ T)
    (hQ : I.denominatorHeight c ≤ T) (hP : I.leadingHeight c ≤ T)
    (k : ℕ) (r t : Fin (S.rank c)) :
    letI := S.ring c
    (Algebra.leftMulMatrix (S.basis c) ((S.annihilator c).coeff k) r t).natAbs ≤ 2 ^ (factor S c * T) :=
  (coefficient_height S I c k r t).trans
    (Nat.pow_le_pow_right (by decide) (budget_scaled S I c T hT hC hV hQ hP))

end LeanCanny.Algebra.IntegralOriginalCriticalFactorBounds
