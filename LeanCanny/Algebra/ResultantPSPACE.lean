/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SylvesterAccessCorrect

/-!
# Polynomial-space zero testing of integer resultants

FP binary degree parameters and coefficient-bit budgets, together with uniform
FP coefficient residue access, instantiate the integer determinant decider.
The specified-degree resultant is used throughout. A corollary uses the actual
polynomial degrees when the supplied degree fields agree with them.
-/

@[expose] public section

namespace LeanCanny.Algebra.Resultant
open Complexity
open LeanCanny.Encoding
open LeanCanny.Computation
open MatrixPower

structure Family where
  left : List Bool → Polynomial ℤ
  right : List Bool → Polynomial ℤ
  leftDegree : List Bool → ℕ
  rightDegree : List Bool → ℕ
  coefficientBits : List Bool → ℕ
  left_bound : ∀ c k, ((left c).coeff k).natAbs ≤ 2 ^ coefficientBits c
  right_bound : ∀ c k, ((right c).coeff k).natAbs ≤ 2 ^ coefficientBits c

def Family.zeroLanguage (F : Family) : Language :=
  {c | (F.left c).resultant (F.right c) (F.leftDegree c) (F.rightDegree c) = 0}

def Family.standardZeroLanguage (F : Family) : Language :=
  {c | (F.left c).resultant (F.right c) = 0}

def Family.integer (F : Family) : Berkowitz.IntegerFamily where
  dimension := fun c => F.leftDegree c + F.rightDegree c
  matrix := fun c => Polynomial.sylvester (F.left c) (F.right c) (F.leftDegree c) (F.rightDegree c)
  budget := fun c => (F.leftDegree c + F.rightDegree c).size * (F.leftDegree c + F.rightDegree c) +
    (F.leftDegree c + F.rightDegree c) * F.coefficientBits c + 1
  determinant_bits := fun c => SylvesterBits.resultant_size_le _ _ _ _ _ (F.left_bound c) (F.right_bound c)

/-- Modular coefficient context `q` specifies original input `pairFst q` and
modulus `fromBitsLE (pairSnd q) + 1`. The coefficient index is a binary natural.
The contract covers every context and every coefficient index. -/
structure Access (F : Family) where
  bits : SylvesterBits.Access
  leftDegree : ∀ c, bits.leftDegree c = BinaryNatCode.encode (F.leftDegree c)
  rightDegree : ∀ c, bits.rightDegree c = BinaryNatCode.encode (F.rightDegree c)
  coefficientBits : ∀ c, bits.coefficientBits c = BinaryNatCode.encode (F.coefficientBits c)
  leftCoefficient : ∀ q k, bits.leftCoefficient (pair q (BinaryNatCode.encode k)) =
    residueBits (((F.left (pairFst q)).coeff k : ℤ) : ZMod (Nat.fromBitsLE (pairSnd q) + 1))
  rightCoefficient : ∀ q k, bits.rightCoefficient (pair q (BinaryNatCode.encode k)) =
    residueBits (((F.right (pairFst q)).coeff k : ℤ) : ZMod (Nat.fromBitsLE (pairSnd q) + 1))

namespace Access

def integer {F : Family} (a : Access F) : Berkowitz.IntegerAccess F.integer where
  dimension := SylvesterBits.dimension a.bits
  budget := SylvesterBits.budget a.bits
  entry := SylvesterBits.entry a.bits
  dimension_eq := fun c => SylvesterBits.dimension_code _ c _ _ (a.leftDegree c) (a.rightDegree c)
  budget_eq := fun c => SylvesterBits.budget_code _ c _ _ _
    (a.leftDegree c) (a.rightDegree c) (a.coefficientBits c)
  entry_eq := by
    intro q i j
    exact SylvesterBits.entry_correct a.bits q (F.left (pairFst q)) (F.right (pairFst q))
      (F.leftDegree (pairFst q)) (F.rightDegree (pairFst q))
      (fun z : ℤ => residueBits (z : ZMod (Nat.fromBitsLE (pairSnd q) + 1)))
      ⟨a.leftDegree _, a.rightDegree _, a.leftCoefficient q, a.rightCoefficient q,
        by simp [residueBits, BinaryNatCode.encode]⟩ i j

theorem integer_polyTime {F : Family} (a : Access F) (ha : a.bits.PolyTime) : a.integer.PolyTime := by
  constructor
  · simpa only [integer] using SylvesterBits.dimension_mem_FP a.bits ha
  · simpa only [integer] using SylvesterBits.budget_mem_FP a.bits ha
  · simpa only [integer] using SylvesterBits.entry_mem_FP a.bits ha

theorem decider {F : Family} (a : Access F) (ha : a.bits.PolyTime) :
    SpaceDecider F.zeroLanguage :=
  Berkowitz.IntegerAccess.decider a.integer (integer_polyTime a ha)

theorem zeroLanguage_mem_PSPACE {F : Family} (a : Access F) (ha : a.bits.PolyTime) :
    F.zeroLanguage ∈ PSPACE := (decider a ha).mem_PSPACE

theorem standardZeroLanguage_mem_PSPACE {F : Family} (a : Access F) (ha : a.bits.PolyTime)
    (hm : ∀ c, F.leftDegree c = (F.left c).natDegree)
    (hn : ∀ c, F.rightDegree c = (F.right c).natDegree) : F.standardZeroLanguage ∈ PSPACE := by
  have h : F.zeroLanguage = F.standardZeroLanguage := by
    ext c
    simp only [Family.zeroLanguage, Family.standardZeroLanguage, hm, hn]
  rw [← h]
  exact zeroLanguage_mem_PSPACE a ha

end Access
end LeanCanny.Algebra.Resultant
