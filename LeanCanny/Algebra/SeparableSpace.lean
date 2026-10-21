/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ResultantSpace
public import LeanCanny.Algebra.SeparableResultant
public import LeanCanny.Algebra.DerivativeCoefficientSpace
public import LeanCanny.Computation.SpaceDeciderFunction

/-! # Native separability tests from streamed integer coefficients

Only the actual degree and a coefficient-height exponent must be FP. Source
coefficients may take arbitrary time in polynomial space. The derivative height
and determinant budget are derived internally. Nonzero constants are accepted.
-/

@[expose] public section

namespace LeanCanny.Algebra.SeparableBits
open Polynomial
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
attribute [local irreducible] BinaryNat.add BinaryNat.sub

structure Family where
  polynomial : List Bool → ℤ[X]
  height : List Bool → ℕ
  coefficient_bound : ∀ c k, ((polynomial c).coeff k).natAbs ≤ 2 ^ height c

structure Readers (F : Family) where
  degree : List Bool → List Bool
  height : List Bool → List Bool
  coefficient : List Bool → List Bool
  degreeFP : degree ∈ FP
  heightFP : height ∈ FP
  degree_eq : ∀ c, degree c = BinaryNatCode.encode (F.polynomial c).natDegree
  height_eq : ∀ c, height c = BinaryNatCode.encode (F.height c)
  coefficient_eq : ∀ q k, coefficient (pair q (BinaryNatCode.encode k)) =
    residueBits (((F.polynomial (pairFst q)).coeff k : ℤ) : ZMod (Nat.fromBitsLE (pairSnd q) + 1))
  evaluator : SpaceFunction coefficient

theorem derivative_bound (p : ℤ[X]) (b : ℕ)
    (h : ∀ k, (p.coeff k).natAbs ≤ 2 ^ b) (k : ℕ) :
    (p.derivative.coeff k).natAbs ≤ 2 ^ (b + p.natDegree.size) := by
  rw [coeff_derivative, ← Nat.cast_add_one, Int.natAbs_mul, Int.natAbs_natCast]
  by_cases hk : k + 1 ≤ p.natDegree
  · calc
      _ ≤ 2 ^ b * 2 ^ p.natDegree.size :=
        Nat.mul_le_mul (h _) (hk.trans (Nat.lt_size_self _).le)
      _ = _ := (pow_add _ _ _).symm
  · rw [coeff_eq_zero_of_natDegree_lt (by omega), Int.natAbs_zero, zero_mul]
    exact Nat.zero_le _

noncomputable def resultantFamily (F : Family) : Resultant.Family where
  left := F.polynomial
  right c := (F.polynomial c).derivative
  leftDegree c := (F.polynomial c).natDegree
  rightDegree c := (F.polynomial c).natDegree - 1
  coefficientBits c := F.height c + (F.polynomial c).natDegree.size
  left_bound c k := (F.coefficient_bound c k).trans (Nat.pow_le_pow_right (by decide) (by omega))
  right_bound c k := derivative_bound _ _ (F.coefficient_bound c) k

def derivativeDegree {F : Family} (A : Readers F) (c : List Bool) : List Bool :=
  BinaryNat.sub (pair (A.degree c) (BinaryNatCode.encode 1))

def derivativeHeight {F : Family} (A : Readers F) (c : List Bool) : List Bool :=
  BinaryNat.add (pair (A.height c) (BinaryNatCode.encode (A.degree c).length))

def modulus (q : List Bool) : List Bool := BinaryNat.succ (pairSnd q)

theorem modulus_FP : modulus ∈ FP := mem_FP_comp pairSnd_mem_FP BinaryNat.succ_mem_FP

noncomputable def access (F : Family) (A : Readers F) : Resultant.Access (resultantFamily F) where
  bits := ⟨A.degree, derivativeDegree A, derivativeHeight A, A.coefficient,
    DerivativeBits.value modulus A.coefficient⟩
  leftDegree := A.degree_eq
  rightDegree c := by
    simp only [derivativeDegree, A.degree_eq, BinaryNat.sub_pair, BinaryNatCode.encode,
      Nat.fromBitsLE_bits, resultantFamily]
  coefficientBits c := by
    simp only [derivativeHeight, A.height_eq, A.degree_eq, BinaryNat.add_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, ← Nat.size_eq_bits_len, resultantFamily]
  leftCoefficient := A.coefficient_eq
  rightCoefficient q k := by
    have h := DerivativeBits.packet modulus A.coefficient q _
      ((F.polynomial (pairFst q)).map (Int.castRingHom (ZMod (Nat.fromBitsLE (pairSnd q) + 1))))
      (by simp only [modulus, BinaryNat.succ_eq_bits, BinaryNatCode.encode])
      (fun k => by simpa only [coeff_map, Int.coe_castRingHom] using A.coefficient_eq q k) k
    simpa only [derivative_map, coeff_map, Int.coe_castRingHom, resultantFamily] using h

theorem access_controls (F : Family) (A : Readers F) : (access F A).bits.ControlsPolyTime := by
  have hd := mem_FP_comp (mem_FP_pair A.degreeFP (constFn_mem_FP (BinaryNatCode.encode 1))) BinaryNat.sub_mem_FP
  have hh := mem_FP_comp (mem_FP_pair A.heightFP (bits_mem_FP (UnaryFn.length A.degreeFP))) BinaryNat.add_mem_FP
  have hd' : derivativeDegree A ∈ FP := mem_FP_of_eq hd (fun _ => rfl)
  have hh' : derivativeHeight A ∈ FP := mem_FP_of_eq hh (fun _ => rfl)
  exact ⟨A.degreeFP, hd', hh'⟩

def language (F : Family) : Language := {c | ((F.polynomial c).map (Int.castRingHom ℚ)).Separable}

theorem decider (F : Family) (A : Readers F) (hne : ∀ c, F.polynomial c ≠ 0) :
    SpaceDecider (language F) := by
  have EL : SpaceFunction (access F A).bits.leftCoefficient := by
    simpa only [access] using A.evaluator
  have ER : SpaceFunction (access F A).bits.rightCoefficient := by
    simpa only [access] using DerivativeBits.evaluator A.evaluator modulus modulus_FP
  have D := Resultant.Access.deciderWithCoefficients (access F A) (access_controls F A)
    EL ER
  have E := D.flagEvaluator
  refine E.decider (fun b => !(b[0]?.getD false)) ?_ ?_
  · simpa using (FPPred.getBit id_mem_FP (UnaryFn.const 0)).not.flag_mem_FP
  · intro c
    simp only [List.getElem?_cons_zero, Option.getD_some, Bool.not_eq_true', decide_eq_false_iff_not]
    change ((F.polynomial c).map (Int.castRingHom ℚ)).Separable ↔
      ¬ (F.polynomial c).resultant (F.polynomial c).derivative
        (F.polynomial c).natDegree ((F.polynomial c).natDegree - 1) = 0
    rw [← natDegree_derivative]
    exact integer_separable_iff_resultant_ne_zero _ (hne c)

end LeanCanny.Algebra.SeparableBits
