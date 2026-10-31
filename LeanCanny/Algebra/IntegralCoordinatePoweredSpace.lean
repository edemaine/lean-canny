/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCoordinateWideSpace
public import LeanCanny.Algebra.FixedWidthCoordinatePowerSpace
public import LeanCanny.Algebra.UniformIntegralPowerSchedule

/-! # Native powered canonical heights from original matrix entries

Coordinate-dependent division undoes the fixed scalar powers. The basis-box
guard then rejects impossible exponents and repacks a single original
matrix query. Query widths and the exponential basis radix are independent;
the original matrix program retains its full space charge.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCoordinateCoefficientBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open UniformIntegralPowerSchedule
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def Family.poweredPolynomial (F : Family) (S : List Bool → ℕ) (c : List Bool) :
    MvPolynomial (Fin (F.arity c)) ℤ :=
  CoordinatePowerSubstitution.substitute (weights (S c) (2 ^ F.width c) (F.arity c)) (F.polynomial c)

theorem powered_evaluator (F : Family) (S V : List Bool → ℕ) (target modulus entry : List Bool → List Bool)
    (hS : UnaryFn S) (hA : UnaryFn F.arity) (hB : UnaryFn F.width) (hV : UnaryFn V)
    (ht : target ∈ FP) (hm : modulus ∈ FP) (E : SpaceFunction entry)
    (he : ∀ c mw (i j : Fin (count (F.arity c) (F.width c))),
      entry (pair (pair c mw) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
        residueBits ((F.matrix c i j : ℤ) : ZMod (Nat.fromBitsLE mw + 1))) :
    SpaceFunction (FixedWidthRowBits.value F.arity V (F.poweredPolynomial S) target modulus) := by
  let N : List Bool → ℕ := fun c => 2 ^ F.width c
  let powers := UniformIntegralPowerSchedule.power S N F.arity
  have hN : BinaryFn N := (BinaryFn.const 2).powUnary hB
  have hP : BinaryFn powers := power_binary hS hN hA
  have HP (c : List Bool) (i : Fin (F.arity c)) :
      powers (pair c (BinaryNatCode.encode i.val)) = weights (S c) (2 ^ F.width c) (F.arity c) i :=
    power_packet S N F.arity c i
  have HR := wide_evaluator F V (FixedWidthCoordinatePowerBits.quotientTarget F.arity V powers target)
    modulus entry hA hB hV (FixedWidthCoordinatePowerBits.quotientTarget_FP F.arity V powers target hA hV hP ht)
    hm E he
  have HE := FixedWidthCoordinatePowerBits.evaluator F.arity V powers target F.polynomial modulus
    (fun c i => by rw [HP]; exact weights_pos _ _ _ _) hA hV hP ht HR
  refine HE.congr (funext fun c => ?_)
  have HW : (fun i : Fin (F.arity c) => powers (pair c (BinaryNatCode.encode i.val))) =
      weights (S c) (2 ^ F.width c) (F.arity c) := funext (HP c)
  simp only [FixedWidthRowBits.value, Family.poweredPolynomial, HW]

end LeanCanny.Algebra.IntegralCoordinateCoefficientBits
