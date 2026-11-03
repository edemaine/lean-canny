/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCoordinatePoweredSpace
/-! # Powered coefficient access with current-modulus matrix replies

Only the modulus already present in each coefficient input is queried. This
retains the actual caller-root budget without imposing replies for unrelated
moduli on that same task word.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCoordinateCoefficientBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
universe u

theorem packet_local (F : Family) (target modulus entry : List Bool → List Bool)
    (he : ∀ c (i j : Fin (count (F.arity c) (F.width c))),
      entry (pair (pair c (modulus c)) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
        residueBits ((F.matrix c i j : ℤ) : ZMod (Nat.fromBitsLE (modulus c) + 1))) (c : List Bool) :
    entry (query F target modulus c) = FixedWidthRowBits.value F.arity F.width F.polynomial target modulus c := by
  let word := FixedWidthQuery.repack F.arity F.width F.arity F.width target c
  let rank := Nat.fromBitsLE word
  have HR : rank < count (F.arity c) (F.width c) := by
    have H := Nat.fromBitsLE_lt_pow_length word
    rw [FixedWidthQuery.repack_length] at H
    simpa only [count, ← pow_mul, Nat.mul_comm (F.width c)] using H
  have HV : vector (F.arity c) (F.width c) ⟨rank, HR⟩ =
      nativeExponent (Equiv.refl _) (F.width c) (Nat.fromBitsLE (target c)) := by
    calc
      _ = nativeExponent (Equiv.refl _) (F.width c) rank :=
        ((nativeExponent_refl _ _ _).trans (entry_vector _ _ ⟨rank, HR⟩)).symm
      _ = _ := nativeExponent_repack (Equiv.refl _) F.width F.width target c le_rfl
  have HQ : query F target modulus c = pair (pair c (modulus c))
      (pair (BinaryNatCode.encode (⟨rank, HR⟩ : Fin (count (F.arity c) (F.width c))).val)
        (BinaryNatCode.encode (IntegralCoordinateBasis.zeroFin (F.arity c) (F.width c)).val)) := by
    simp only [query, IntegralCoordinateBasis.zeroFin, BinaryNat.normalize_eq_bits]
    rfl
  rw [HQ, he]
  have HC : F.matrix c ⟨rank, HR⟩ (IntegralCoordinateBasis.zeroFin (F.arity c) (F.width c)) =
      (F.polynomial c).coeff (nativeExponent (Equiv.refl _) (F.width c) (Nat.fromBitsLE (target c))) := by
    rw [← F.coefficient c ⟨rank, HR⟩, HV]
  rw [HC]
  rfl

theorem evaluator_local (F : Family) (target modulus entry : List Bool → List Bool)
    (hA : UnaryFn F.arity) (hW : UnaryFn F.width) (ht : target ∈ FP) (hm : modulus ∈ FP)
    (E : SpaceFunction entry)
    (he : ∀ c (i j : Fin (count (F.arity c) (F.width c))),
      entry (pair (pair c (modulus c)) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
        residueBits ((F.matrix c i j : ℤ) : ZMod (Nat.fromBitsLE (modulus c) + 1))) :
    SpaceFunction (FixedWidthRowBits.value F.arity F.width F.polynomial target modulus) :=
  (E.precompose _ (query_FP F target modulus hA hW ht hm)).congr (funext fun c => packet_local F target modulus entry he c)

theorem wide_evaluator_local (F : Family) (V : List Bool → ℕ) (target modulus entry : List Bool → List Bool)
    (hA : UnaryFn F.arity) (hB : UnaryFn F.width) (hV : UnaryFn V)
    (ht : target ∈ FP) (hm : modulus ∈ FP) (E : SpaceFunction entry)
    (he : ∀ c (i j : Fin (count (F.arity c) (F.width c))),
      entry (pair (pair c (modulus c)) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
        residueBits ((F.matrix c i j : ℤ) : ZMod (Nat.fromBitsLE (modulus c) + 1))) :
    SpaceFunction (FixedWidthRowBits.value F.arity V F.polynomial target modulus) := by
  have HR := evaluator_local F (FixedWidthQuery.repack F.arity V F.arity F.width target) modulus entry
    hA hB (FixedWidthQuery.repack_mem_FP hA hV hA hB ht) hm E he
  have HG := SpaceFunction.branch (fun c => decide (Fits F V target c))
    (fits_FP F V target hA hB hV ht).flag_mem_FP HR (SpaceFunction.ofFP _ (constFn_mem_FP []))
  refine HG.congr (funext fun c => ?_)
  simp only [FixedWidthRowBits.value]
  rw [wide_coefficient F V target c]
  by_cases hf : Fits F V target c
  · simp only [hf, decide_eq_true_eq, ite_true]
  · simp only [hf, decide_eq_true_eq, ite_false, Int.cast_zero, residueBits, ZMod.val_zero, BinaryNatCode.encode]
    rfl

open UniformIntegralPowerSchedule
theorem powered_evaluator_local (F : Family) (S V : List Bool → ℕ) (target modulus entry : List Bool → List Bool)
    (hS : UnaryFn S) (hA : UnaryFn F.arity) (hB : UnaryFn F.width) (hV : UnaryFn V)
    (ht : target ∈ FP) (hm : modulus ∈ FP) (E : SpaceFunction entry)
    (he : ∀ c (i j : Fin (count (F.arity c) (F.width c))),
      entry (pair (pair c (modulus c)) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
        residueBits ((F.matrix c i j : ℤ) : ZMod (Nat.fromBitsLE (modulus c) + 1))) :
    SpaceFunction (FixedWidthRowBits.value F.arity V (F.poweredPolynomial S) target modulus) := by
  let N : List Bool → ℕ := fun c => 2 ^ F.width c
  let powers := UniformIntegralPowerSchedule.power S N F.arity
  have hN : BinaryFn N := (BinaryFn.const 2).powUnary hB
  have hP : BinaryFn powers := power_binary hS hN hA
  have HP (c : List Bool) (i : Fin (F.arity c)) :
      powers (pair c (BinaryNatCode.encode i.val)) = weights (S c) (2 ^ F.width c) (F.arity c) i :=
    power_packet S N F.arity c i
  have HR := wide_evaluator_local F V (FixedWidthCoordinatePowerBits.quotientTarget F.arity V powers target)
    modulus entry hA hB hV (FixedWidthCoordinatePowerBits.quotientTarget_FP F.arity V powers target hA hV hP ht)
    hm E he
  have HE := FixedWidthCoordinatePowerBits.evaluator F.arity V powers target F.polynomial modulus
    (fun c i => by rw [HP]; exact weights_pos _ _ _ _) hA hV hP ht HR
  refine HE.congr (funext fun c => ?_)
  have HW : (fun i : Fin (F.arity c) => powers (pair c (BinaryNatCode.encode i.val))) =
      weights (S c) (2 ^ F.width c) (F.arity c) := funext (HP c)
  simp only [FixedWidthRowBits.value, Family.poweredPolynomial, HW]

end LeanCanny.Algebra.IntegralCoordinateCoefficientBits
