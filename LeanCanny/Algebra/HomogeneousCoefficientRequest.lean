/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.RelativeValueSystemMap
public import LeanCanny.Algebra.HomogenizationBinarySpace
public import LeanCanny.Algebra.DiagonalPolynomialParameterSpace
public import LeanCanny.Computation.SingleCallController

/-! # Native homogenization requests without a coefficient evaluator

The clipped total-degree guard is polynomial time for a binary degree.
Only the emitted coefficient request is charged to the lower stage.
The coefficient identity applies over arbitrary finite coefficient algebras,
including the two nilpotent extensions used by the value system.
-/

@[expose] public section
namespace LeanCanny.Algebra.HomogeneousCoefficientRequest
open LeanCanny.Encoding LeanCanny.Computation FixedWidthPolynomial

def program (N W D : List Bool → ℕ) : SingleCall.Program where
  request p := decide (HomogenizationBits.total N N W D p = D (pairFst p))
  query := HomogenizationBits.oldQuery W
  immediate _ := []
  finish := pairSnd

theorem controls (N W D : List Bool → ℕ) (hN : UnaryFn N) (hW : UnaryFn W) (hD : BinaryFn D) :
    (program N W D).Controls :=
  ⟨((HomogenizationBits.total_binary hN hN hW hD).eq (hD.comp pairFst_mem_FP)).flag_mem_FP,
    HomogenizationBits.oldQuery_mem_FP hW, constFn_mem_FP [], pairSnd_mem_FP⟩

theorem homogeneousRows_eq {A : Type*} [CommRing A] {n : ℕ}
    (p : Fin n → MvPolynomial (Fin n) A) (d : Fin n → ℕ) (j : Fin n) :
    AffineRingCoordinates.homogeneousRows p d j = RelativeValueSystemMap.homogeneousTest (p j) (d j) := rfl

theorem coefficient_rank {A : Type*} [CommRing A] {n : ℕ}
    (p : MvPolynomial (Fin n) A) (D W k : ℕ) :
    (RelativeValueSystemMap.homogeneousTest p D).coeff (nativeExponent (Equiv.refl _) W k) =
      if HomogenizationLayout.weightedSum n n W k = D then
        p.coeff (nativeExponent (Equiv.refl _) W (Nat.fromBitsLE (k.bits.drop W))) else 0 := by
  rw [RelativeValueSystemMap.homogeneousTest, nativeExponent_refl, coeff_rename_rank]
  simpa only [HomogenizationLayout.prefixWeight_all, AffineFiniteCoordinates.layout] using
    HomogenizationLayout.coefficient_rank (Equiv.refl _) n D W k p

theorem actual_value {A : Type*} [CommRing A]
    (N W D : List Bool → ℕ) (reply : List Bool → List Bool) (c : List Bool)
    (p : MvPolynomial (Fin (N c)) A) (enc : A → List Bool) (hz : enc 0 = []) (k : ℕ)
    (ha : HomogenizationBits.total N N W D (pair c (BinaryNatCode.encode k)) = D c →
      reply (HomogenizationBits.oldQuery W (pair c (BinaryNatCode.encode k))) =
        enc (p.coeff (nativeExponent (Equiv.refl _) (W c) (Nat.fromBitsLE (k.bits.drop (W c)))))) :
    (program N W D).value reply (pair c (BinaryNatCode.encode k)) =
      enc ((RelativeValueSystemMap.homogeneousTest p (D c)).coeff
        (nativeExponent (Equiv.refl _) (W c) k)) := by
  have HG := HomogenizationBits.total_eq_iff N N W D (pair c (BinaryNatCode.encode k))
  simp only [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits] at HG
  rw [coefficient_rank]
  by_cases H : HomogenizationBits.total N N W D (pair c (BinaryNatCode.encode k)) = D c
  · simp only [SingleCall.Program.value, program, pairFst_pair, H, decide_true, ite_true, pairSnd_pair,
      ha H, ite_eq_left (HG.mp H)]
  · simp only [SingleCall.Program.value, program, pairFst_pair, H, decide_false, Bool.false_eq_true,
      ite_false, ite_eq_right (fun h => H (HG.mpr h)), hz]

/-- Homogeneous coordinate rows request one coefficient of that same coordinate. -/
theorem diagonal_coefficient {A : Type*} [CommRing A] {n : ℕ}
    (p : Polynomial A) (i : Fin n) (D W k : ℕ) :
    (RelativeValueSystemMap.homogeneousTest (p.toMvPolynomial i) D).coeff
        (nativeExponent (Equiv.refl _) W k) =
      if HomogenizationLayout.weightedSum n n W k = D ∧
          (∀ j : Fin n, j ≠ i →
            nativeExponent (Equiv.refl _) W (Nat.fromBitsLE (k.bits.drop W)) j = 0) then
        p.coeff (entry W k (i.val + 1)) else 0 := by
  rw [coefficient_rank, DiagonalParameterBits.coefficient]
  have HE : nativeExponent (Equiv.refl (Fin n)) W (Nat.fromBitsLE (k.bits.drop W)) i =
      entry W k (i.val + 1) := HomogenizationLayout.entry_drop W k i.val
  rw [HE]
  split_ifs <;> simp_all

end LeanCanny.Algebra.HomogeneousCoefficientRequest
