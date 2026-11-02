/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.FermatLevelCoefficient
public import LeanCanny.ETR.SizedCollectedCoefficient
/-! # Native appended-coordinate and unit-monomial guards -/
@[expose] public section
namespace LeanCanny.Algebra.FermatLevelCoefficientBits
open LeanCanny.Encoding LeanCanny.Computation FixedWidthPolynomial

def lastExponent (N W : List Bool → ℕ) (p : List Bool) :=
  entry (W (pairFst p)) (Nat.fromBitsLE (pairSnd p)) (N (pairFst p))

theorem lastExponent_binary {N W : List Bool → ℕ} (hN : UnaryFn N) (hW : UnaryFn W) :
    BinaryFn (lastExponent N W) := by
  have HN := hN.comp pairFst_mem_FP
  have HW := hW.comp pairFst_mem_FP
  have HR := take_mem_FP (drop_mem_FP (mem_FP_comp pairSnd_mem_FP BinaryNat.normalize_mem_FP) (HN.mul HW)) HW
  exact (BinaryFn.fromBits HR).of_eq (fun p => by
    simp only [lastExponent, entry, BinaryNat.normalize_eq_bits, Function.comp_apply])

def OldZero (N W : List Bool → ℕ) (p : List Bool) : Prop :=
  ∀ i < N (pairFst p), entry (W (pairFst p)) (Nat.fromBitsLE (pairSnd p)) i = 0

theorem oldZero_fppred {N W : List Bool → ℕ} (hN : UnaryFn N) (hW : UnaryFn W) : FPPred (OldZero N W) := by
  apply (FixedWidthQuery.bounded_fppred (hN.comp pairFst_mem_FP) (hW.comp pairFst_mem_FP)
    (UnaryFn.const 0) (mem_FP_comp pairSnd_mem_FP BinaryNat.normalize_mem_FP)).of_iff
  intro p
  unfold FixedWidthQuery.Bounded OldZero
  have HC : FixedWidthQuery.coordinate (fun q => W (pairFst q)) (BinaryNat.normalize ∘ pairSnd) p =
      entry (W (pairFst p)) (Nat.fromBitsLE (pairSnd p)) := by
    funext i
    simp only [FixedWidthQuery.coordinate, Function.comp_apply, BinaryNat.normalize_eq_bits, entry]
  rw [HC]
  exact forall₂_congr (fun _ _ => Nat.le_zero)

def IsLast (N W : List Bool → ℕ) (p : List Bool) : Prop :=
  FermatLevelCoefficient.IsLast (N (pairFst p)) (W (pairFst p)) (Nat.fromBitsLE (pairSnd p))

theorem isLast_fppred {N W : List Bool → ℕ} (hN : UnaryFn N) (hW : UnaryFn W) : FPPred (IsLast N W) :=
  ((lastExponent_binary hN hW).eq (BinaryFn.const 1)).and (oldZero_fppred hN hW)

theorem lastExponent_bits {N W : List Bool → ℕ} (p : List Bool) :
    (lastExponent N W p).size ≤ W (pairFst p) := by
  exact Nat.size_le.mpr (entry_lt _ _ _)

end LeanCanny.Algebra.FermatLevelCoefficientBits
