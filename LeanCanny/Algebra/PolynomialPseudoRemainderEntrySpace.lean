/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PseudoRemainderEntrySpace

/-! # Streamed parameter coefficients of pseudo-remainder entries

The reduction step uses only head coefficients through its declared degree.
Its sparse entry formula therefore also holds when higher symbolic head
coefficients vanish only after specialization. Each parameter coefficient is
an original coefficient, its modular negation, or zero.
-/

@[expose] public section
namespace LeanCanny.Algebra.PseudoRemainder
open Polynomial Matrix
open scoped Classical

theorem step_low_head {R : Type*} [CommRing R] (p g : R[X]) (d : ℕ) :
    step (low (d + 1) p) d g = step p d g := by
  have hc : (low (d + 1) p).coeff d = p.coeff d := by
    rw [low_coeff, ite_eq_left (Nat.lt_succ_self d)]
  have hl : low d (low (d + 1) p) = low d p := by
    ext i
    simp only [low_coeff]
    by_cases hi : i < d
    · simp only [ite_eq_left hi, ite_eq_left (by omega : i < d + 1)]
    · simp only [ite_eq_right hi]
  simp only [step, hc, hl]

theorem matrix_low_head {R : Type*} [CommRing R] (p : R[X]) (d D : ℕ) :
    matrix (low (d + 1) p) d D = matrix p d D := by
  funext i j
  exact congrArg (fun f : R[X] => f.coeff i.val) (step_low_head p (monomial j.val 1) d)

/-- Higher symbolic coefficients are irrelevant to the fixed reduction step. -/
theorem matrix_apply_sparse_unbounded {R : Type*} [CommRing R] (p : R[X]) (d D : ℕ)
    (i j : Fin (D + 1)) :
    matrix p d D i j =
      if i = j ∧ j.val < d then p.coeff d
      else if i.val < j.val ∧ d ≤ j.val ∧ j.val - d ≤ i.val then
        -p.coeff (i.val - (j.val - d)) else 0 := by
  have hp : (low (d + 1) p).natDegree ≤ d := by
    have h := low_natDegree_lt (d + 1) p (Nat.succ_pos d)
    omega
  rw [← matrix_low_head p d D, matrix_apply_sparse _ d D hp]
  by_cases hpos : i = j ∧ j.val < d
  · simp only [ite_eq_left hpos, low_coeff, ite_eq_left (Nat.lt_succ_self d)]
  · simp only [ite_eq_right hpos]
    by_cases hneg : i.val < j.val ∧ d ≤ j.val ∧ j.val - d ≤ i.val
    · simp only [ite_eq_left hneg, low_coeff, ite_eq_left (by omega : i.val - (j.val - d) < d + 1)]
    · simp only [ite_eq_right hneg]

end LeanCanny.Algebra.PseudoRemainder

namespace LeanCanny.Algebra.PseudoRemainderBits
open Polynomial LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical

/-- The scalar controller also reads a selected parameter coefficient of the
polynomial reduction matrix, without assuming the symbolic head degree. -/
theorem entry_coefficient_correct (a : Access) (c : List Bool) (m d D u : ℕ) [NeZero m]
    (p : ((ZMod m)[X])[X])
    (hd : a.headDegree c = BinaryNatCode.encode d)
    (hm : a.modulus c = BinaryNatCode.encode m)
    (hc : ∀ k, a.coefficient (pair c (BinaryNatCode.encode k)) = residueBits ((p.coeff k).coeff u))
    (i j : Fin (D + 1)) :
    entry a (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
      residueBits ((PseudoRemainder.matrix p d D i j).coeff u) := by
  let q := pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))
  have hpos : positive a q ↔ i = j ∧ j.val < d := by
    simp only [positive, q, row, col, pairFst_pair, pairSnd_pair, hd,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, Fin.ext_iff]
  have hneg : negative a q ↔ i.val < j.val ∧ d ≤ j.val ∧ j.val - d ≤ i.val := by
    simp only [negative, q, row, col, pairFst_pair, pairSnd_pair, hd,
      BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have hidx : index a q =
      if positive a q then BinaryNatCode.encode d
      else BinaryNatCode.encode (i.val - (j.val - d)) := by
    simp only [index, q, row, col, shift, pairFst_pair, pairSnd_pair, hd,
      BinaryNat.sub_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    rfl
  change finish a (pair q (a.coefficient (query a q))) = _
  rw [PseudoRemainder.matrix_apply_sparse_unbounded]
  by_cases h : positive a q
  · rw [ite_eq_left (hpos.mp h)]
    simp only [finish, pairFst_pair, pairSnd_pair, query, hidx, ite_eq_left h,
      q, pairFst_pair, hc]
  · rw [ite_eq_right (fun hn => h (hpos.mpr hn))]
    by_cases hn : negative a q
    · rw [ite_eq_left (hneg.mp hn), Polynomial.coeff_neg]
      simp only [finish, pairFst_pair, pairSnd_pair, ite_eq_left hn,
        query, hidx, ite_eq_right h, q, pairFst_pair, hc, hm]
      exact ArithmeticBits.negate_residueBits m _
    · rw [ite_eq_right (fun h' => hn (hneg.mpr h'))]
      simp only [finish, pairFst_pair, pairSnd_pair, ite_eq_right h, ite_eq_right hn]
      simp [residueBits, BinaryNatCode.encode]

end LeanCanny.Algebra.PseudoRemainderBits
