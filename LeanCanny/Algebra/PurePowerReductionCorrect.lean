/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PurePowerReductionSpace
public import LeanCanny.Algebra.PurePowerReductionMatrix

/-! # Correctness of streamed pure-power reduction entries

Native exponent subtraction reads the concrete degree-decreasing matrix,
with source columns queried before target rows. Bounds remain binary.
-/

@[expose] public section

namespace LeanCanny.Algebra.PurePowerReductionBits

open LeanCanny.Encoding
open scoped BigOperators

abbrev Degrees (L : Layout) (c : List Bool) : Fin (L.arity c) → ℕ := fun i => L.degree c i

abbrev Indices (L : Layout) (q : List Bool) := PurePowerReductionMatrix.Index (L.arity (pairFst q)) (L.width (pairFst q))

def packet (q : List Bool) (r s : ℕ) : List Bool :=
  pair q (pair (BinaryNatCode.encode r) (BinaryNatCode.encode s))

@[simp] theorem context_packet (q : List Bool) (r s : ℕ) : context (packet q r s) = pairFst q := by
  simp only [packet, context, pairFst_pair]

@[simp] theorem row_packet (q : List Bool) (r s : ℕ) : row (packet q r s) = BinaryNatCode.encode r := by
  simp only [packet, row, pairFst_pair, pairSnd_pair]

@[simp] theorem col_packet (q : List Bool) (r s : ℕ) : col (packet q r s) = BinaryNatCode.encode s := by
  simp only [packet, col, pairSnd_pair]

theorem rowAt_packet (L : Layout) (q : List Bool) (r : Indices L q) (s : ℕ) (i : Fin (L.arity (pairFst q))) :
    rowAt L (packet q r.val s) i.val = FixedWidthPolynomial.vector _ _ r i := by
  simp only [rowAt, FixedWidthQuery.entry, Function.comp_apply, context_packet, i.isLt, ite_true,
    FixedWidthQuery.coordinate, row_packet, BinaryNatCode.encode]
  exact (FixedWidthPolynomial.entry_eq_digit _ _ _).trans (FixedWidthPolynomial.vector_apply _ _ r i).symm

theorem colAt_packet (L : Layout) (q : List Bool) (r : ℕ) (s : Indices L q) (i : Fin (L.arity (pairFst q))) :
    colAt L (packet q r s.val) i.val = FixedWidthPolynomial.vector _ _ s i := by
  simp only [colAt, FixedWidthQuery.entry, Function.comp_apply, context_packet, i.isLt, ite_true,
    FixedWidthQuery.coordinate, col_packet, BinaryNatCode.encode]
  exact (FixedWidthPolynomial.entry_eq_digit _ _ _).trans (FixedWidthPolynomial.vector_apply _ _ s i).symm

theorem normal_packet (L : Layout) (q : List Bool) (r : Indices L q) (s : ℕ) :
    normal L (packet q r.val s) ↔ PurePowerReductionMatrix.Normal (Degrees L (pairFst q))
      (FixedWidthPolynomial.vector _ _ r) := by
  constructor
  · intro H i
    simpa only [rowAt_packet, context_packet, Degrees] using H i.val (by simp only [context_packet]; exact i.isLt)
  · intro H i hi
    have hn : i < L.arity (pairFst q) := by simpa only [context_packet] using hi
    change rowAt L (packet q r.val s) (⟨i, hn⟩ : Fin (L.arity (pairFst q))).val < _
    rw [rowAt_packet, context_packet]
    exact H ⟨i, hn⟩

theorem valid_packet (L : Layout) (bound : List Bool → ℕ) (q : List Bool) (r : Indices L q) (s : ℕ) :
    valid L bound (packet q r.val s) ↔ (FixedWidthPolynomial.vector _ _ r).degree ≤ bound (pairFst q) := by
  simp only [valid, rowTotal, context_packet, Finset.sum_range, rowAt_packet, Finsupp.degree_eq_sum]

theorem selected_le {n : ℕ} (fallback : Fin n) (d : Fin n → ℕ) (e : Fin n →₀ ℕ)
    (_he : ¬PurePowerReductionMatrix.Normal d e) (i : Fin n) (hi : d i ≤ e i) :
    PurePowerReductionMatrix.selected fallback d e ≤ i := by
  classical
  have H : (PurePowerReductionMatrix.candidates d e).Nonempty :=
    ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  rw [PurePowerReductionMatrix.selected, dite_eq_left H]
  have HI : i ∈ PurePowerReductionMatrix.candidates d e := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
  exact Finset.min'_le _ _ HI

theorem pivot_packet (L : Layout) (q : List Bool) (r : Indices L q) (s : ℕ)
    (fallback : Fin (L.arity (pairFst q)))
    (hr : ¬PurePowerReductionMatrix.Normal (Degrees L (pairFst q)) (FixedWidthPolynomial.vector _ _ r)) :
    pivot L (packet q r.val s) =
      (PurePowerReductionMatrix.selected fallback (Degrees L (pairFst q)) (FixedWidthPolynomial.vector _ _ r)).val := by
  rw [pivot, context_packet, List.findIdx_eq (by simp)]
  simp only [List.getElem_range, decide_eq_true_eq, decide_eq_false_iff_not]
  constructor
  · rw [rowAt_packet]
    exact PurePowerReductionMatrix.selected_divides fallback _ _ hr
  · intro j hj
    have hjn : j < L.arity (pairFst q) := hj.trans (PurePowerReductionMatrix.selected fallback (Degrees L (pairFst q)) (FixedWidthPolynomial.vector _ _ r)).isLt
    rw [show j = (⟨j, hjn⟩ : Fin (L.arity (pairFst q))).val from rfl, rowAt_packet]
    intro hd
    have H := selected_le fallback _ _ hr ⟨j, hjn⟩ hd
    have HV : (PurePowerReductionMatrix.selected fallback (Degrees L (pairFst q)) (FixedWidthPolynomial.vector _ _ r)).val ≤ j := H
    omega

theorem remainderAt_packet (L : Layout) (q : List Bool) (r : Indices L q) (s : ℕ)
    (fallback : Fin (L.arity (pairFst q)))
    (hr : ¬PurePowerReductionMatrix.Normal (Degrees L (pairFst q)) (FixedWidthPolynomial.vector _ _ r))
    (i : Fin (L.arity (pairFst q))) :
    remainderAt L (packet q r.val s) i.val = MonicMonomialReduction.residual (FixedWidthPolynomial.vector _ _ r)
      (PurePowerReductionMatrix.selected fallback (Degrees L (pairFst q)) (FixedWidthPolynomial.vector _ _ r))
      (Degrees L (pairFst q) (PurePowerReductionMatrix.selected fallback (Degrees L (pairFst q)) (FixedWidthPolynomial.vector _ _ r))) i := by
  rw [remainderAt, rowAt_packet, pivot_packet L q r s fallback hr, context_packet]
  simp only [MonicMonomialReduction.residual, Finsupp.tsub_apply, Finsupp.single_apply, Degrees]
  have H : i.val = (PurePowerReductionMatrix.selected fallback (Degrees L (pairFst q))
      (FixedWidthPolynomial.vector _ _ r)).val ↔
      PurePowerReductionMatrix.selected fallback (Degrees L (pairFst q)) (FixedWidthPolynomial.vector _ _ r) = i := by
    constructor
    · intro h; exact Fin.ext h.symm
    · intro h; exact congrArg Fin.val h.symm
  simp only [H]

theorem admissible_packet (L : Layout) (q : List Bool) (r s : Indices L q)
    (fallback : Fin (L.arity (pairFst q)))
    (hr : ¬PurePowerReductionMatrix.Normal (Degrees L (pairFst q)) (FixedWidthPolynomial.vector _ _ r)) :
    admissible L (packet q r.val s.val) ↔ MonicMonomialReduction.residual (FixedWidthPolynomial.vector _ _ r)
      (PurePowerReductionMatrix.selected fallback (Degrees L (pairFst q)) (FixedWidthPolynomial.vector _ _ r))
      (Degrees L (pairFst q) (PurePowerReductionMatrix.selected fallback (Degrees L (pairFst q)) (FixedWidthPolynomial.vector _ _ r))) ≤ FixedWidthPolynomial.vector _ _ s := by
  constructor
  · intro h i
    have hn : i.val < L.arity (context (packet q r.val s.val)) := by simpa only [context_packet] using i.isLt
    simpa only [remainderAt_packet L q r s.val fallback hr i, colAt_packet] using h i.val hn
  · intro h i hi
    have hn : i < L.arity (pairFst q) := by simpa only [context_packet] using hi
    change remainderAt L (packet q r.val s.val) (⟨i, hn⟩ : Fin (L.arity (pairFst q))).val ≤
      colAt L (packet q r.val s.val) (⟨i, hn⟩ : Fin (L.arity (pairFst q))).val
    rw [remainderAt_packet L q r s.val fallback hr, colAt_packet]
    exact h ⟨i, hn⟩

theorem entry_encoded_vector (A W : ℕ) (e : ℕ → ℕ) (i : ℕ) (hi : i < A) (he : e i < 2 ^ W) :
    FixedWidthPolynomial.entry W (Nat.fromBitsLE (FixedWidthNatVector.encode A W e)) i = e i := by
  rw [FixedWidthPolynomial.entry_eq_digit, ← FixedWidthPolynomial.drop_value, ← BinaryNat.value_take]
  exact FixedWidthNatVector.decode_block A W e i hi he

theorem difference_exponent (L : Layout) (q : List Bool) (r s : Indices L q)
    (fallback : Fin (L.arity (pairFst q)))
    (hr : ¬PurePowerReductionMatrix.Normal (Degrees L (pairFst q)) (FixedWidthPolynomial.vector _ _ r)) :
    RationalSubstitution.Indexed.exponentVector (L.arity (pairFst q))
      (FixedWidthPolynomial.entry (L.width (pairFst q)) (Nat.fromBitsLE (differenceWord L (packet q r.val s.val)))) =
      FixedWidthPolynomial.vector _ _ s - MonicMonomialReduction.residual (FixedWidthPolynomial.vector _ _ r)
        (PurePowerReductionMatrix.selected fallback (Degrees L (pairFst q)) (FixedWidthPolynomial.vector _ _ r))
        (Degrees L (pairFst q) (PurePowerReductionMatrix.selected fallback (Degrees L (pairFst q)) (FixedWidthPolynomial.vector _ _ r))) := by
  ext i
  change FixedWidthPolynomial.entry _ _ i.val = _
  rw [differenceWord, context_packet, entry_encoded_vector]
  · rw [differenceAt, colAt_packet, remainderAt_packet L q r s.val fallback hr i, Finsupp.tsub_apply]
  · exact i.isLt
  · exact (Nat.sub_le _ _).trans_lt (by rw [colAt_packet]; exact FixedWidthPolynomial.vector_lt _ _ s i)

theorem sourceQuery_packet (L : Layout) (q : List Bool) (r s : Indices L q) :
    sourceQuery L (packet q r.val s.val) = pair q
      (pair (BinaryNatCode.encode (pivot L (packet q r.val s.val)))
        (BinaryNatCode.encode (Nat.fromBitsLE (differenceWord L (packet q r.val s.val))))) := by
  simp only [sourceQuery, packet, pairFst_pair, BinaryNat.normalize_eq_bits, BinaryNatCode.encode]

theorem negate_packet (q : List Bool) (r s : ℕ) (a : ZMod (Nat.fromBitsLE (pairSnd q) + 1)) :
    negate (pair (packet q r s) (MatrixPower.residueBits a)) = MatrixPower.residueBits (-a) := by
  simp only [negate, packet, pairFst_pair, pairSnd_pair]
  rw [BinaryNat.succ_eq_bits]
  exact MatrixPower.ArithmeticBits.negate_residueBits _ a

theorem entry_packet (L : Layout) (bound : List Bool → ℕ)
    (constant coefficient : List Bool → List Bool) (q : List Bool)
    (low : Fin (L.arity (pairFst q)) → MvPolynomial (Fin (L.arity (pairFst q))) ℤ)
    (c : ℤ) (fallback : Fin (L.arity (pairFst q)))
    (hconstant : constant q = MatrixPower.residueBits (c : ZMod (Nat.fromBitsLE (pairSnd q) + 1)))
    (hcoefficient : ∀ (i : Fin (L.arity (pairFst q))) (k : ℕ),
      coefficient (packet q i.val k) = MatrixPower.residueBits
        ((low i).coeff (RationalSubstitution.Indexed.exponentVector (L.arity (pairFst q))
          (FixedWidthPolynomial.entry (L.width (pairFst q)) k)) : ZMod (Nat.fromBitsLE (pairSnd q) + 1)))
    (r s : Indices L q) :
    entry L bound constant coefficient (packet q r.val s.val) = MatrixPower.residueBits
      ((PurePowerReductionMatrix.matrix fallback (Degrees L (pairFst q)) low c (bound (pairFst q)) s r : ℤ) :
        ZMod (Nat.fromBitsLE (pairSnd q) + 1)) := by
  classical
  by_cases hn : PurePowerReductionMatrix.Normal (Degrees L (pairFst q)) (FixedWidthPolynomial.vector _ _ r)
  · rw [entry, ite_eq_left ((normal_packet L q r s.val).mpr hn), PurePowerReductionMatrix.normal_column _ _ _ _ _ _ hn]
    have HF : pairFst (packet q r.val s.val) = q := by simp only [packet, pairFst_pair]
    rw [HF]
    simp only [sameIndex, row_packet, col_packet, fromBits_encode]
    by_cases he : r = s
    · subst s
      simp only [ite_true, hconstant]
    · have hv : r.val ≠ s.val := fun h => he (Fin.ext h)
      simp only [ite_eq_right hv, ite_eq_right (Ne.symm he), Int.cast_zero, MatrixPower.residueBits,
        ZMod.val_zero, BinaryNatCode.encode]
      rfl
  · have HN : ¬normal L (packet q r.val s.val) := fun h => hn ((normal_packet L q r s.val).mp h)
    rw [entry, ite_eq_right HN, PurePowerReductionMatrix.matrix, ite_eq_right hn]
    by_cases hv : (FixedWidthPolynomial.vector _ _ r).degree ≤ bound (pairFst q)
    · rw [ite_eq_left ((valid_packet L bound q r s.val).mpr hv), ite_eq_left hv,
        MonicMonomialReduction.step_coefficient]
      by_cases ha : MonicMonomialReduction.residual (FixedWidthPolynomial.vector _ _ r)
          (PurePowerReductionMatrix.selected fallback (Degrees L (pairFst q)) (FixedWidthPolynomial.vector _ _ r))
          (Degrees L (pairFst q) (PurePowerReductionMatrix.selected fallback (Degrees L (pairFst q)) (FixedWidthPolynomial.vector _ _ r))) ≤ FixedWidthPolynomial.vector _ _ s
      · rw [ite_eq_left ((admissible_packet L q r s fallback hn).mpr ha), ite_eq_left ha,
          sourceQuery_packet, pivot_packet L q r s.val fallback hn]
        rw [show pair q (pair (BinaryNatCode.encode (PurePowerReductionMatrix.selected fallback
            (Degrees L (pairFst q)) (FixedWidthPolynomial.vector _ _ r)).val)
            (BinaryNatCode.encode (Nat.fromBitsLE (differenceWord L (packet q r.val s.val))))) =
            packet q (PurePowerReductionMatrix.selected fallback (Degrees L (pairFst q)) (FixedWidthPolynomial.vector _ _ r)).val
              (Nat.fromBitsLE (differenceWord L (packet q r.val s.val))) from rfl,
          hcoefficient, difference_exponent L q r s fallback hn, negate_packet, Int.cast_neg]
      · rw [ite_eq_right (fun h => ha ((admissible_packet L q r s fallback hn).mp h)), ite_eq_right ha]
        rfl
    · rw [ite_eq_right (fun h => hv ((valid_packet L bound q r s.val).mp h)), ite_eq_right hv]
      rfl

end LeanCanny.Algebra.PurePowerReductionBits
