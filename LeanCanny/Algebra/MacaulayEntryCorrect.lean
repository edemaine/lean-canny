/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayEntrySpace
public import LeanCanny.Algebra.MacaulayMatrix

/-! # Correctness of streamed Macaulay coefficient selection -/

@[expose] public section

namespace LeanCanny.Algebra.MacaulayBits
open Complexity
open LeanCanny.Encoding
open scoped BigOperators

abbrev Degrees (L : Layout) (c : List Bool) : Fin (L.arity c) → ℕ := fun i => L.degree c i

abbrev Indices (L : Layout) (q : List Bool) := Macaulay.Index (L.arity (pairFst q)) (L.width (pairFst q))

def packet (q : List Bool) (r s : ℕ) : List Bool :=
  pair q (pair (BinaryNatCode.encode r) (BinaryNatCode.encode s))

@[simp] theorem context_packet (q : List Bool) (r s : ℕ) : context (packet q r s) = pairFst q := by
  simp only [packet, context, pairFst_pair]

@[simp] theorem row_packet (q : List Bool) (r s : ℕ) : row (packet q r s) = BinaryNatCode.encode r := by
  simp only [packet, row, pairFst_pair, pairSnd_pair]

@[simp] theorem col_packet (q : List Bool) (r s : ℕ) : col (packet q r s) = BinaryNatCode.encode s := by
  simp only [packet, col, pairSnd_pair]

theorem level_eq (L : Layout) (c : List Bool) : L.level c = Macaulay.level (Degrees L c) := by
  simp only [Layout.level, Macaulay.level, Finset.sum_range, Degrees]

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

theorem sum_min_eq_iff {ι : Type*} (s : Finset ι) (f : ι → ℕ) (T : ℕ) :
    (∑ i ∈ s, min (f i) (T + 1)) = T ↔ (∑ i ∈ s, f i) = T := by
  have haux : ∀ g : ι → ℕ, (∑ i ∈ s, g i) = T → ∀ i ∈ s, g i ≤ T := by
    intro g hg i hi
    exact (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hi).trans_eq hg
  constructor
  · intro h
    have hb := haux _ h
    have he : ∀ i ∈ s, min (f i) (T + 1) = f i := by
      intro i hi
      have hh := hb i hi
      omega
    simpa only [Finset.sum_congr rfl he] using h
  · intro h
    have hb := haux _ h
    calc
      _ = ∑ i ∈ s, f i := Finset.sum_congr rfl (fun i hi => min_eq_left (by have := hb i hi; omega))
      _ = T := h

theorem active_packet (L : Layout) (q : List Bool) (r : Indices L q) (s : ℕ) :
    active L (packet q r.val s) ↔ (FixedWidthPolynomial.vector _ _ r).degree = Macaulay.level (Degrees L (pairFst q)) := by
  rw [active, rowTotal, context_packet, sum_min_eq_iff]
  simp only [Finset.sum_range, rowAt_packet, level_eq, Finsupp.degree_eq_sum]

theorem pivot_packet (L : Layout) (q : List Bool) (r : Indices L q) (s : ℕ)
    (hr : (FixedWidthPolynomial.vector _ _ r).degree = Macaulay.level (Degrees L (pairFst q))) :
    pivot L (packet q r.val s) = (Macaulay.pivot _ _ hr).val := by
  rw [pivot, context_packet, List.findIdx_eq (by simp)]
  simp only [List.getElem_range, decide_eq_true_eq, decide_eq_false_iff_not]
  constructor
  · rw [rowAt_packet]
    exact Macaulay.pivot_le _ _ hr
  · intro j hj
    have hjn : j < L.arity (pairFst q) := hj.trans (Macaulay.pivot _ _ hr).isLt
    rw [show j = (⟨j, hjn⟩ : Fin (L.arity (pairFst q))).val from rfl, rowAt_packet]
    intro hd
    have hm : (⟨j, hjn⟩ : Fin (L.arity (pairFst q))) ∈ Macaulay.eligible (Degrees L (pairFst q)) (FixedWidthPolynomial.vector _ _ r) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd⟩
    have hmin := Finset.min'_le _ _ hm
    have hle : (Macaulay.pivot (Degrees L (pairFst q)) _ hr).val ≤ j := hmin
    omega

theorem remainderAt_packet (L : Layout) (q : List Bool) (r : Indices L q) (s : ℕ)
    (hr : (FixedWidthPolynomial.vector _ _ r).degree = Macaulay.level (Degrees L (pairFst q)))
    (i : Fin (L.arity (pairFst q))) :
    remainderAt L (packet q r.val s) i.val = Macaulay.remainder _ _ hr i := by
  rw [remainderAt, rowAt_packet, pivot_packet L q r s hr, context_packet]
  simp only [Macaulay.remainder, Finsupp.tsub_apply, Finsupp.single_apply]
  by_cases hi : i = Macaulay.pivot _ _ hr
  · subst i
    simp
  · have hv : i.val ≠ (Macaulay.pivot _ _ hr).val := fun hv => hi (Fin.ext hv)
    simp [hv, Ne.symm hi]

theorem admissible_packet (L : Layout) (q : List Bool) (r s : Indices L q)
    (hr : (FixedWidthPolynomial.vector _ _ r).degree = Macaulay.level (Degrees L (pairFst q))) :
    admissible L (packet q r.val s.val) ↔ Macaulay.remainder _ _ hr ≤ FixedWidthPolynomial.vector _ _ s := by
  constructor
  · intro h i
    have hn : i.val < L.arity (context (packet q r.val s.val)) := by simpa only [context_packet] using i.isLt
    have hh := h i.val hn
    rw [remainderAt_packet L q r s.val hr i, colAt_packet L q r.val s i] at hh
    exact hh
  · intro h i hi
    have hn : i < L.arity (pairFst q) := by simpa only [context_packet] using hi
    change remainderAt L (packet q r.val s.val) (⟨i, hn⟩ : Fin (L.arity (pairFst q))).val ≤
      colAt L (packet q r.val s.val) (⟨i, hn⟩ : Fin (L.arity (pairFst q))).val
    rw [remainderAt_packet L q r s.val hr, colAt_packet]
    exact h ⟨i, hn⟩

theorem entry_encoded_vector (A W : ℕ) (e : ℕ → ℕ) (i : ℕ) (hi : i < A) (he : e i < 2 ^ W) :
    FixedWidthPolynomial.entry W (Nat.fromBitsLE (FixedWidthNatVector.encode A W e)) i = e i := by
  rw [FixedWidthPolynomial.entry_eq_digit, ← FixedWidthPolynomial.drop_value, ← BinaryNat.value_take]
  exact FixedWidthNatVector.decode_block A W e i hi he

theorem difference_exponent (L : Layout) (q : List Bool) (r s : Indices L q)
    (hr : (FixedWidthPolynomial.vector _ _ r).degree = Macaulay.level (Degrees L (pairFst q))) :
    RationalSubstitution.Indexed.exponentVector (L.arity (pairFst q))
      (FixedWidthPolynomial.entry (L.width (pairFst q))
        (Nat.fromBitsLE (differenceWord L (packet q r.val s.val)))) =
      FixedWidthPolynomial.vector _ _ s - Macaulay.remainder _ _ hr := by
  ext i
  change FixedWidthPolynomial.entry _ _ i.val = _
  rw [differenceWord, context_packet, entry_encoded_vector]
  · rw [differenceAt, colAt_packet, remainderAt_packet L q r s.val hr i, Finsupp.tsub_apply]
  · exact i.isLt
  · exact (Nat.sub_le _ _).trans_lt (by
      rw [colAt_packet]
      exact FixedWidthPolynomial.vector_lt _ _ s i)

theorem sourceQuery_packet (L : Layout) (q : List Bool) (r s : Indices L q) :
    sourceQuery L (packet q r.val s.val) = pair q
      (pair (BinaryNatCode.encode (pivot L (packet q r.val s.val)))
        (BinaryNatCode.encode (Nat.fromBitsLE (differenceWord L (packet q r.val s.val))))) := by
  simp only [sourceQuery, packet, pairFst_pair, BinaryNat.normalize_eq_bits, BinaryNatCode.encode]

theorem identityEntry_packet (q : List Bool) (r s : ℕ) :
    identityEntry (packet q r s) = MatrixPower.residueBits
      ((if r = s then 1 else 0) : ZMod (Nat.fromBitsLE (pairSnd q) + 1)) := by
  simp only [identityEntry, sameIndex, row_packet, col_packet, fromBits_encode]
  simp only [packet, pairFst_pair]
  by_cases he : r = s
  · rw [ite_eq_left he, ite_eq_left he, BinaryNat.succ_eq_bits]
    exact MatrixPower.ArithmeticBits.one_residueBits _
  · simp only [ite_eq_right he]
    rfl

theorem entry_packet (L : Layout) (coefficient : List Bool → List Bool) (q : List Bool)
    (p : Fin (L.arity (pairFst q)) → MvPolynomial (Fin (L.arity (pairFst q))) ℤ)
    (hc : ∀ (i : Fin (L.arity (pairFst q))) (k : ℕ),
      coefficient (packet q i.val k) = MatrixPower.residueBits
        ((p i).coeff (RationalSubstitution.Indexed.exponentVector (L.arity (pairFst q))
          (FixedWidthPolynomial.entry (L.width (pairFst q)) k)) : ZMod (Nat.fromBitsLE (pairSnd q) + 1)))
    (r s : Indices L q) : entry L coefficient (packet q r.val s.val) =
      MatrixPower.residueBits ((Macaulay.matrix p (Degrees L (pairFst q)) (L.width (pairFst q)) r s : ℤ) :
        ZMod (Nat.fromBitsLE (pairSnd q) + 1)) := by
  by_cases hr : (FixedWidthPolynomial.vector _ _ r).degree = Macaulay.level (Degrees L (pairFst q))
  · have ha := (active_packet L q r s.val).mpr hr
    rw [entry, ite_eq_left ha, Macaulay.entry_active p _ _ r s hr]
    by_cases hg : Macaulay.remainder _ _ hr ≤ FixedWidthPolynomial.vector _ _ s
    · rw [ite_eq_left ((admissible_packet L q r s hr).mpr hg), ite_eq_left hg, sourceQuery_packet,
        pivot_packet L q r s.val hr]
      rw [show pair q (pair (BinaryNatCode.encode (Macaulay.pivot _ _ hr).val)
        (BinaryNatCode.encode (Nat.fromBitsLE (differenceWord L (packet q r.val s.val))))) =
        packet q (Macaulay.pivot _ _ hr).val (Nat.fromBitsLE (differenceWord L (packet q r.val s.val))) from rfl,
        hc, difference_exponent L q r s hr]
    · rw [ite_eq_right (fun h => hg ((admissible_packet L q r s hr).mp h)), ite_eq_right hg]
      rfl
  · have ha : ¬active L (packet q r.val s.val) := fun h => hr ((active_packet L q r s.val).mp h)
    rw [entry, ite_eq_right ha, identityEntry_packet, Macaulay.matrix, dite_eq_right hr]
    simp only [Matrix.one_apply, Fin.ext_iff, Int.cast_ite, Int.cast_one, Int.cast_zero]

end LeanCanny.Algebra.MacaulayBits
