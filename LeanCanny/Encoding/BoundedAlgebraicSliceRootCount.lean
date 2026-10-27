/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicSliceUnit
public import LeanCanny.Algebra.SingleRootSignCount
public import LeanCanny.Algebra.SignedIntegerArithmeticFP

/-! # Native distinct-root and single-sign counts in algebraic fibers

The unit, first, and second sign moments come from the native algebraic-slice
Tarski evaluator. Signed binary subtraction and exact halving recover each
count. Repeated roots are counted once; zero heads have an empty root list.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicSlice.RootCount
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open scoped Classical

noncomputable def roots (P : Readers) (F : Family) (u : List Bool) : Finset ℝ := (specialized P F u).roots.toFinset
noncomputable def count (P : Readers) (F : Family) (u : List Bool) : ℕ := (roots P F u).card
noncomputable def signCount (P : Readers) (F G : Family) (s : SignType) (u : List Bool) : ℕ :=
  RootSignQueries.singleSignCount (specialized P F u) (specialized P G u) s

theorem unit_query (P : Readers) (F : Family) (u : List Bool) :
    RootSignQueries.tarskiQuery (specialized P F u) (specialized P unit u) = (count P F u : ℤ) := by
  by_cases hu : u ∈ valid P
  · rw [unit_specialized P u hu, RootSignQueries.tarskiQuery_one]
    rfl
  · have hz : specialized P F u = 0 := by rw [specialized, ite_eq_right hu]
    simp [hz, count, roots, RootSignQueries.tarskiQuery, RootSignQueries.signSum]

theorem count_evaluator {P : Readers} (h : P.PolyTime) {F : Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun u => BinaryNatCode.encode (count P F u)) := by
  have E := (Tarski.evaluator h A unitAccess ha).postcompose pairFst pairFst_mem_FP
  refine E.congr (funext fun u => ?_)
  rw [Function.comp_apply, Tarski.value, unit_query]
  simp only [SignStatisticBits.integerCode, pairFst_pair, Int.toNat_natCast]

def negateCode (z : List Bool) : List Bool := pair (pairSnd z) (pairFst z)
theorem negateCode_FP : negateCode ∈ FP := mem_FP_pair pairSnd_mem_FP pairFst_mem_FP
theorem negateCode_packet (z : ℤ) : negateCode (SignStatisticBits.integerCode z) = SignStatisticBits.integerCode (-z) := by
  simp only [negateCode, SignStatisticBits.integerCode, pairFst_pair, pairSnd_pair, neg_neg]

def difference (z : List Bool) : List Bool := pairFst (SignedIntegerArithmetic.subtract z)
def halfDifference (z : List Bool) : List Bool := BinaryNat.half (difference z)
theorem difference_FP : difference ∈ FP := by
  have H := mem_FP_comp SignedIntegerArithmetic.subtract_FP pairFst_mem_FP
  exact mem_FP_of_eq H (fun z => by simp only [difference, Function.comp_apply])
theorem halfDifference_FP : halfDifference ∈ FP := by
  have H := mem_FP_comp difference_FP BinaryNat.half_mem_FP
  exact mem_FP_of_eq H (fun z => by simp only [halfDifference, Function.comp_apply])

theorem difference_packet (a b : ℤ) (n : ℕ) (hn : a - b = (n : ℤ)) :
    difference (pair (SignStatisticBits.integerCode a) (SignStatisticBits.integerCode b)) = BinaryNatCode.encode n := by
  rw [difference, SignedIntegerArithmetic.subtract_packet, hn]
  simp only [SignStatisticBits.integerCode, pairFst_pair, Int.toNat_natCast]

theorem halfDifference_packet (a b : ℤ) (n : ℕ) (hn : a - b = 2 * (n : ℤ)) :
    halfDifference (pair (SignStatisticBits.integerCode a) (SignStatisticBits.integerCode b)) = BinaryNatCode.encode n := by
  have hd : a - b = ((2 * n : ℕ) : ℤ) := by simpa only [Nat.cast_mul, Nat.cast_ofNat] using hn
  rw [halfDifference, difference_packet a b (2 * n) hd, BinaryNat.half_eq_bits]
  simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
  congr 1
  omega

theorem signCount_evaluator {P : Readers} (h : P.PolyTime) {F G : Family} (A : F.Access) (B : G.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (s : SignType) :
    SpaceFunction (fun u => BinaryNatCode.encode (signCount P F G s u)) := by
  have U := Tarski.evaluator h A unitAccess ha
  have L := Tarski.evaluator h A B ha
  have S := Tarski.evaluator h A (squareAccess B) ha
  cases s with
  | zero =>
    have E := (U.pairOutputs S).postcompose difference difference_FP
    refine E.congr (funext fun u => ?_)
    simp only [Function.comp_apply, Tarski.value, square_specialized]
    apply difference_packet
    rw [unit_query]
    simpa only [RootSignQueries.tarskiQuery_one, count, roots, signCount, SignType.zero_eq_zero] using
      (RootSignQueries.singleSignCount_zero (specialized P F u) (specialized P G u)).symm
  | neg =>
    have E := (S.pairOutputs L).postcompose halfDifference halfDifference_FP
    refine E.congr (funext fun u => ?_)
    simp only [Function.comp_apply, Tarski.value, square_specialized]
    apply halfDifference_packet
    exact (RootSignQueries.singleSignCount_negative (specialized P F u) (specialized P G u)).symm
  | pos =>
    have E := (S.pairOutputs (L.postcompose negateCode negateCode_FP)).postcompose halfDifference halfDifference_FP
    refine E.congr (funext fun u => ?_)
    simp only [Function.comp_apply, Tarski.value, square_specialized, negateCode_packet]
    apply halfDifference_packet
    rw [sub_neg_eq_add]
    exact (RootSignQueries.singleSignCount_positive (specialized P F u) (specialized P G u)).symm

noncomputable def realizable (P : Readers) (F G : Family) (s : SignType) : Language := {u | 0 < signCount P F G s u}

theorem realizable_decider {P : Readers} (h : P.PolyTime) {F G : Family} (A : F.Access) (B : G.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (s : SignType) : SpaceDecider (realizable P F G s) := by
  apply (signCount_evaluator h A B ha s).decider (fun z => decide (z ≠ []))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [])).not.flag_mem_FP
  intro u
  simp only [realizable, Set.mem_ofPred_eq, decide_eq_true_eq, ne_eq, BinaryNatCode.encode, BinaryNat.bits_eq_nil_iff]
  omega

end LeanCanny.Encoding.BoundedAlgebraicSlice.RootCount
