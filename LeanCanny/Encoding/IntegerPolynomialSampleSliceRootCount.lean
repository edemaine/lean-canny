/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.IntegerPolynomialSampleSliceTarski
public import LeanCanny.Encoding.BoundedAlgebraicSliceRootCount

/-! # Native fiber-root counts over complete algebraic samples

Unit, first, and second Tarski moments give distinct-root counts and counts
of each prescribed sign. The original complete scalar-root label remains fixed, including repeated roots. Zero
heads use the polynomial root-list convention and have count zero.
-/

@[expose] public section
namespace LeanCanny.Encoding.IntegerPolynomialSampleSlice.RootCount
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open IntegerPolynomialRootQueriesBits (Source)
open BoundedAlgebraicSlice (Family unit unitAccess square squareAccess)
open BoundedAlgebraicSlice.RootCount (difference difference_FP difference_packet halfDifference halfDifference_FP
  halfDifference_packet negateCode negateCode_FP negateCode_packet)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

noncomputable def roots (P : Source) (F : Family) (u : List Bool) : Finset ℝ := (specialized P F u).roots.toFinset
noncomputable def count (P : Source) (F : Family) (u : List Bool) : ℕ := (roots P F u).card
noncomputable def signCount (P : Source) (F G : Family) (s : SignType) (u : List Bool) : ℕ :=
  RootSignQueries.singleSignCount (specialized P F u) (specialized P G u) s

theorem unit_specialized (P : Source) (u : List Bool) (hu : u ∈ valid P) : specialized P unit u = 1 := by
  rw [specialized, ite_eq_left hu, BoundedAlgebraicSlice.unit, BoundedAlgebraicSlice.ofTest_slice]
  simp only [BoundedAlgebraicSlice.unitTest, Polynomial.map_one]

theorem square_specialized (P : Source) (F : Family) (u : List Bool) :
    specialized P (square F) u = specialized P F u ^ 2 := by
  by_cases hu : u ∈ valid P
  · simp only [specialized, ite_eq_left hu, Family.slice, square, Polynomial.map_pow]
  · simp only [specialized, ite_eq_right hu, zero_pow (by decide : 2 ≠ 0)]

theorem unit_query (P : Source) (F : Family) (u : List Bool) :
    RootSignQueries.tarskiQuery (specialized P F u) (specialized P unit u) = (count P F u : ℤ) := by
  by_cases hu : u ∈ valid P
  · rw [unit_specialized P u hu, RootSignQueries.tarskiQuery_one]
    rfl
  · have hz : specialized P F u = 0 := by rw [specialized, ite_eq_right hu]
    simp [hz, count, roots, RootSignQueries.tarskiQuery, RootSignQueries.signSum]

theorem count_evaluator {P : Source} (h : IntegerPolynomialRootQueriesBits.Access P) {F : Family} (A : F.Access) :
    SpaceFunction (fun u => BinaryNatCode.encode (count P F u)) := by
  have E := (Tarski.evaluator h A unitAccess).postcompose pairFst pairFst_mem_FP
  apply E.congr
  funext u
  rw [Function.comp_apply, Tarski.value, unit_query]
  simp only [SignStatisticBits.integerCode, pairFst_pair, Int.toNat_natCast]

theorem signCount_evaluator {P : Source} (h : IntegerPolynomialRootQueriesBits.Access P) {F G : Family} (A : F.Access) (B : G.Access) (s : SignType) :
    SpaceFunction (fun u => BinaryNatCode.encode (signCount P F G s u)) := by
  have U := Tarski.evaluator h A unitAccess
  have L := Tarski.evaluator h A B
  have S := Tarski.evaluator h A (squareAccess B)
  cases s with
  | zero =>
    have E := (U.pairOutputs S).postcompose difference difference_FP
    apply E.congr
    funext u
    simp only [Function.comp_apply, Tarski.value, square_specialized]
    apply difference_packet
    rw [unit_query]
    simpa only [RootSignQueries.tarskiQuery_one, count, roots, signCount, SignType.zero_eq_zero] using
      (RootSignQueries.singleSignCount_zero (specialized P F u) (specialized P G u)).symm
  | neg =>
    have E := (S.pairOutputs L).postcompose halfDifference halfDifference_FP
    apply E.congr
    funext u
    simp only [Function.comp_apply, Tarski.value, square_specialized]
    apply halfDifference_packet
    exact (RootSignQueries.singleSignCount_negative (specialized P F u) (specialized P G u)).symm
  | pos =>
    have E := (S.pairOutputs (L.postcompose negateCode negateCode_FP)).postcompose halfDifference halfDifference_FP
    apply E.congr
    funext u
    simp only [Function.comp_apply, Tarski.value, square_specialized, negateCode_packet]
    apply halfDifference_packet
    rw [sub_neg_eq_add]
    exact (RootSignQueries.singleSignCount_positive (specialized P F u) (specialized P G u)).symm

noncomputable def realizable (P : Source) (F G : Family) (s : SignType) : Language := {u | 0 < signCount P F G s u}
theorem realizable_decider {P : Source} (h : IntegerPolynomialRootQueriesBits.Access P) {F G : Family} (A : F.Access) (B : G.Access) (s : SignType) : SpaceDecider (realizable P F G s) := by
  apply (signCount_evaluator h A B s).decider (fun z => decide (z ≠ []))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [])).not.flag_mem_FP
  intro u
  simp only [realizable, Set.mem_ofPred_eq, decide_eq_true_eq, ne_eq, BinaryNatCode.encode, BinaryNat.bits_eq_nil_iff]
  omega
theorem realizable_mem_PSPACE {P : Source} (h : IntegerPolynomialRootQueriesBits.Access P) {F G : Family} (A : F.Access) (B : G.Access) (s : SignType) : realizable P F G s ∈ PSPACE :=
  (realizable_decider h A B s).mem_PSPACE

end LeanCanny.Encoding.IntegerPolynomialSampleSlice.RootCount
