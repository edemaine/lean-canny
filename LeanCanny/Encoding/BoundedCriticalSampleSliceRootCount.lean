/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleSliceTarski
public import LeanCanny.Encoding.BoundedAlgebraicSliceRootCount

/-! # Native fiber-root counts over actual critical samples

Unit, first, and second Tarski moments give distinct-root counts and counts
of each prescribed sign. The original actual sample remains fixed. Zero
heads use the polynomial root-list convention and have count zero.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleSlice.RootCount
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedAlgebraicSlice (Family unit unitAccess square squareAccess)
open BoundedAlgebraicSlice.RootCount (difference difference_FP difference_packet halfDifference halfDifference_FP
  halfDifference_packet negateCode negateCode_FP negateCode_packet)
open scoped Classical

noncomputable def roots (P : Readers) (F : Family) (u : List Bool) : Finset ℝ := (specialized P F u).roots.toFinset
noncomputable def count (P : Readers) (F : Family) (u : List Bool) : ℕ := (roots P F u).card
noncomputable def signCount (P : Readers) (F G : Family) (s : SignType) (u : List Bool) : ℕ :=
  RootSignQueries.singleSignCount (specialized P F u) (specialized P G u) s

theorem unit_specialized (P : Readers) (u : List Bool) (hu : u ∈ valid P) : specialized P unit u = 1 := by
  rw [specialized, ite_eq_left hu, BoundedAlgebraicSlice.unit, BoundedAlgebraicSlice.ofTest_slice]
  simp only [BoundedAlgebraicSlice.unitTest, Polynomial.map_one]

theorem square_specialized (P : Readers) (F : Family) (u : List Bool) :
    specialized P (square F) u = specialized P F u ^ 2 := by
  by_cases hu : u ∈ valid P
  · simp only [specialized, ite_eq_left hu, Family.slice, square, Polynomial.map_pow]
  · simp only [specialized, ite_eq_right hu, zero_pow (by decide : 2 ≠ 0)]

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
  apply E.congr
  funext u
  rw [Function.comp_apply, Tarski.value, unit_query]
  simp only [SignStatisticBits.integerCode, pairFst_pair, Int.toNat_natCast]

theorem signCount_evaluator {P : Readers} (h : P.PolyTime) {F G : Family} (A : F.Access) (B : G.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (s : SignType) :
    SpaceFunction (fun u => BinaryNatCode.encode (signCount P F G s u)) := by
  have U := Tarski.evaluator h A unitAccess ha
  have L := Tarski.evaluator h A B ha
  have S := Tarski.evaluator h A (squareAccess B) ha
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

noncomputable def realizable (P : Readers) (F G : Family) (s : SignType) : Language := {u | 0 < signCount P F G s u}
theorem realizable_decider {P : Readers} (h : P.PolyTime) {F G : Family} (A : F.Access) (B : G.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (s : SignType) : SpaceDecider (realizable P F G s) := by
  apply (signCount_evaluator h A B ha s).decider (fun z => decide (z ≠ []))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [])).not.flag_mem_FP
  intro u
  simp only [realizable, Set.mem_ofPred_eq, decide_eq_true_eq, ne_eq, BinaryNatCode.encode, BinaryNat.bits_eq_nil_iff]
  omega
theorem realizable_mem_PSPACE {P : Readers} (h : P.PolyTime) {F G : Family} (A : F.Access) (B : G.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (s : SignType) : realizable P F G s ∈ PSPACE :=
  (realizable_decider h A B ha s).mem_PSPACE

theorem count_sample (P : Readers) (F : Family) (c r : List Bool) (x : BoundedFullCriticalSamples.Samples P c) :
    count P F (pair (pair c (BoundedCriticalSampleHashChoice.descriptor P c x)) r) =
      ((F.slice (pair c r) (BoundedCriticalSampleLabels.parameter P c x).val).roots.toFinset).card := by
  rw [count, roots, specialized_sample]

end LeanCanny.Encoding.BoundedCriticalSampleSlice.RootCount
