/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicFiberRootCells

/-! # Validated native sign queries for algebraic endpoint cells

The sign language validates the fiber-root ordinal. For consecutive labels
and a zero or factor test, its right-sided query is exactly the sign on the
whole intervening open cell. Both query evaluation and validity are native.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicFiberCellQueries
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial Set
open BoundedAlgebraicSlice
open scoped Classical

noncomputable def language (P : Readers) (F G : Family) (fromLeft : Bool) (s : SignType) : Language := {q |
  Nat.fromBitsLE (pairSnd q) < RootCount.count P F (pairFst q) ∧
    BoundedAlgebraicFiberLocalSign.value P F G fromLeft q = InfinitesimalSign.encode s}

theorem decider {P : Readers} (h : P.PolyTime) {F G : Family} (A : F.Access) (B : G.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (fromLeft : Bool) (s : SignType) :
    SpaceDecider (language P F G fromLeft s) := by
  have N := (RootCount.count_evaluator h A ha).precompose pairFst pairFst_mem_FP
  have E := BoundedAlgebraicFiberLocalSign.evaluator h A B ha fromLeft
  apply (N.pairOutputs E).withInput.decider (BoundedAlgebraicFiberTestSign.accept s)
    (BoundedAlgebraicFiberTestSign.accept_FP s)
  intro q
  simp only [language, Set.mem_ofPred_eq, BoundedAlgebraicFiberTestSign.accept, Function.comp_apply,
    pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, decide_eq_true_eq]

theorem mem_PSPACE {P : Readers} (h : P.PolyTime) {F G : Family} (A : F.Access) (B : G.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (fromLeft : Bool) (s : SignType) :
    language P F G fromLeft s ∈ PSPACE := (decider h A B ha fromLeft s).mem_PSPACE

theorem invalid (P : Readers) (F G : Family) (q : List Bool) (fromLeft : Bool) (s : SignType)
    (hq : RootCount.count P F (pairFst q) ≤ Nat.fromBitsLE (pairSnd q)) :
    q ∉ language P F G fromLeft s := fun H => (Nat.not_lt_of_ge hq) H.1

theorem interval_packet (P : Readers) (F G : Family) (u : List Bool)
    (r t : Fin (RootCount.count P F u)) (hrt : t.val = r.val + 1)
    (hG : specialized P G u = 0 ∨ specialized P G u ∣ specialized P F u) (s : SignType)
    (y : ℝ) (hy : y ∈ Ioo (BoundedAlgebraicFiberRoot.root P F u r).val (BoundedAlgebraicFiberRoot.root P F u t).val) :
    pair u (BinaryNatCode.encode r.val) ∈ language P F G false s ↔
      SignType.sign ((specialized P G u).eval y) = s := by
  change _ ∧ BoundedAlgebraicFiberLocalSign.value P F G false _ = _ ↔ _
  rw [BoundedAlgebraicFiberRootCells.interval_packet P F G u r t hrt hG y hy]
  have hr : Nat.fromBitsLE (pairSnd (pair u (BinaryNatCode.encode r.val))) <
      RootCount.count P F (pairFst (pair u (BinaryNatCode.encode r.val))) := by
    simpa only [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits] using r.isLt
  rw [and_iff_right hr]
  generalize SignType.sign ((specialized P G u).eval y) = v
  cases v <;> cases s <;> decide

end LeanCanny.Encoding.BoundedAlgebraicFiberCellQueries
