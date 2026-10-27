/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleSliceRootCount

/-! # Fiber-root ordinals over actual critical samples

Distinct real roots have short binary ordinals, with native validity. Invalid
sample descriptors and zero specializations have no valid child ordinals.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleFiberRoot
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedAlgebraicSlice (Family)
open BoundedCriticalSampleSlice
open scoped Classical

abbrev Root (P : Readers) (F : Family) (u : List Bool) := {x // x ∈ RootCount.roots P F u}

theorem count_le_degree (P : Readers) (F : Family) (u : List Bool) :
    RootCount.count P F u ≤ F.degree (context u) :=
  ((Multiset.toFinset_card_le (m := (specialized P F u).roots)).trans
    (Polynomial.card_roots' _)).trans (specialized_degree P F u)

noncomputable def root (P : Readers) (F : Family) (u : List Bool) (i : Fin (RootCount.count P F u)) : Root P F u :=
  (RootCount.roots P F u).orderIsoOfFin (k := RootCount.count P F u) rfl i

theorem root_eval_zero (P : Readers) (F : Family) (u : List Bool) (i : Fin (RootCount.count P F u)) :
    (specialized P F u).eval (root P F u i).val = 0 :=
  Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp (root P F u i).property)

theorem root_strictMono (P : Readers) (F : Family) (u : List Bool) :
    StrictMono (fun i => (root P F u i).val) := by
  intro a b hab
  exact ((RootCount.roots P F u).orderIsoOfFin (k := RootCount.count P F u) rfl).strictMono hab

theorem root_surjective (P : Readers) (F : Family) (u : List Bool) : Function.Surjective (root P F u) :=
  ((RootCount.roots P F u).orderIsoOfFin (k := RootCount.count P F u) rfl).surjective

theorem label_length_le (P : Readers) (F : Family) (u : List Bool) (i : Fin (RootCount.count P F u)) :
    (BinaryNatCode.encode i.val).length ≤ (F.degree (context u)).size := by
  rw [BinaryNatCode.length_encode]
  exact Nat.size_le_size (i.isLt.le.trans (count_le_degree P F u))

noncomputable def valid (P : Readers) (F : Family) : Language :=
  {q | Nat.fromBitsLE (pairSnd q) < RootCount.count P F (pairFst q)}

theorem valid_decider {P : Readers} (h : P.PolyTime) {F : Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceDecider (valid P F) := by
  apply ((RootCount.count_evaluator h A ha).precompose pairFst pairFst_mem_FP).withInput.decider
    BoundedAlgebraicSlice.accept BoundedAlgebraicSlice.accept_FP
  intro q
  simp only [valid, Set.mem_ofPred_eq, BoundedAlgebraicSlice.accept, Function.comp_apply,
    pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, decide_eq_true_eq]

theorem valid_mem_PSPACE {P : Readers} (h : P.PolyTime) {F : Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : valid P F ∈ PSPACE :=
  (valid_decider h A ha).mem_PSPACE

theorem invalid_base (P : Readers) (F : Family) (u : List Bool) (hu : u ∉ BoundedCriticalSampleSlice.valid P)
    (i : List Bool) : pair u i ∉ valid P F := by
  simp only [valid, Set.mem_ofPred_eq, pairFst_pair, pairSnd_pair, RootCount.count, RootCount.roots,
    specialized, ite_eq_right hu, Polynomial.roots_zero, Multiset.toFinset_zero, Finset.card_empty,
    Nat.not_lt_zero, not_false_eq_true]

theorem zero_head (P : Readers) (F : Family) (u : List Bool) (hz : specialized P F u = 0)
    (i : List Bool) : pair u i ∉ valid P F := by
  simp only [valid, Set.mem_ofPred_eq, pairFst_pair, pairSnd_pair, RootCount.count, RootCount.roots,
    hz, Polynomial.roots_zero, Multiset.toFinset_zero, Finset.card_empty, Nat.not_lt_zero, not_false_eq_true]

end LeanCanny.Encoding.BoundedCriticalSampleFiberRoot
