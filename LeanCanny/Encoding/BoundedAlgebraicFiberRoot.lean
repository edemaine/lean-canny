/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicFiberCut

/-! # Ordered labels for roots in algebraic fibers

A label is a binary ordinal among the distinct real roots of the specialized
polynomial. Its validity and its comparison with a rational cut have native
polynomial-space deciders. The ordinal is bounded by the original outer degree.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicFiberRoot
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedAlgebraicSlice
open scoped Classical
attribute [local irreducible] BoundedProjectionRootCount.count BoundedProjectionOrderedRoot.root

theorem count_le_degree (P : Readers) (F : Family) (u : List Bool) :
    RootCount.count P F u ≤ F.degree (pairFst u) := by
  exact ((Multiset.toFinset_card_le (m := (specialized P F u).roots)).trans
    (Polynomial.card_roots' _)).trans (specialized_degree P F u)

noncomputable def root (P : Readers) (F : Family) (u : List Bool) (i : Fin (RootCount.count P F u)) :
    {y // y ∈ RootCount.roots P F u} :=
  (RootCount.roots P F u).orderIsoOfFin (k := RootCount.count P F u) rfl i

theorem label_length_le (P : Readers) (F : Family) (u : List Bool) (i : Fin (RootCount.count P F u)) :
    (BinaryNatCode.encode i.val).length ≤ (F.degree (pairFst u)).size := by
  rw [BinaryNatCode.length_encode]
  exact Nat.size_le_size (i.isLt.le.trans (count_le_degree P F u))

theorem root_eval_zero (P : Readers) (F : Family) (u : List Bool) (i : Fin (RootCount.count P F u)) :
    (specialized P F u).eval (root P F u i).val = 0 :=
  Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp (root P F u i).property)

theorem root_strictMono (P : Readers) (F : Family) (u : List Bool) :
    StrictMono (fun i => (root P F u i).val) := by
  intro a b hab
  exact ((RootCount.roots P F u).orderIsoOfFin (k := RootCount.count P F u) rfl).strictMono hab

theorem root_surjective (P : Readers) (F : Family) (u : List Bool) : Function.Surjective (root P F u) :=
  ((RootCount.roots P F u).orderIsoOfFin (k := RootCount.count P F u) rfl).surjective

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

theorem invalid_base (P : Readers) (F : Family) (u : List Bool) (hu : u ∉ BoundedAlgebraicSlice.valid P)
    (i : List Bool) : pair u i ∉ valid P F := by
  simp only [valid, Set.mem_ofPred_eq, pairFst_pair, pairSnd_pair, RootCount.count, RootCount.roots,
    specialized, ite_eq_right hu, Polynomial.roots_zero, Multiset.toFinset_zero, Finset.card_empty,
    Nat.not_lt_zero, not_false_eq_true]

private theorem ordered_rank_eq_card {α : Type*} [LinearOrder α] (s : Finset α) {k : ℕ}
    (hk : s.card = k) (x : {a // a ∈ s}) :
    ((s.orderIsoOfFin hk).symm x).val = (s.filter (fun a => a < x.val)).card := by
  let e := (s.orderIsoOfFin hk).symm
  rw [← Finset.card_range (e x).val]
  symm
  apply Finset.card_bij (fun y hy => (e ⟨y, (Finset.mem_filter.mp hy).1⟩).val)
  · intro y hy
    rw [Finset.mem_range]
    exact e.lt_iff_lt.mpr (Finset.mem_filter.mp hy).2
  · intro a ha b hb hab
    exact congrArg Subtype.val (e.injective (Fin.ext hab))
  · intro n hn
    have hn' : n < (e x).val := Finset.mem_range.mp hn
    let j : Fin k := ⟨n, hn'.trans (e x).isLt⟩
    refine ⟨(e.symm j).val, Finset.mem_filter.mpr ⟨(e.symm j).property, ?_⟩, ?_⟩
    · change e.symm j < x
      have h := e.symm.strictMono (show j < e x from hn')
      rw [e.symm_apply_apply] at h
      exact h
    · simp only [e.apply_symm_apply]
      rfl

theorem root_rank (P : Readers) (F : Family) (u : List Bool) (i : Fin (RootCount.count P F u)) :
    i.val = ((RootCount.roots P F u).filter (fun y => y < (root P F u i).val)).card := by
  have hr := ordered_rank_eq_card (RootCount.roots P F u) (k := RootCount.count P F u) rfl (root P F u i)
  unfold root at hr
  rw [OrderIso.symm_apply_apply] at hr
  exact hr

theorem root_lt_iff (P : Readers) (F : Family) (u : List Bool) (i : Fin (RootCount.count P F u)) (a : ℝ) :
    (root P F u i).val < a ↔ i.val < ((RootCount.roots P F u).filter (fun y => y < a)).card := by
  have hr := root_rank P F u i
  constructor
  · intro ha
    rw [hr]
    apply Finset.card_lt_card
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨?_, ?_⟩
    · intro y hy
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hy).1, (Finset.mem_filter.mp hy).2.trans ha⟩
    · intro he
      have hx : (root P F u i).val ∈ (RootCount.roots P F u).filter (fun y => y < a) :=
        Finset.mem_filter.mpr ⟨(root P F u i).property, ha⟩
      rw [← he] at hx
      exact (lt_irrefl _) (Finset.mem_filter.mp hx).2
  · intro hi
    by_contra hn
    have hs : (RootCount.roots P F u).filter (fun y => y < a) ⊆
        (RootCount.roots P F u).filter (fun y => y < (root P F u i).val) := by
      intro y hy
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hy).1,
        (Finset.mem_filter.mp hy).2.trans_le (le_of_not_gt hn)⟩
    have hc := Finset.card_le_card hs
    omega

def cutQuery (q : List Bool) : List Bool := pair (pairFst (pairFst q)) (pairSnd q)
theorem cutQuery_FP : cutQuery ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP

/-- Input: a fiber-root label paired with a rational-cut record. -/
noncomputable def below (P : Readers) (F : Family) : Language := {q |
  pairFst q ∈ valid P F ∧ Nat.fromBitsLE (pairSnd (pairFst q)) <
    Nat.fromBitsLE (BoundedAlgebraicFiberCut.value P F (cutQuery q))}

def acceptBelow (z : List Bool) : Bool := decide
  (Nat.fromBitsLE (pairSnd (pairFst (pairFst z))) < Nat.fromBitsLE (pairFst (pairSnd z)) ∧
    Nat.fromBitsLE (pairSnd (pairFst (pairFst z))) < Nat.fromBitsLE (pairSnd (pairSnd z)))

theorem acceptBelow_FP : (fun z => [acceptBelow z]) ∈ FP := by
  have hi := BinaryFn.fromBits (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP)
  have hn := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
  have hc := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
  exact ((hi.lt hn).and (hi.lt hc)).flag_mem_FP

theorem below_decider {P : Readers} (h : P.PolyTime) {F : Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceDecider (below P F) := by
  have N := (RootCount.count_evaluator h A ha).precompose (fun q => pairFst (pairFst q))
    (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  have C := (BoundedAlgebraicFiberCut.evaluator h A ha).precompose cutQuery cutQuery_FP
  apply (N.pairOutputs C).withInput.decider acceptBelow acceptBelow_FP
  intro q
  simp only [below, valid, Set.mem_ofPred_eq, acceptBelow, Function.comp_apply,
    pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, decide_eq_true_eq]

theorem below_packet (P : Readers) (F : Family) (c : List Bool) (r : Fin (BoundedProjectionRootCount.count P c))
    (i : Fin (RootCount.count P F (pair c (BinaryNatCode.encode r.val)))) (cut : List Bool) :
    pair (pair (pair c (BinaryNatCode.encode r.val)) (BinaryNatCode.encode i.val)) cut ∈ below P F ↔
      (root P F (pair c (BinaryNatCode.encode r.val)) i).val < RationalCutBits.threshold (pair c cut) := by
  have hr := root_lt_iff P F (pair c (BinaryNatCode.encode r.val)) i (RationalCutBits.threshold (pair c cut))
  simp only [RootCount.roots, specialized_packet] at hr
  simp only [below, valid, Set.mem_ofPred_eq, cutQuery, pairFst_pair, pairSnd_pair]
  rw [BoundedAlgebraicFiberCut.value_packet]
  have hd (n : ℕ) : Nat.fromBitsLE (BinaryNatCode.encode n) = n := Nat.fromBitsLE_bits n
  simpa only [hd, i.isLt, true_and] using hr.symm

theorem below_mem_PSPACE {P : Readers} (h : P.PolyTime) {F : Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : below P F ∈ PSPACE :=
  (below_decider h A ha).mem_PSPACE

end LeanCanny.Encoding.BoundedAlgebraicFiberRoot
