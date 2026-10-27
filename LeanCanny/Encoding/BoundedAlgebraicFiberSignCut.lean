/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicSliceJointCount
public import LeanCanny.Encoding.BoundedAlgebraicFiberCut

/-! # Sign-constrained rational-cut queries in algebraic fibers

The query counts roots of one algebraic-slice polynomial below a rational
cut where another slice polynomial has a prescribed sign. The attached cut
retains the original base root. All product moments are computed internally.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicFiberSignCut
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedAlgebraicSlice
open scoped Classical
attribute [local irreducible] BoundedProjectionRootCount.count BoundedProjectionOrderedRoot.root

noncomputable def value (P : Readers) (F G : Family) (s : SignType) (q : List Bool) : List Bool :=
  BinaryNatCode.encode (JointCount.count (P.comp pairFst) (F.comp pairFst) (G.comp pairFst)
    BoundedAlgebraicFiberCut.cutTest s .neg (signQuery q))

theorem evaluator {P : Readers} (h : P.PolyTime) {F G : Family} (A : F.Access) (B : G.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (s : SignType) : SpaceFunction (value P F G s) :=
  (JointCount.evaluator (h.comp pairFst_mem_FP) (A.comp pairFst pairFst_mem_FP) (B.comp pairFst pairFst_mem_FP)
    BoundedAlgebraicFiberCut.cutAccess (fun c => ha (pairFst c)) s .neg).precompose signQuery signQuery_FP

theorem value_packet (P : Readers) (F G : Family) (s : SignType) (c : List Bool)
    (r : Fin (BoundedProjectionRootCount.count P c)) (cut : List Bool) :
    value P F G s (pair (pair c (BinaryNatCode.encode r.val)) cut) = BinaryNatCode.encode
      (((F.slice c (BoundedProjectionOrderedRoot.root P c r).val).roots.toFinset.filter (fun y =>
        SignType.sign ((G.slice c (BoundedProjectionOrderedRoot.root P c r).val).eval y) = s ∧
          y < RationalCutBits.threshold (pair c cut))).card) := by
  simp only [value, JointCount.count_eq_filter, specialized_attach, Family.slice_comp, pairFst_pair,
    BoundedAlgebraicFiberCut.cutTest, ofTest_slice, BoundedProjectionTestSign.rationalCut]
  apply congrArg BinaryNatCode.encode
  apply congrArg Finset.card
  ext y
  simp only [Finset.mem_filter, ← algebraMap_int_eq, RationalCutBits.sign_neg_iff]

noncomputable def language (P : Readers) (F G : Family) (s : SignType) : Language :=
  {q | value P F G s q ≠ []}

theorem decider {P : Readers} (h : P.PolyTime) {F G : Family} (A : F.Access) (B : G.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (s : SignType) :
    SpaceDecider (language P F G s) := by
  apply (evaluator h A B ha s).decider (fun z => decide (z ≠ []))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [])).not.flag_mem_FP
  intro q
  simp only [language, Set.mem_ofPred_eq, decide_eq_true_eq]

theorem language_packet (P : Readers) (F G : Family) (s : SignType) (c : List Bool)
    (r : Fin (BoundedProjectionRootCount.count P c)) (cut : List Bool) :
    pair (pair c (BinaryNatCode.encode r.val)) cut ∈ language P F G s ↔
      ∃ y ∈ (F.slice c (BoundedProjectionOrderedRoot.root P c r).val).roots.toFinset,
        SignType.sign ((G.slice c (BoundedProjectionOrderedRoot.root P c r).val).eval y) = s ∧
          y < RationalCutBits.threshold (pair c cut) := by
  change value P F G s _ ≠ [] ↔ _
  rw [value_packet]
  simp only [ne_eq, BinaryNatCode.encode, BinaryNat.bits_eq_nil_iff]
  have hpos (n : ℕ) : (¬ n = 0) ↔ 0 < n := by omega
  rw [hpos, Finset.card_pos]
  simp only [Finset.Nonempty, Finset.mem_filter]

theorem mem_PSPACE {P : Readers} (h : P.PolyTime) {F G : Family} (A : F.Access) (B : G.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (s : SignType) :
    language P F G s ∈ PSPACE := (decider h A B ha s).mem_PSPACE

end LeanCanny.Encoding.BoundedAlgebraicFiberSignCut
