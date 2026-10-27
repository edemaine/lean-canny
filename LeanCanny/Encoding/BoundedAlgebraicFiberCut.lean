/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicSliceRootCount
public import LeanCanny.Encoding.BoundedAlgebraicSliceReindex

/-! # Native rational-cut counts in algebraic fibers

The input pairs a base algebraic-root query with a signed rational-cut record.
The negative sign of the rational linear polynomial counts roots strictly
below that cut. Attaching the cut preserves the original real-order root.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicFiberCut
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter Polynomial
open BoundedAlgebraicSlice
open scoped Classical
attribute [local irreducible] BoundedProjectionRootCount.count BoundedProjectionOrderedRoot.root

noncomputable def cutTest : Family := ofTest BoundedProjectionTestSign.rationalCut
noncomputable def cutAccess : cutTest.Access := ofTestAccess BoundedProjectionTestSign.rationalCutAccess

noncomputable def value (P : Readers) (F : Family) (q : List Bool) : List Bool :=
  BinaryNatCode.encode (RootCount.signCount (P.comp pairFst) (F.comp pairFst) cutTest .neg (signQuery q))

theorem evaluator {P : Readers} (h : P.PolyTime) {F : Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (value P F) :=
  (RootCount.signCount_evaluator (h.comp pairFst_mem_FP) (A.comp pairFst pairFst_mem_FP) cutAccess
    (fun c => ha (pairFst c)) .neg).precompose signQuery signQuery_FP

theorem value_packet (P : Readers) (F : Family) (c : List Bool) (r : Fin (BoundedProjectionRootCount.count P c))
    (cut : List Bool) :
    value P F (pair (pair c (BinaryNatCode.encode r.val)) cut) = BinaryNatCode.encode
      (((F.slice c (BoundedProjectionOrderedRoot.root P c r).val).roots.toFinset.filter
        (fun y => y < RationalCutBits.threshold (pair c cut))).card) := by
  let v := pair c cut
  let s : Fin (BoundedProjectionRootCount.count (P.comp pairFst) v) :=
    ⟨r.val, by simpa only [BoundedProjectionRootCount.count_comp, v, pairFst_pair] using r.isLt⟩
  have hq : signQuery (pair (pair c (BinaryNatCode.encode r.val)) cut) = pair v (BinaryNatCode.encode s.val) := by
    simp only [signQuery, v, s, pairFst_pair, pairSnd_pair, BinaryNat.normalize_eq_bits,
      BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have he := BoundedProjectionOrderedRoot.root_value_reindex P pairFst v c (pairFst_pair _ _) s r rfl
  have hc : RootCount.signCount (P.comp pairFst) (F.comp pairFst) cutTest .neg (pair v (BinaryNatCode.encode s.val)) =
      (((F.slice c (BoundedProjectionOrderedRoot.root P c r).val).roots.toFinset.filter
        (fun y => y < RationalCutBits.threshold (pair c cut))).card) := by
    rw [RootCount.signCount, RootSignQueries.singleSignCount, specialized_packet, specialized_packet]
    simp only [Family.slice_comp, cutTest, ofTest_slice, BoundedProjectionTestSign.rationalCut]
    rw [he]
    simp only [v, pairFst_pair]
    apply congrArg Finset.card
    ext y
    simp only [Finset.mem_filter, ← algebraMap_int_eq, RationalCutBits.sign_neg_iff]
  rw [value, hq, hc]

end LeanCanny.Encoding.BoundedAlgebraicFiberCut
