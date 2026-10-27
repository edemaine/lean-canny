/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicFiberSignatureRead
public import LeanCanny.Algebra.ThomOrderSpace

/-! # Native real-order comparisons of short fiber-root labels

Input is `pair sourceContext (pair leftHashOrdinal rightHashOrdinal)`.
The roots are enumerated by their hashes, while this query compares their
actual real coordinates. Every derivative sign is recomputed natively.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicFiberRootOrder
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open scoped Classical

def leftQuery (q : List Bool) : List Bool :=
  pair (pair (pairFst (pairFst q)) (pairFst (pairSnd (pairFst q)))) (pairSnd q)
def rightQuery (q : List Bool) : List Bool :=
  pair (pair (pairFst (pairFst q)) (pairSnd (pairSnd (pairFst q)))) (pairSnd q)
theorem leftQuery_FP : leftQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
    (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairFst_mem_FP)) pairSnd_mem_FP
theorem rightQuery_FP : rightQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
    (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) pairSnd_mem_FP)) pairSnd_mem_FP

noncomputable def read (P : Readers) (F : BoundedAlgebraicSlice.Family) (q : List Bool) : List Bool :=
  pair (BoundedAlgebraicFiberSignatureRead.value P F (leftQuery q)) (BoundedAlgebraicFiberSignatureRead.value P F (rightQuery q))
theorem read_evaluator {P : Readers} (h : P.PolyTime) {F : BoundedAlgebraicSlice.Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (read P F) :=
  ((BoundedAlgebraicFiberSignatureRead.evaluator h A ha).precompose leftQuery leftQuery_FP).pairOutputs
    ((BoundedAlgebraicFiberSignatureRead.evaluator h A ha).precompose rightQuery rightQuery_FP)

noncomputable def bound (F : BoundedAlgebraicSlice.Family) (u : List Bool) : List Bool :=
  BinaryNatCode.encode (F.degree (pairFst (pairFst u)) + 1)
theorem bound_FP {F : BoundedAlgebraicSlice.Family} (A : F.Access) : bound F ∈ FP := by
  have hd : BinaryFn (fun u => F.degree (pairFst (pairFst u))) :=
    A.degree_binary.comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  exact (hd.add (BinaryFn.const 1)).bits_mem_FP

noncomputable def value (P : Readers) (F : BoundedAlgebraicSlice.Family) : List Bool → List Bool := ThomOrderBits.value (read P F) (bound F)
theorem evaluator {P : Readers} (h : P.PolyTime) {F : BoundedAlgebraicSlice.Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (value P F) :=
  ThomOrderBits.evaluator (read_evaluator h A ha) (bound_FP A)

theorem read_packet (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) (a b : Fin (BoundedAlgebraicSlice.RootCount.count P F c)) (k : ℕ) :
    read P F (pair (pair c (pair (BinaryNatCode.encode a.val) (BinaryNatCode.encode b.val))) (BinaryNatCode.encode k)) =
      pair (InfinitesimalSign.encode (ThomEncoding.sign
        (BoundedAlgebraicSlice.specialized P F c) (BoundedAlgebraicFiberHashEnumeration.root P F c a).val k))
        (InfinitesimalSign.encode (ThomEncoding.sign
          (BoundedAlgebraicSlice.specialized P F c) (BoundedAlgebraicFiberHashEnumeration.root P F c b).val k)) := by
  simp only [read, leftQuery, rightQuery, pairFst_pair, pairSnd_pair]
  rw [BoundedAlgebraicFiberSignatureRead.derivative_packet, BoundedAlgebraicFiberSignatureRead.derivative_packet]
  rfl

theorem value_packet (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) (a b : Fin (BoundedAlgebraicSlice.RootCount.count P F c)) :
    value P F (pair c (pair (BinaryNatCode.encode a.val) (BinaryNatCode.encode b.val))) =
      [decide ((BoundedAlgebraicFiberHashEnumeration.root P F c a).val < (BoundedAlgebraicFiberHashEnumeration.root P F c b).val)] := by
  let p := BoundedAlgebraicSlice.specialized P F c
  let x := BoundedAlgebraicFiberHashEnumeration.root P F c a
  let y := BoundedAlgebraicFiberHashEnumeration.root P F c b
  have hp : p ≠ 0 := Polynomial.ne_zero_of_mem_roots (Multiset.mem_toFinset.mp x.property)
  have hx : p.IsRoot x.val := Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp x.property)
  have hy : p.IsRoot y.val := Polynomial.isRoot_of_mem_roots (Multiset.mem_toFinset.mp y.property)
  have hbound : Nat.fromBitsLE (bound F (pair c (pair (BinaryNatCode.encode a.val) (BinaryNatCode.encode b.val)))) =
      F.degree (pairFst c) + 1 := by
    simp only [bound, pairFst_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [value, ThomOrderBits.value, hbound]
  rw [ThomOrderBits.fold_packet (read P F) _ (ThomEncoding.sign p x.val) (ThomEncoding.sign p y.val)
    (read_packet P F c a b)]
  rw [ThomEncoding.orderScan_roots p hp (F.degree (pairFst c))
    (BoundedAlgebraicSlice.specialized_degree P F c) _ _ hx hy]

/-- The real-order index used by the geometric fiber labels. -/
noncomputable def rank (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) (a : Fin (BoundedAlgebraicSlice.RootCount.count P F c)) : ℕ :=
  (((BoundedAlgebraicSlice.RootCount.roots P F c).orderIsoOfFin rfl).symm (BoundedAlgebraicFiberHashEnumeration.root P F c a)).val

theorem rank_lt_iff (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) (a b : Fin (BoundedAlgebraicSlice.RootCount.count P F c)) :
    rank P F c a < rank P F c b ↔
      (BoundedAlgebraicFiberHashEnumeration.root P F c a).val < (BoundedAlgebraicFiberHashEnumeration.root P F c b).val :=
  ((BoundedAlgebraicSlice.RootCount.roots P F c).orderIsoOfFin rfl).symm.lt_iff_lt

theorem value_rank (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) (a b : Fin (BoundedAlgebraicSlice.RootCount.count P F c)) :
    value P F (pair c (pair (BinaryNatCode.encode a.val) (BinaryNatCode.encode b.val))) =
      [decide (rank P F c a < rank P F c b)] := by
  rw [value_packet]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, rank_lt_iff]

end LeanCanny.Encoding.BoundedAlgebraicFiberRootOrder
