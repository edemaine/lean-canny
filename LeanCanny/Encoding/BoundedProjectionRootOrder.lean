/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedProjectionSignatureRead
public import LeanCanny.Algebra.ThomOrderSpace

/-! # Native real-order comparisons of short projection-root labels

Input is `pair sourceContext (pair leftHashOrdinal rightHashOrdinal)`.
The roots are enumerated by their hashes, while this query compares their
actual real coordinates. Every derivative sign is recomputed natively.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedProjectionRootOrder
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

noncomputable def read (P : Readers) (q : List Bool) : List Bool :=
  pair (BoundedProjectionSignatureRead.value P (leftQuery q)) (BoundedProjectionSignatureRead.value P (rightQuery q))
theorem read_evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (read P) :=
  ((BoundedProjectionSignatureRead.evaluator h ha).precompose leftQuery leftQuery_FP).pairOutputs
    ((BoundedProjectionSignatureRead.evaluator h ha).precompose rightQuery rightQuery_FP)

noncomputable def bound (P : Readers) (u : List Bool) : List Bool :=
  BinaryNatCode.encode (BoundedProjectionRootCount.degree P (pairFst u) + 1)
theorem bound_FP {P : Readers} (h : P.PolyTime) : bound P ∈ FP := by
  have hd : BinaryFn (fun u => BoundedProjectionRootCount.degree P (pairFst u)) :=
    (BoundedProjectionRootCount.degree_binary h).comp pairFst_mem_FP
  exact (hd.add (BinaryFn.const 1)).bits_mem_FP

noncomputable def value (P : Readers) : List Bool → List Bool := ThomOrderBits.value (read P) (bound P)
theorem evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (value P) :=
  ThomOrderBits.evaluator (read_evaluator h ha) (bound_FP h)

theorem read_packet (P : Readers) (c : List Bool) (a b : Fin (BoundedProjectionRootCount.count P c)) (k : ℕ) :
    read P (pair (pair c (pair (BinaryNatCode.encode a.val) (BinaryNatCode.encode b.val))) (BinaryNatCode.encode k)) =
      pair (InfinitesimalSign.encode (ThomEncoding.sign
        ((BoundedCriticalProjection.polynomial P c).map (Int.castRingHom ℝ)) (BoundedProjectionHashEnumeration.root P c a).val k))
        (InfinitesimalSign.encode (ThomEncoding.sign
          ((BoundedCriticalProjection.polynomial P c).map (Int.castRingHom ℝ)) (BoundedProjectionHashEnumeration.root P c b).val k)) := by
  simp only [read, leftQuery, rightQuery, pairFst_pair, pairSnd_pair]
  rw [BoundedProjectionSignatureRead.derivative_packet, BoundedProjectionSignatureRead.derivative_packet]
  simp only [ThomEncoding.sign, BoundedProjectionThom.polynomial, Polynomial.iterate_derivative_map]

theorem value_packet (P : Readers) (c : List Bool) (a b : Fin (BoundedProjectionRootCount.count P c)) :
    value P (pair c (pair (BinaryNatCode.encode a.val) (BinaryNatCode.encode b.val))) =
      [decide ((BoundedProjectionHashEnumeration.root P c a).val < (BoundedProjectionHashEnumeration.root P c b).val)] := by
  let p := (BoundedCriticalProjection.polynomial P c).map (Int.castRingHom ℝ)
  let x := BoundedProjectionHashEnumeration.root P c a
  let y := BoundedProjectionHashEnumeration.root P c b
  have hx : p.IsRoot x.val := (Polynomial.mem_roots (BoundedCriticalLabels.mapped_ne_zero P c)).mp
    (Multiset.mem_toFinset.mp x.property)
  have hy : p.IsRoot y.val := (Polynomial.mem_roots (BoundedCriticalLabels.mapped_ne_zero P c)).mp
    (Multiset.mem_toFinset.mp y.property)
  have hbound : Nat.fromBitsLE (bound P (pair c (pair (BinaryNatCode.encode a.val) (BinaryNatCode.encode b.val)))) =
      BoundedProjectionRootCount.degree P c + 1 := by
    simp only [bound, pairFst_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [value, ThomOrderBits.value, hbound]
  rw [ThomOrderBits.fold_packet (read P) _ (ThomEncoding.sign p x.val) (ThomEncoding.sign p y.val)
    (read_packet P c a b)]
  rw [ThomEncoding.orderScan_roots p (BoundedCriticalLabels.mapped_ne_zero P c) (BoundedProjectionRootCount.degree P c)
    (Polynomial.natDegree_map_le.trans (BoundedCriticalProjection.polynomial_degree P c)) _ _ hx hy]

/-- The real-order index used by the geometric projection labels. -/
noncomputable def rank (P : Readers) (c : List Bool) (a : Fin (BoundedProjectionRootCount.count P c)) : ℕ :=
  (((BoundedCriticalLabels.rootSet P c).orderIsoOfFin rfl).symm (BoundedProjectionHashEnumeration.root P c a)).val

theorem rank_lt_iff (P : Readers) (c : List Bool) (a b : Fin (BoundedProjectionRootCount.count P c)) :
    rank P c a < rank P c b ↔
      (BoundedProjectionHashEnumeration.root P c a).val < (BoundedProjectionHashEnumeration.root P c b).val :=
  ((BoundedCriticalLabels.rootSet P c).orderIsoOfFin rfl).symm.lt_iff_lt

theorem value_rank (P : Readers) (c : List Bool) (a b : Fin (BoundedProjectionRootCount.count P c)) :
    value P (pair c (pair (BinaryNatCode.encode a.val) (BinaryNatCode.encode b.val))) =
      [decide (rank P c a < rank P c b)] := by
  rw [value_packet]
  congr 1
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, rank_lt_iff]

end LeanCanny.Encoding.BoundedProjectionRootOrder
