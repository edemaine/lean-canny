/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicFiberRecordMoments

/-! # Native entries of the full fiber-record Gram matrix

Concatenating two fixed-length records computes their inner product over
the actual distinct roots. The matrix has the full root count as rank;
its dimension and entry budgets have native binary controls.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicFiberRecordGram
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter BoundedAlgebraicSlice
open BoundedAlgebraicFiberRecords BoundedAlgebraicFiberRecordSpan
open scoped Classical BigOperators

noncomputable def gramQuery (F : Family) (q : List Bool) : List Bool := pair (pairFst q)
  (ImplicitGraph.word (length F (pairFst (pairFst q))) (Nat.fromBitsLE (pairFst (pairSnd q))) ++
    ImplicitGraph.word (length F (pairFst (pairFst q))) (Nat.fromBitsLE (pairSnd (pairSnd q))))

theorem gramQuery_FP {F : Family} (A : F.Access) : gramQuery F ∈ FP := by
  have hw := (length_unary A).comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  have hL := ImplicitGraph.word_computable hw (BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP))
  have hR := ImplicitGraph.word_computable hw (BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP))
  have H := mem_FP_pair pairFst_mem_FP (appendFn_mem_FP hL hR)
  exact mem_FP_of_eq H (fun _ => by simp only [gramQuery, Function.comp_apply])

noncomputable def entry (P : Readers) (F : Family) (q : List Bool) : ℤ :=
  BoundedAlgebraicFiberRecordMoments.moment P F (gramQuery F q)

theorem evaluator {P : Readers} (h : P.PolyTime) {F : Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun q => SignStatisticBits.integerCode (entry P F q)) :=
  (BoundedAlgebraicFiberRecordMoments.evaluator h A ha).precompose (gramQuery F) (gramQuery_FP A)

theorem entry_bound (P : Readers) (F : Family) (q : List Bool) :
    (entry P F q).natAbs ≤ F.degree (pairFst (pairFst q)) := by
  simpa only [entry, gramQuery, pairFst_pair] using BoundedAlgebraicFiberRecordMoments.moment_bound P F (gramQuery F q)

theorem entry_packet (P : Readers) (F : Family) (u : List Bool) (i j : Index F u) :
    (entry P F (pair u (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) : ℚ) = gram P F u i j := by
  simp only [entry, gramQuery, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  let r := ImplicitGraph.word (length F (pairFst u)) i.val
  let s := ImplicitGraph.word (length F (pairFst u)) j.val
  have hr : r.length = length F (pairFst u) := ImplicitGraph.length_word _ _
  have hs : s.length = length F (pairFst u) := ImplicitGraph.length_word _ _
  have hc : recordSlots F (pair (pairFst u) (r ++ s)) = slots F (pairFst u) + slots F (pairFst u) := by
    simp only [recordSlots, pairFst_pair, pairSnd_pair, List.length_append, hr, hs, BoundedAlgebraicFiberRecords.length]
    rw [← Nat.add_mul, Nat.mul_div_cancel _ (width_pos F (pairFst u))]
  rw [BoundedAlgebraicFiberRecordMoments.moment_eq_sum_values, hc]
  change (∑ x : Root P F u, SparseFeatureRecords.value (Nat.succ_pos _)
    (slots F (pairFst u) + slots F (pairFst u)) (width F (pairFst u))
    (fun k : Feature F u => (BoundedAlgebraicFiberThom.signature P F u x k : ℚ)) (r ++ s)) = _
  simp_rw [SparseFeatureRecords.value_append _ _ _ _ _ r s hr]
  change _ = ∑ x : Root P F u, matrix P F u i x * matrix P F u j x
  apply Finset.sum_congr rfl
  intro x _
  rw [← row_apply P F u r x, ← row_apply P F u s x]
  rfl

end LeanCanny.Encoding.BoundedAlgebraicFiberRecordGram
