/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleFiberBasisMoments

/-! # Native child-basis moments weighted by a derivative sign

Two selected sparse records and one derivative-sign block are concatenated
for the original Tarski reader. The block uses a bounded binary derivative
index; arbitrary raw indices are clamped to the final feature. No full
signature or table of weighted entries is stored. The sample descriptor
and original query record are preserved.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleFiberFeatureMoments
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open BoundedAlgebraicSlice (Family)
open BoundedCriticalSampleSlice BoundedCriticalSampleFiberRankBasis
open scoped Classical BigOperators

noncomputable def order (F : Family) (q : List Bool) : ℕ :=
  min (Nat.fromBitsLE (pairSnd q)) (F.degree (context (pairFst q)))
theorem order_binary {F : Family} (A : F.Access) : BinaryFn (order F) := by
  have hi := BinaryFn.fromBits pairSnd_mem_FP
  have hd : BinaryFn (fun q => F.degree (context (pairFst q))) :=
    A.degree_binary.comp (mem_FP_comp pairFst_mem_FP context_FP)
  have H := BinaryFn.ite (hi.le hd) hi hd
  exact BinaryFn.of_eq H (fun _ => by simp only [order, min_def])

noncomputable def block (F : Family) (q : List Bool) : List Bool :=
  ImplicitGraph.word (BoundedAlgebraicFiberRecords.width F (context (pairFst q))) (order F q + 1)
theorem block_FP {F : Family} (A : F.Access) : block F ∈ FP :=
  ImplicitGraph.word_computable ((BoundedAlgebraicFiberRecords.width_unary A).comp
    (mem_FP_comp pairFst_mem_FP context_FP)) ((order_binary A).add (BinaryFn.const 1))

theorem block_packet (F : Family) (c : List Bool) (d : BoundedCriticalSampleFiberThom.Feature F c) :
    block F (pair c (BinaryNatCode.encode d.val)) = ImplicitGraph.word (BoundedAlgebraicFiberRecords.width F (context c)) (d.val + 1) := by
  have hd : d.val ≤ F.degree (context c) := by have H := d.isLt; omega
  simp only [block, order, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.min_eq_left hd]

theorem block_length (F : Family) (q : List Bool) : (block F q).length = BoundedAlgebraicFiberRecords.width F (context (pairFst q)) :=
  ImplicitGraph.length_word _ _

theorem block_value (P : Readers) (F : Family) (c : List Bool) (d : BoundedCriticalSampleFiberThom.Feature F c)
    (x : BoundedCriticalSampleFiberRecordSpan.Root P F c) :
    SparseFeatureRecords.value (Nat.succ_pos _) 1 (BoundedAlgebraicFiberRecords.width F (context c))
      (fun i => (BoundedCriticalSampleFiberThom.signature P F c x i : ℚ)) (block F (pair c (BinaryNatCode.encode d.val))) =
        (BoundedCriticalSampleFiberThom.signature P F c x d : ℚ) := by
  have hd : d.val + 1 < 2 ^ BoundedAlgebraicFiberRecords.width F (context c) :=
    (Nat.succ_le_of_lt d.isLt).trans_lt (BoundedAlgebraicFiberRecords.feature_fits F (context c))
  have he := FixedWidthNatVector.decode_block 1 (BoundedAlgebraicFiberRecords.width F (context c)) (fun _ => d.val + 1) 0 (by decide) hd
  simp only [Nat.zero_mul, List.drop_zero] at he
  have hs : SparseFeatureRecords.coordinate (BoundedAlgebraicFiberRecords.width F (context c))
      (block F (pair c (BinaryNatCode.encode d.val))) 0 = d.val + 1 := by
    rw [block_packet]
    simp only [SparseFeatureRecords.coordinate, Nat.zero_mul, List.drop_zero, ImplicitGraph.word]
    exact he
  simp only [SparseFeatureRecords.value, Finset.prod_range_succ, Finset.prod_range_zero, one_mul, hs,
    SparseFeatureRecords.factor_succ]

noncomputable def source (P : Readers) (F : Family) (q : List Bool) : List Bool := pair (pairFst q)
  ((BoundedCriticalSampleFiberBasisMoments.record P F (BoundedCriticalSampleFiberBasisMoments.firstQuery q) ++
    BoundedCriticalSampleFiberBasisMoments.record P F (BoundedCriticalSampleFiberBasisMoments.secondQuery q)) ++
      block F (BoundedCriticalSampleFiberBasisMoments.thirdQuery q))
theorem source_evaluator {P : Readers} (h : P.PolyTime) {F : Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (source P F) := by
  have E := BoundedCriticalSampleFiberBasisMoments.record_evaluator h A ha
  have L := E.precompose BoundedCriticalSampleFiberBasisMoments.firstQuery BoundedCriticalSampleFiberBasisMoments.firstQuery_FP
  have R := E.precompose BoundedCriticalSampleFiberBasisMoments.secondQuery BoundedCriticalSampleFiberBasisMoments.secondQuery_FP
  have T := SpaceFunction.ofFP (block F ∘ BoundedCriticalSampleFiberBasisMoments.thirdQuery)
    (mem_FP_comp BoundedCriticalSampleFiberBasisMoments.thirdQuery_FP (block_FP A))
  have H := (L.pairOutputs (R.pairOutputs T)).withInput.postcompose
    BoundedCriticalSampleFiberBasisMoments.finish BoundedCriticalSampleFiberBasisMoments.finish_FP
  exact H.congr (funext fun q => by simp only [source, BoundedCriticalSampleFiberBasisMoments.finish, Function.comp_apply,
    pairFst_pair, pairSnd_pair])

noncomputable def moment (P : Readers) (F : Family) (q : List Bool) : ℤ := BoundedCriticalSampleFiberRecordMoments.moment P F (source P F q)
theorem evaluator {P : Readers} (h : P.PolyTime) {F : Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun q => SignStatisticBits.integerCode (moment P F q)) :=
  (source_evaluator h A ha).chain (BoundedCriticalSampleFiberRecordMoments.evaluator h A ha)

theorem moment_bound (P : Readers) (F : Family) (q : List Bool) :
    (moment P F q).natAbs ≤ F.degree (context (pairFst q)) := by
  have H := BoundedCriticalSampleFiberBasisMoments.raw_moment_bound P F (source P F q)
  simpa only [moment, source, pairFst_pair] using H

theorem moment_packet (P : Readers) (F : Family) (c : List Bool) (i j : Fin (RootCount.count P F c))
    (d : BoundedCriticalSampleFiberThom.Feature F c) :
    (moment P F (pair c (pair (BinaryNatCode.encode i.val) (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode d.val)))) : ℚ) =
      ∑ x : BoundedCriticalSampleFiberRecordSpan.Root P F c, selected P F c i x * selected P F c j x *
        (BoundedCriticalSampleFiberThom.signature P F c x d : ℚ) := by
  let a := BoundedCriticalSampleFiberBasisMoments.selectedRecord P F c i
  let b := BoundedCriticalSampleFiberBasisMoments.selectedRecord P F c j
  let f := block F (pair c (BinaryNatCode.encode d.val))
  have ha : a.length = BoundedAlgebraicFiberRecords.length F (context c) := ImplicitGraph.length_word _ _
  have hb : b.length = BoundedAlgebraicFiberRecords.length F (context c) := ImplicitGraph.length_word _ _
  have hf : f.length = BoundedAlgebraicFiberRecords.width F (context c) := by rw [block_length, pairFst_pair]
  have hs : source P F (pair c (pair (BinaryNatCode.encode i.val) (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode d.val)))) =
      pair c ((a ++ b) ++ f) := by
    simp only [source, BoundedCriticalSampleFiberBasisMoments.firstQuery, BoundedCriticalSampleFiberBasisMoments.secondQuery,
      BoundedCriticalSampleFiberBasisMoments.thirdQuery, pairFst_pair, pairSnd_pair, BoundedCriticalSampleFiberBasisMoments.record_packet]
    rfl
  rw [moment, hs, BoundedCriticalSampleFiberRecordMoments.moment_eq_sum_values]
  have hc : BoundedAlgebraicFiberRecords.recordSlots F (pair (context c) ((a ++ b) ++ f)) =
      (BoundedAlgebraicFiberRecords.slots F (context c) + BoundedAlgebraicFiberRecords.slots F (context c)) + 1 := by
    simp only [BoundedAlgebraicFiberRecords.recordSlots, pairFst_pair, pairSnd_pair, List.length_append,
      ha, hb, hf, BoundedAlgebraicFiberRecords.length]
    have he : BoundedAlgebraicFiberRecords.slots F (context c) * BoundedAlgebraicFiberRecords.width F (context c) +
        BoundedAlgebraicFiberRecords.slots F (context c) * BoundedAlgebraicFiberRecords.width F (context c) + BoundedAlgebraicFiberRecords.width F (context c) =
          (BoundedAlgebraicFiberRecords.slots F (context c) + BoundedAlgebraicFiberRecords.slots F (context c) + 1) * BoundedAlgebraicFiberRecords.width F (context c) := by ring
    rw [he, Nat.mul_div_cancel _ (BoundedAlgebraicFiberRecords.width_pos F (context c))]
  rw [hc]
  have hab : (a ++ b).length = (BoundedAlgebraicFiberRecords.slots F (context c) + BoundedAlgebraicFiberRecords.slots F (context c)) *
      BoundedAlgebraicFiberRecords.width F (context c) := by rw [List.length_append, ha, hb, BoundedAlgebraicFiberRecords.length, Nat.add_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [SparseFeatureRecords.value_append _ _ _ _ _ (a ++ b) f hab,
    SparseFeatureRecords.value_append _ _ _ _ _ a b ha,
    BoundedCriticalSampleFiberBasisMoments.selected_value, BoundedCriticalSampleFiberBasisMoments.selected_value, block_value]

end LeanCanny.Encoding.BoundedCriticalSampleFiberFeatureMoments
