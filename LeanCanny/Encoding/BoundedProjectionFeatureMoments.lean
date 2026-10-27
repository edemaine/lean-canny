/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedProjectionBasisMoments

/-! # Native selected-basis moments weighted by one derivative sign

Two selected sparse records and one derivative-sign block are concatenated
for the original Tarski reader. The block uses a bounded binary derivative
index; arbitrary raw indices are clamped to the final feature. No full
signature or table of weighted entries is stored.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedProjectionFeatureMoments
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open BoundedProjectionRankBasis
open scoped Classical BigOperators

noncomputable def order (P : Readers) (q : List Bool) : ℕ :=
  min (Nat.fromBitsLE (pairSnd q)) (BoundedProjectionRootCount.degree P (pairFst q))
theorem order_binary {P : Readers} (h : P.PolyTime) : BinaryFn (order P) := by
  have hi := BinaryFn.fromBits pairSnd_mem_FP
  have hd := (BoundedProjectionRootCount.degree_binary h).comp pairFst_mem_FP
  have H := BinaryFn.ite (hi.le hd) hi hd
  exact BinaryFn.of_eq H (fun _ => by simp only [order, min_def, Function.comp_apply])

noncomputable def block (P : Readers) (q : List Bool) : List Bool :=
  ImplicitGraph.word (BoundedProjectionRecords.width P (pairFst q)) (order P q + 1)
theorem block_FP {P : Readers} (h : P.PolyTime) : block P ∈ FP :=
  ImplicitGraph.word_computable ((BoundedProjectionRecords.width_unary h).comp pairFst_mem_FP)
    ((order_binary h).add (BinaryFn.const 1))

theorem block_packet (P : Readers) (c : List Bool) (d : BoundedProjectionMoments.Feature P c) :
    block P (pair c (BinaryNatCode.encode d.val)) = ImplicitGraph.word (BoundedProjectionRecords.width P c) (d.val + 1) := by
  have hd : d.val ≤ BoundedProjectionRootCount.degree P c := by have H := d.isLt; omega
  simp only [block, order, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.min_eq_left hd]

theorem block_length (P : Readers) (q : List Bool) : (block P q).length = BoundedProjectionRecords.width P (pairFst q) :=
  ImplicitGraph.length_word _ _

theorem block_value (P : Readers) (c : List Bool) (d : BoundedProjectionMoments.Feature P c)
    (x : BoundedProjectionRecordSpan.Root P c) :
    SparseFeatureRecords.value (Nat.succ_pos _) 1 (BoundedProjectionRecords.width P c)
      (fun i => (BoundedProjectionMoments.signature P c x i : ℚ)) (block P (pair c (BinaryNatCode.encode d.val))) =
        (BoundedProjectionMoments.signature P c x d : ℚ) := by
  have hd : d.val + 1 < 2 ^ BoundedProjectionRecords.width P c :=
    (Nat.succ_le_of_lt d.isLt).trans_lt (BoundedProjectionRecordSpan.feature_fits P c)
  have he := FixedWidthNatVector.decode_block 1 (BoundedProjectionRecords.width P c) (fun _ => d.val + 1) 0 (by decide) hd
  simp only [Nat.zero_mul, List.drop_zero] at he
  have hs : SparseFeatureRecords.coordinate (BoundedProjectionRecords.width P c)
      (block P (pair c (BinaryNatCode.encode d.val))) 0 = d.val + 1 := by
    rw [block_packet]
    simp only [SparseFeatureRecords.coordinate, Nat.zero_mul, List.drop_zero, ImplicitGraph.word]
    exact he
  simp only [SparseFeatureRecords.value, Finset.prod_range_succ, Finset.prod_range_zero, one_mul, hs,
    SparseFeatureRecords.factor_succ]

noncomputable def source (P : Readers) (q : List Bool) : List Bool := pair (pairFst q)
  ((BoundedProjectionBasisMoments.record P (BoundedProjectionBasisMoments.firstQuery q) ++
    BoundedProjectionBasisMoments.record P (BoundedProjectionBasisMoments.secondQuery q)) ++
      block P (BoundedProjectionBasisMoments.thirdQuery q))
theorem source_evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (source P) := by
  have E := BoundedProjectionBasisMoments.record_evaluator h ha
  have A := E.precompose BoundedProjectionBasisMoments.firstQuery BoundedProjectionBasisMoments.firstQuery_FP
  have B := E.precompose BoundedProjectionBasisMoments.secondQuery BoundedProjectionBasisMoments.secondQuery_FP
  have C := SpaceFunction.ofFP (block P ∘ BoundedProjectionBasisMoments.thirdQuery)
    (mem_FP_comp BoundedProjectionBasisMoments.thirdQuery_FP (block_FP h))
  have H := (A.pairOutputs (B.pairOutputs C)).withInput.postcompose
    BoundedProjectionBasisMoments.finish BoundedProjectionBasisMoments.finish_FP
  exact H.congr (funext fun q => by simp only [source, BoundedProjectionBasisMoments.finish, Function.comp_apply,
    pairFst_pair, pairSnd_pair])

noncomputable def moment (P : Readers) (q : List Bool) : ℤ := BoundedProjectionRecords.moment P (source P q)
theorem evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun q => SignStatisticBits.integerCode (moment P q)) :=
  (source_evaluator h ha).chain (BoundedProjectionRecords.evaluator h ha)

theorem moment_bound (P : Readers) (q : List Bool) :
    (moment P q).natAbs ≤ 2 ^ BoundedCriticalProjection.labelWidth P (pairFst q) := by
  have H := BoundedProjectionBasisMoments.raw_moment_bound P (source P q)
  simpa only [moment, source, pairFst_pair] using H

theorem moment_packet (P : Readers) (c : List Bool) (i j : Fin (BoundedProjectionRootCount.count P c))
    (d : BoundedProjectionMoments.Feature P c) :
    (moment P (pair c (pair (BinaryNatCode.encode i.val) (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode d.val)))) : ℚ) =
      ∑ x : BoundedProjectionRecordSpan.Root P c, selected P c i x * selected P c j x *
        (BoundedProjectionMoments.signature P c x d : ℚ) := by
  let a := BoundedProjectionRootHash.record P c i
  let b := BoundedProjectionRootHash.record P c j
  let f := block P (pair c (BinaryNatCode.encode d.val))
  have ha : a.length = BoundedProjectionRecords.length P c := ImplicitGraph.length_word _ _
  have hb : b.length = BoundedProjectionRecords.length P c := ImplicitGraph.length_word _ _
  have hf : f.length = BoundedProjectionRecords.width P c := by rw [block_length, pairFst_pair]
  have hs : source P (pair c (pair (BinaryNatCode.encode i.val) (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode d.val)))) =
      pair c ((a ++ b) ++ f) := by
    simp only [source, BoundedProjectionBasisMoments.firstQuery, BoundedProjectionBasisMoments.secondQuery,
      BoundedProjectionBasisMoments.thirdQuery, pairFst_pair, pairSnd_pair, BoundedProjectionBasisMoments.record_packet]
    rfl
  rw [moment, hs, BoundedProjectionRecordSpan.moment_eq_sum_values]
  have hc : BoundedProjectionRecords.recordSlots P (pair c ((a ++ b) ++ f)) =
      (BoundedProjectionRecords.slots P c + BoundedProjectionRecords.slots P c) + 1 := by
    simp only [BoundedProjectionRecords.recordSlots, pairFst_pair, pairSnd_pair, List.length_append,
      ha, hb, hf, BoundedProjectionRecords.length]
    have he : BoundedProjectionRecords.slots P c * BoundedProjectionRecords.width P c +
        BoundedProjectionRecords.slots P c * BoundedProjectionRecords.width P c + BoundedProjectionRecords.width P c =
          (BoundedProjectionRecords.slots P c + BoundedProjectionRecords.slots P c + 1) * BoundedProjectionRecords.width P c := by ring
    rw [he, Nat.mul_div_cancel _ (BoundedProjectionRecords.width_pos P c)]
  rw [hc]
  have hab : (a ++ b).length = (BoundedProjectionRecords.slots P c + BoundedProjectionRecords.slots P c) *
      BoundedProjectionRecords.width P c := by rw [List.length_append, ha, hb, BoundedProjectionRecords.length, Nat.add_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [SparseFeatureRecords.value_append _ _ _ _ _ (a ++ b) f hab,
    SparseFeatureRecords.value_append _ _ _ _ _ a b ha,
    BoundedProjectionBasisMoments.selected_value, BoundedProjectionBasisMoments.selected_value, block_value]

end LeanCanny.Encoding.BoundedProjectionFeatureMoments
