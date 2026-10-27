/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedProjectionRootHash

/-! # Native triple moments of the selected projection-sign basis

The selected record reader recomputes its row index using native prefix
ranks. Concatenating three such records feeds the original Tarski reader.
Thus triple products need no basis table or supplied moment oracle.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedProjectionBasisMoments
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open BoundedProjectionRankBasis
open scoped Classical BigOperators

noncomputable def record (P : Readers) (q : List Bool) : List Bool :=
  ImplicitGraph.word (BoundedProjectionRecords.length P (pairFst q)) (BoundedProjectionRankChoice.index P q)

noncomputable def recordFinish (P : Readers) (z : List Bool) : List Bool :=
  ImplicitGraph.word (BoundedProjectionRecords.length P (pairFst (pairFst z))) (Nat.fromBitsLE (pairSnd z))

theorem recordFinish_FP {P : Readers} (h : P.PolyTime) : recordFinish P ∈ FP :=
  ImplicitGraph.word_computable ((BoundedProjectionRecords.length_unary h).comp
    (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)) (BinaryFn.fromBits pairSnd_mem_FP)

theorem record_evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (record P) := by
  have H := (BoundedProjectionRankChoice.evaluator h ha).withInput.postcompose (recordFinish P) (recordFinish_FP h)
  exact H.congr (funext fun q => by simp only [record, recordFinish, Function.comp_apply,
    pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits])

theorem record_packet (P : Readers) (c : List Bool) (r : Fin (BoundedProjectionRootCount.count P c)) :
    record P (pair c (BinaryNatCode.encode r.val)) = BoundedProjectionRootHash.record P c r := by
  simp only [record, pairFst_pair, BoundedProjectionRootHash.record, chosen]

theorem record_length (P : Readers) (q : List Bool) :
    (record P q).length = BoundedProjectionRecords.length P (pairFst q) := ImplicitGraph.length_word _ _

def firstQuery (q : List Bool) : List Bool := pair (pairFst q) (pairFst (pairSnd q))
def secondQuery (q : List Bool) : List Bool := pair (pairFst q) (pairFst (pairSnd (pairSnd q)))
def thirdQuery (q : List Bool) : List Bool := pair (pairFst q) (pairSnd (pairSnd (pairSnd q)))
theorem firstQuery_FP : firstQuery ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
theorem secondQuery_FP : secondQuery ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairFst_mem_FP)
theorem thirdQuery_FP : thirdQuery ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairSnd_mem_FP)

noncomputable def source (P : Readers) (q : List Bool) : List Bool := pair (pairFst q)
  ((record P (firstQuery q) ++ record P (secondQuery q)) ++ record P (thirdQuery q))

def finish (z : List Bool) : List Bool := pair (pairFst (pairFst z))
  ((pairFst (pairSnd z) ++ pairFst (pairSnd (pairSnd z))) ++ pairSnd (pairSnd (pairSnd z)))
theorem finish_FP : finish ∈ FP := by
  have hs := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
  have hA := appendFn_mem_FP (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) (mem_FP_comp hs pairFst_mem_FP)
  exact mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) (appendFn_mem_FP hA (mem_FP_comp hs pairSnd_mem_FP))

theorem source_evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (source P) := by
  have E := record_evaluator h ha
  have A := E.precompose firstQuery firstQuery_FP
  have B := E.precompose secondQuery secondQuery_FP
  have C := E.precompose thirdQuery thirdQuery_FP
  have H := (A.pairOutputs (B.pairOutputs C)).withInput.postcompose finish finish_FP
  exact H.congr (funext fun q => by simp only [source, finish, Function.comp_apply, pairFst_pair, pairSnd_pair])

noncomputable def moment (P : Readers) (q : List Bool) : ℤ := BoundedProjectionRecords.moment P (source P q)
theorem evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun q => SignStatisticBits.integerCode (moment P q)) :=
  (source_evaluator h ha).chain (BoundedProjectionRecords.evaluator h ha)

theorem selected_value (P : Readers) (c : List Bool) (r : Fin (BoundedProjectionRootCount.count P c))
    (x : BoundedProjectionRecordSpan.Root P c) :
    SparseFeatureRecords.value (Nat.succ_pos _) (BoundedProjectionRecords.slots P c)
      (BoundedProjectionRecords.width P c)
      (fun i => (BoundedProjectionMoments.signature P c x i : ℚ)) (BoundedProjectionRootHash.record P c r) =
        selected P c r x := by
  rw [selected, Matrix.row, BoundedProjectionRecordSpan.matrix, BoundedProjectionRecordSpan.row_apply]
  rfl

theorem moment_packet (P : Readers) (c : List Bool)
    (i j k : Fin (BoundedProjectionRootCount.count P c)) :
    (moment P (pair c (pair (BinaryNatCode.encode i.val)
      (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode k.val)))) : ℚ) =
      ∑ x : BoundedProjectionRecordSpan.Root P c, selected P c i x * selected P c j x * selected P c k x := by
  let a := BoundedProjectionRootHash.record P c i
  let b := BoundedProjectionRootHash.record P c j
  let d := BoundedProjectionRootHash.record P c k
  have ha : a.length = BoundedProjectionRecords.length P c := ImplicitGraph.length_word _ _
  have hb : b.length = BoundedProjectionRecords.length P c := ImplicitGraph.length_word _ _
  have hd : d.length = BoundedProjectionRecords.length P c := ImplicitGraph.length_word _ _
  have hs : source P (pair c (pair (BinaryNatCode.encode i.val)
      (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode k.val)))) = pair c ((a ++ b) ++ d) := by
    simp only [source, firstQuery, secondQuery, thirdQuery, pairFst_pair, pairSnd_pair, record_packet]
    rfl
  rw [moment, hs, BoundedProjectionRecordSpan.moment_eq_sum_values]
  have hc : BoundedProjectionRecords.recordSlots P (pair c ((a ++ b) ++ d)) =
      (BoundedProjectionRecords.slots P c + BoundedProjectionRecords.slots P c) + BoundedProjectionRecords.slots P c := by
    simp only [BoundedProjectionRecords.recordSlots, pairFst_pair, pairSnd_pair, List.length_append,
      ha, hb, hd, BoundedProjectionRecords.length]
    rw [← Nat.add_mul, ← Nat.add_mul, Nat.mul_div_cancel _ (BoundedProjectionRecords.width_pos P c)]
  rw [hc]
  have hab : (a ++ b).length = (BoundedProjectionRecords.slots P c + BoundedProjectionRecords.slots P c) *
      BoundedProjectionRecords.width P c := by rw [List.length_append, ha, hb, BoundedProjectionRecords.length, Nat.add_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [SparseFeatureRecords.value_append _ _ _ _ _ (a ++ b) d hab,
    SparseFeatureRecords.value_append _ _ _ _ _ a b ha]
  rw [selected_value, selected_value, selected_value]

theorem raw_moment_bound (P : Readers) (z : List Bool) :
    (BoundedProjectionRecords.moment P z).natAbs ≤ 2 ^ BoundedCriticalProjection.labelWidth P (pairFst z) := by
  have hv := RootSignQueries.tarskiQuery_bounds (((BoundedProjectionRecords.family P).root z).map (algebraMap ℤ ℝ))
    (((BoundedProjectionRecords.family P).product z).map (algebraMap ℤ ℝ))
  change -((((BoundedProjectionRecords.family P).root z).map (algebraMap ℤ ℝ)).natDegree : ℤ) ≤
      BoundedProjectionRecords.moment P z ∧ BoundedProjectionRecords.moment P z ≤
      ((((BoundedProjectionRecords.family P).root z).map (algebraMap ℤ ℝ)).natDegree : ℤ) at hv
  have hd : (((BoundedProjectionRecords.family P).root z).map (algebraMap ℤ ℝ)).natDegree ≤
      Nat.fromBitsLE ((BoundedProjectionRecords.family P).rootDegree z) :=
    Polynomial.natDegree_map_le.trans ((BoundedProjectionRecords.family P).root_degree z)
  have he : Nat.fromBitsLE ((BoundedProjectionRecords.family P).rootDegree z) =
      2 ^ BoundedCriticalProjection.labelWidth P (pairFst z) := by
    simp only [BoundedProjectionRecords.family, BinaryNatCode.encode, Nat.fromBitsLE_bits,
      BoundedProjectionRootCount.degree]
  rw [he] at hd
  omega

theorem moment_bound (P : Readers) (q : List Bool) :
    (moment P q).natAbs ≤ 2 ^ BoundedCriticalProjection.labelWidth P (pairFst q) := by
  have H := raw_moment_bound P (source P q)
  simpa only [moment, source, pairFst_pair] using H

end LeanCanny.Encoding.BoundedProjectionBasisMoments
