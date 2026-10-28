/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleChildRootHash

/-! # Native triple moments of the selected regular-child sign basis

The selected record reader recomputes its row index using native prefix
ranks. Concatenating three such records feeds the original Tarski reader.
Thus triple products need no basis table or supplied moment oracle.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleChildBasisMoments
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open BoundedCriticalSampleChildRankBasis
open BoundedCriticalSampleChildSource (Inputs)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedCriticalSampleChildRecords.length BoundedCriticalSampleChildThom.labelWidth
  BoundedCriticalSampleChildCoordinates.parameterDegree BoundedCriticalSampleChildCoordinates.baseHeight
  BoundedCriticalSampleChildQueries.roots BoundedCriticalSampleChildRegularCount.count

noncomputable def record (P : Inputs) (q : List Bool) : List Bool :=
  ImplicitGraph.word (BoundedCriticalSampleChildRecords.length P (pairFst q)) (BoundedCriticalSampleChildRankChoice.index P q)

noncomputable def recordFinish (P : Inputs) (z : List Bool) : List Bool :=
  ImplicitGraph.word (BoundedCriticalSampleChildRecords.length P (pairFst (pairFst z))) (Nat.fromBitsLE (pairSnd z))

theorem recordFinish_FP {P : Inputs} (h : P.PolyTime) : recordFinish P ∈ FP :=
  ImplicitGraph.word_computable ((BoundedCriticalSampleChildRecords.length_unary h).comp
    (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)) (BinaryFn.fromBits pairSnd_mem_FP)

theorem record_evaluator {P : Inputs} (h : P.PolyTime) : SpaceFunction (record P) := by
  have H := (BoundedCriticalSampleChildRankChoice.evaluator h).withInput.postcompose (recordFinish P) (recordFinish_FP h)
  exact H.congr (funext fun q => by simp only [record, recordFinish, Function.comp_apply,
    pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits])

theorem record_packet (P : Inputs) (c : List Bool) (r : Fin (BoundedCriticalSampleChildRegularCount.count P c)) :
    record P (pair c (BinaryNatCode.encode r.val)) = BoundedCriticalSampleChildRootHash.record P c r := by
  simp only [record, pairFst_pair, BoundedCriticalSampleChildRootHash.record, chosen]

theorem record_length (P : Inputs) (q : List Bool) :
    (record P q).length = BoundedCriticalSampleChildRecords.length P (pairFst q) := ImplicitGraph.length_word _ _

def firstQuery (q : List Bool) : List Bool := pair (pairFst q) (pairFst (pairSnd q))
def secondQuery (q : List Bool) : List Bool := pair (pairFst q) (pairFst (pairSnd (pairSnd q)))
def thirdQuery (q : List Bool) : List Bool := pair (pairFst q) (pairSnd (pairSnd (pairSnd q)))
theorem firstQuery_FP : firstQuery ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
theorem secondQuery_FP : secondQuery ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairFst_mem_FP)
theorem thirdQuery_FP : thirdQuery ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairSnd_mem_FP)

noncomputable def source (P : Inputs) (q : List Bool) : List Bool := pair (pairFst q)
  ((record P (firstQuery q) ++ record P (secondQuery q)) ++ record P (thirdQuery q))

def finish (z : List Bool) : List Bool := pair (pairFst (pairFst z))
  ((pairFst (pairSnd z) ++ pairFst (pairSnd (pairSnd z))) ++ pairSnd (pairSnd (pairSnd z)))
theorem finish_FP : finish ∈ FP := by
  have hs := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
  have hA := appendFn_mem_FP (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) (mem_FP_comp hs pairFst_mem_FP)
  exact mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) (appendFn_mem_FP hA (mem_FP_comp hs pairSnd_mem_FP))

theorem source_evaluator {P : Inputs} (h : P.PolyTime) : SpaceFunction (source P) := by
  have E := record_evaluator h
  have A := E.precompose firstQuery firstQuery_FP
  have B := E.precompose secondQuery secondQuery_FP
  have C := E.precompose thirdQuery thirdQuery_FP
  have H := (A.pairOutputs (B.pairOutputs C)).withInput.postcompose finish finish_FP
  exact H.congr (funext fun q => by simp only [source, finish, Function.comp_apply, pairFst_pair, pairSnd_pair])

noncomputable def moment (P : Inputs) (q : List Bool) : ℤ := BoundedCriticalSampleChildRecords.moment P (source P q)
theorem evaluator {P : Inputs} (h : P.PolyTime) :
    SpaceFunction (fun q => SignStatisticBits.integerCode (moment P q)) :=
  (source_evaluator h).chain (BoundedCriticalSampleChildRecords.evaluator h)

theorem selected_value (P : Inputs) (c : List Bool) (r : Fin (BoundedCriticalSampleChildRegularCount.count P c))
    (x : BoundedCriticalSampleChildRecordSpan.Root P c) :
    SparseFeatureRecords.value (Nat.succ_pos _) (BoundedCriticalSampleChildRecords.slots P c)
      (BoundedCriticalSampleChildRecords.width P c)
      (fun i => (BoundedCriticalSampleChildThom.signature P c x i : ℚ)) (BoundedCriticalSampleChildRootHash.record P c r) =
        selected P c r x := by
  rw [selected, Matrix.row, BoundedCriticalSampleChildRecordSpan.matrix, Matrix.of_apply, BoundedCriticalSampleChildRecordSpan.row_apply]
  rfl

theorem moment_packet (P : Inputs) (c : List Bool)
    (i j k : Fin (BoundedCriticalSampleChildRegularCount.count P c)) :
    (moment P (pair c (pair (BinaryNatCode.encode i.val)
      (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode k.val)))) : ℚ) =
      ∑ x : BoundedCriticalSampleChildRecordSpan.Root P c, selected P c i x * selected P c j x * selected P c k x := by
  let a := BoundedCriticalSampleChildRootHash.record P c i
  let b := BoundedCriticalSampleChildRootHash.record P c j
  let d := BoundedCriticalSampleChildRootHash.record P c k
  have ha : a.length = BoundedCriticalSampleChildRecords.length P c := ImplicitGraph.length_word _ _
  have hb : b.length = BoundedCriticalSampleChildRecords.length P c := ImplicitGraph.length_word _ _
  have hd : d.length = BoundedCriticalSampleChildRecords.length P c := ImplicitGraph.length_word _ _
  have hs : source P (pair c (pair (BinaryNatCode.encode i.val)
      (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode k.val)))) = pair c ((a ++ b) ++ d) := by
    simp only [source, firstQuery, secondQuery, thirdQuery, pairFst_pair, pairSnd_pair, record_packet]
    rfl
  rw [moment, hs, BoundedCriticalSampleChildRecordSpan.moment_eq_sum_values]
  have hc : BoundedCriticalSampleChildRecords.recordSlots P (pair c ((a ++ b) ++ d)) =
      (BoundedCriticalSampleChildRecords.slots P c + BoundedCriticalSampleChildRecords.slots P c) + BoundedCriticalSampleChildRecords.slots P c := by
    simp only [BoundedCriticalSampleChildRecords.recordSlots, pairFst_pair, pairSnd_pair, List.length_append,
      ha, hb, hd, BoundedCriticalSampleChildRecords.length]
    rw [← Nat.add_mul, ← Nat.add_mul, Nat.mul_div_cancel _ (BoundedCriticalSampleChildRecords.width_pos P c)]
  rw [hc]
  have hab : (a ++ b).length = (BoundedCriticalSampleChildRecords.slots P c + BoundedCriticalSampleChildRecords.slots P c) *
      BoundedCriticalSampleChildRecords.width P c := by rw [List.length_append, ha, hb, BoundedCriticalSampleChildRecords.length, Nat.add_mul]
  have ha' : a.length = BoundedCriticalSampleChildRecords.slots P c * BoundedCriticalSampleChildRecords.width P c := by
    simpa only [BoundedCriticalSampleChildRecords.length] using ha
  apply Finset.sum_congr rfl
  intro x _
  rw [SparseFeatureRecords.value_append _ _ _ _ _ (a ++ b) d hab,
    SparseFeatureRecords.value_append _ _ _ _ _ a b ha']
  rw [selected_value, selected_value, selected_value]

theorem raw_moment_bound (P : Inputs) (z : List Bool) :
    (BoundedCriticalSampleChildRecords.moment P z).natAbs ≤ 2 ^ BoundedCriticalSampleChildThom.labelWidth P (pairFst z) := by
  exact BoundedCriticalSampleChildRecords.moment_bound P z

theorem moment_bound (P : Inputs) (q : List Bool) :
    (moment P q).natAbs ≤ 2 ^ BoundedCriticalSampleChildThom.labelWidth P (pairFst q) := by
  have H := raw_moment_bound P (source P q)
  simpa only [moment, source, pairFst_pair] using H

end LeanCanny.Encoding.BoundedCriticalSampleChildBasisMoments
