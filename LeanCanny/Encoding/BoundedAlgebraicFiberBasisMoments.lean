/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicFiberRootHash

/-! # Native triple moments of the selected fiber-sign basis

The selected record reader recomputes its row index using native prefix
ranks. Concatenating three such records feeds the original Tarski reader.
Thus triple products need no basis table or supplied moment oracle.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicFiberBasisMoments
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open BoundedAlgebraicSlice BoundedAlgebraicFiberRankBasis
open scoped Classical BigOperators

noncomputable def record (P : Readers) (F : Family) : List Bool → List Bool := BoundedAlgebraicFiberRankBasis.record P F

theorem record_evaluator {P : Readers} (h : P.PolyTime) {F : Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (record P F) :=
  BoundedAlgebraicFiberRankBasis.record_evaluator h A ha

theorem record_packet (P : Readers) (F : Family) (c : List Bool) (r : Fin (RootCount.count P F c)) :
    record P F (pair c (BinaryNatCode.encode r.val)) = BoundedAlgebraicFiberRootHash.record P F c r := by
  simp only [record, BoundedAlgebraicFiberRankBasis.record, pairFst_pair, BoundedAlgebraicFiberRootHash.record, chosen]

theorem record_length (P : Readers) (F : Family) (q : List Bool) :
    (record P F q).length = BoundedAlgebraicFiberRecords.length F (pairFst (pairFst q)) :=
  BoundedAlgebraicFiberRankBasis.record_length P F q

def firstQuery (q : List Bool) : List Bool := pair (pairFst q) (pairFst (pairSnd q))
def secondQuery (q : List Bool) : List Bool := pair (pairFst q) (pairFst (pairSnd (pairSnd q)))
def thirdQuery (q : List Bool) : List Bool := pair (pairFst q) (pairSnd (pairSnd (pairSnd q)))
theorem firstQuery_FP : firstQuery ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
theorem secondQuery_FP : secondQuery ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairFst_mem_FP)
theorem thirdQuery_FP : thirdQuery ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairSnd_mem_FP)

noncomputable def source (P : Readers) (F : Family) (q : List Bool) : List Bool := pair (pairFst q)
  ((record P F (firstQuery q) ++ record P F (secondQuery q)) ++ record P F (thirdQuery q))

def finish (z : List Bool) : List Bool := pair (pairFst (pairFst z))
  ((pairFst (pairSnd z) ++ pairFst (pairSnd (pairSnd z))) ++ pairSnd (pairSnd (pairSnd z)))
theorem finish_FP : finish ∈ FP := by
  have hs := mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP
  have hA := appendFn_mem_FP (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) (mem_FP_comp hs pairFst_mem_FP)
  exact mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) (appendFn_mem_FP hA (mem_FP_comp hs pairSnd_mem_FP))

theorem source_evaluator {P : Readers} (h : P.PolyTime) {F : Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (source P F) := by
  have E := record_evaluator h A ha
  have L := E.precompose firstQuery firstQuery_FP
  have R := E.precompose secondQuery secondQuery_FP
  have T := E.precompose thirdQuery thirdQuery_FP
  have H := (L.pairOutputs (R.pairOutputs T)).withInput.postcompose finish finish_FP
  exact H.congr (funext fun q => by simp only [source, finish, Function.comp_apply, pairFst_pair, pairSnd_pair])

noncomputable def moment (P : Readers) (F : Family) (q : List Bool) : ℤ := BoundedAlgebraicFiberRecordMoments.moment P F (source P F q)
theorem evaluator {P : Readers} (h : P.PolyTime) {F : Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun q => SignStatisticBits.integerCode (moment P F q)) :=
  (source_evaluator h A ha).chain (BoundedAlgebraicFiberRecordMoments.evaluator h A ha)

theorem selected_value (P : Readers) (F : Family) (c : List Bool) (r : Fin (RootCount.count P F c))
    (x : BoundedAlgebraicFiberRecordSpan.Root P F c) :
    SparseFeatureRecords.value (Nat.succ_pos _) (BoundedAlgebraicFiberRecords.slots F (pairFst c))
      (BoundedAlgebraicFiberRecords.width F (pairFst c))
      (fun i => (BoundedAlgebraicFiberThom.signature P F c x i : ℚ)) (BoundedAlgebraicFiberRootHash.record P F c r) =
        selected P F c r x := by
  rw [selected, Matrix.row, BoundedAlgebraicFiberRecordSpan.matrix, BoundedAlgebraicFiberRecordSpan.row_apply]
  rfl

theorem moment_packet (P : Readers) (F : Family) (c : List Bool)
    (i j k : Fin (RootCount.count P F c)) :
    (moment P F (pair c (pair (BinaryNatCode.encode i.val)
      (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode k.val)))) : ℚ) =
      ∑ x : BoundedAlgebraicFiberRecordSpan.Root P F c, selected P F c i x * selected P F c j x * selected P F c k x := by
  let a := BoundedAlgebraicFiberRootHash.record P F c i
  let b := BoundedAlgebraicFiberRootHash.record P F c j
  let d := BoundedAlgebraicFiberRootHash.record P F c k
  have ha : a.length = BoundedAlgebraicFiberRecords.length F (pairFst c) := ImplicitGraph.length_word _ _
  have hb : b.length = BoundedAlgebraicFiberRecords.length F (pairFst c) := ImplicitGraph.length_word _ _
  have hd : d.length = BoundedAlgebraicFiberRecords.length F (pairFst c) := ImplicitGraph.length_word _ _
  have hs : source P F (pair c (pair (BinaryNatCode.encode i.val)
      (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode k.val)))) = pair c ((a ++ b) ++ d) := by
    simp only [source, firstQuery, secondQuery, thirdQuery, pairFst_pair, pairSnd_pair, record_packet]
    rfl
  rw [moment, hs, BoundedAlgebraicFiberRecordMoments.moment_eq_sum_values]
  have hc : BoundedAlgebraicFiberRecords.recordSlots F (pair (pairFst c) ((a ++ b) ++ d)) =
      (BoundedAlgebraicFiberRecords.slots F (pairFst c) + BoundedAlgebraicFiberRecords.slots F (pairFst c)) + BoundedAlgebraicFiberRecords.slots F (pairFst c) := by
    simp only [BoundedAlgebraicFiberRecords.recordSlots, pairFst_pair, pairSnd_pair, List.length_append,
      ha, hb, hd, BoundedAlgebraicFiberRecords.length]
    rw [← Nat.add_mul, ← Nat.add_mul, Nat.mul_div_cancel _ (BoundedAlgebraicFiberRecords.width_pos F (pairFst c))]
  rw [hc]
  have hab : (a ++ b).length = (BoundedAlgebraicFiberRecords.slots F (pairFst c) + BoundedAlgebraicFiberRecords.slots F (pairFst c)) *
      BoundedAlgebraicFiberRecords.width F (pairFst c) := by rw [List.length_append, ha, hb, BoundedAlgebraicFiberRecords.length, Nat.add_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [SparseFeatureRecords.value_append _ _ _ _ _ (a ++ b) d hab,
    SparseFeatureRecords.value_append _ _ _ _ _ a b ha]
  rw [selected_value, selected_value, selected_value]

theorem raw_moment_bound (P : Readers) (F : Family) (z : List Bool) :
    (BoundedAlgebraicFiberRecordMoments.moment P F z).natAbs ≤ F.degree (pairFst (pairFst z)) :=
  BoundedAlgebraicFiberRecordMoments.moment_bound P F z

theorem moment_bound (P : Readers) (F : Family) (q : List Bool) :
    (moment P F q).natAbs ≤ F.degree (pairFst (pairFst q)) := by
  have H := raw_moment_bound P F (source P F q)
  simpa only [moment, source, pairFst_pair] using H

end LeanCanny.Encoding.BoundedAlgebraicFiberBasisMoments
