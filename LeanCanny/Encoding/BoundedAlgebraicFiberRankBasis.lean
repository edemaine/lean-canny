/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicFiberRankChoice
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-! # A basis selected by native prefix-rank queries

There is exactly one rank-increasing row for each rank number. Rows skipped
by the search belong to the previous prefix span. Thus the selected rows
span all rational functions on the distinct fiber roots, and their
cardinality makes them a basis. Selection retains only a binary row index.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicFiberRankBasis
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open BoundedAlgebraicSlice BoundedAlgebraicFiberPrefixRank BoundedAlgebraicFiberRankChoice Submodule
open scoped Classical

noncomputable def chosen (P : Readers) (F : Family) (c : List Bool) (r : ℕ) : ℕ :=
  index P F (pair c (BinaryNatCode.encode r))

theorem chosen_spec (P : Readers) (F : Family) (c : List Bool) (r : ℕ)
    (hr : r < RootCount.count P F c) :
    chosen P F c r < 2 ^ BoundedAlgebraicFiberRecords.length F (pairFst c) ∧
      prefixRank P F c (chosen P F c r) = r ∧
      prefixRank P F c (chosen P F c r) < prefixRank P F c (chosen P F c r + 1) := by
  simpa only [chosen, dimension, pairFst_pair, pairSnd_pair, BinaryNatCode.encode,
    Nat.fromBitsLE_bits] using index_spec P F (pair c (BinaryNatCode.encode r)) (by
      simpa only [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits] using hr)

theorem gain_unique (P : Readers) (F : Family) (c : List Bool) {i j : ℕ}
    (he : prefixRank P F c i = prefixRank P F c j)
    (hi : prefixRank P F c i < prefixRank P F c (i + 1))
    (hj : prefixRank P F c j < prefixRank P F c (j + 1)) : i = j := by
  by_contra hn
  rcases lt_or_gt_of_ne hn with hij | hji
  · have h := prefixRank_mono P F c (show i + 1 ≤ j by omega)
    omega
  · have h := prefixRank_mono P F c (show j + 1 ≤ i by omega)
    omega

theorem chosen_of_gain (P : Readers) (F : Family) (c : List Bool) (k : ℕ)
    (hk : k < 2 ^ BoundedAlgebraicFiberRecords.length F (pairFst c))
    (hg : prefixRank P F c k < prefixRank P F c (k + 1)) :
    chosen P F c (prefixRank P F c k) = k := by
  have hle := prefixRank_mono P F c (show k + 1 ≤ 2 ^ BoundedAlgebraicFiberRecords.length F (pairFst c) by omega)
  rw [prefixRank_full P F c _ le_rfl] at hle
  have hr : prefixRank P F c k < RootCount.count P F c := hg.trans_le hle
  obtain ⟨_, he, hi⟩ := chosen_spec P F c (prefixRank P F c k) hr
  exact gain_unique P F c he hi hg

noncomputable def selectedIndex (P : Readers) (F : Family) (c : List Bool)
    (r : Fin (RootCount.count P F c)) : BoundedAlgebraicFiberRecordSpan.Index F c :=
  ⟨chosen P F c r.val, (chosen_spec P F c r.val r.isLt).1⟩

noncomputable def selected (P : Readers) (F : Family) (c : List Bool)
    (r : Fin (RootCount.count P F c)) : BoundedAlgebraicFiberRecordSpan.Root P F c → ℚ :=
  (BoundedAlgebraicFiberRecordSpan.matrix P F c).row (selectedIndex P F c r)

noncomputable def prefixSpan (P : Readers) (F : Family) (c : List Bool) (k : ℕ) :=
  span ℚ (Set.range (prefixRows P F c k).row)

theorem prefixSpan_mono (P : Readers) (F : Family) (c : List Bool) : Monotone (prefixSpan P F c) := by
  intro k l hkl
  apply span_le.mpr
  rintro _ ⟨i, rfl⟩
  by_cases hi : i.val < k
  · have he : (prefixRows P F c k).row i = (prefixRows P F c l).row i := by
      ext x
      simp only [Matrix.row, prefixRows, hi, hi.trans_le hkl, ite_true]
    rw [he]
    exact subset_span ⟨i, rfl⟩
  · have he : (prefixRows P F c k).row i = 0 := by
      ext x
      simp only [Matrix.row, prefixRows, hi, ite_false, Pi.zero_apply]
    rw [he]
    exact zero_mem _

theorem skipped_mem (P : Readers) (F : Family) (c : List Bool) (i : BoundedAlgebraicFiberRecordSpan.Index F c)
    (hg : ¬ prefixRank P F c i.val < prefixRank P F c (i.val + 1)) :
    (BoundedAlgebraicFiberRecordSpan.matrix P F c).row i ∈ prefixSpan P F c i.val := by
  have hle := prefixRank_mono P F c (Nat.le_succ i.val)
  have he : prefixSpan P F c i.val = prefixSpan P F c (i.val + 1) := by
    apply Submodule.eq_of_le_of_finrank_eq (prefixSpan_mono P F c (Nat.le_succ i.val))
    unfold prefixSpan
    rw [← prefixRank_eq_span, ← prefixRank_eq_span]
    exact hle.antisymm (Nat.le_of_not_gt hg)
  rw [he]
  have hrow : (BoundedAlgebraicFiberRecordSpan.matrix P F c).row i = (prefixRows P F c (i.val + 1)).row i := by
    ext x
    simp only [Matrix.row, prefixRows, Nat.lt_succ_self, ite_true]
  rw [hrow]
  exact subset_span ⟨i, rfl⟩

theorem selected_mem_of_gain (P : Readers) (F : Family) (c : List Bool) (i : BoundedAlgebraicFiberRecordSpan.Index F c)
    (hg : prefixRank P F c i.val < prefixRank P F c (i.val + 1)) :
    (BoundedAlgebraicFiberRecordSpan.matrix P F c).row i ∈ span ℚ (Set.range (selected P F c)) := by
  have hle := prefixRank_mono P F c (show i.val + 1 ≤ 2 ^ BoundedAlgebraicFiberRecords.length F (pairFst c) by omega)
  rw [prefixRank_full P F c _ le_rfl] at hle
  let r : Fin (RootCount.count P F c) := ⟨prefixRank P F c i.val, hg.trans_le hle⟩
  have he : selectedIndex P F c r = i := Fin.ext (chosen_of_gain P F c i.val i.isLt hg)
  apply subset_span
  exact ⟨r, by rw [selected, he]⟩

theorem prefixSpan_le_selected (P : Readers) (F : Family) (c : List Bool) (k : ℕ) :
    prefixSpan P F c k ≤ span ℚ (Set.range (selected P F c)) := by
  induction k with
  | zero =>
    apply span_le.mpr
    rintro _ ⟨i, rfl⟩
    have he : (prefixRows P F c 0).row i = 0 := by ext x; simp [Matrix.row, prefixRows]
    rw [he]
    exact zero_mem _
  | succ k ih =>
    apply span_le.mpr
    rintro _ ⟨i, rfl⟩
    by_cases hi : i.val < k
    · have he : (prefixRows P F c (k + 1)).row i = (prefixRows P F c k).row i := by
        ext x
        simp only [Matrix.row, prefixRows, hi, hi.trans (Nat.lt_succ_self k), ite_true]
      rw [he]
      exact ih (subset_span ⟨i, rfl⟩)
    · by_cases he : i.val = k
      · have hrow : (prefixRows P F c (k + 1)).row i = (BoundedAlgebraicFiberRecordSpan.matrix P F c).row i := by
          ext x
          simp only [Matrix.row, prefixRows, he, Nat.lt_succ_self, ite_true]
        rw [hrow]
        by_cases hg : prefixRank P F c i.val < prefixRank P F c (i.val + 1)
        · exact selected_mem_of_gain P F c i hg
        · have hm := skipped_mem P F c i hg
          rw [he] at hm
          exact ih hm
      · have hn : ¬ i.val < k + 1 := by omega
        have hrow : (prefixRows P F c (k + 1)).row i = 0 := by
          ext x
          simp only [Matrix.row, prefixRows, hn, ite_false, Pi.zero_apply]
        rw [hrow]
        exact zero_mem _

theorem span_selected (P : Readers) (F : Family) (c : List Bool) : span ℚ (Set.range (selected P F c)) = ⊤ := by
  apply top_unique
  rw [← BoundedAlgebraicFiberRecordSpan.span_matrix_rows P F c]
  apply span_le.mpr
  rintro _ ⟨i, rfl⟩
  apply prefixSpan_le_selected P F c (i.val + 1)
  have he : (BoundedAlgebraicFiberRecordSpan.matrix P F c).row i = (prefixRows P F c (i.val + 1)).row i := by
    ext x
    simp only [Matrix.row, prefixRows, Nat.lt_succ_self, ite_true]
  rw [he]
  exact subset_span ⟨i, rfl⟩

theorem independent (P : Readers) (F : Family) (c : List Bool) : LinearIndependent ℚ (selected P F c) := by
  apply linearIndependent_of_top_le_span_of_card_eq_finrank
  · rw [span_selected]
  · rw [Fintype.card_fin, Module.finrank_fintype_fun_eq_card]
    exact (Fintype.card_coe _).symm

noncomputable def basis (P : Readers) (F : Family) (c : List Bool) :
    Module.Basis (Fin (RootCount.count P F c)) ℚ (BoundedAlgebraicFiberRecordSpan.Root P F c → ℚ) :=
  Module.Basis.mk (independent P F c) (by rw [span_selected])

@[simp] theorem basis_apply (P : Readers) (F : Family) (c : List Bool) (r : Fin (RootCount.count P F c)) :
    basis P F c r = selected P F c r := Module.Basis.mk_apply _ _ _

theorem selected_separates (P : Readers) (F : Family) (c : List Bool) {x y : BoundedAlgebraicFiberRecordSpan.Root P F c}
    (h : ∀ r, selected P F c r x = selected P F c r y) : x = y := by
  have he : (LinearMap.proj x : (BoundedAlgebraicFiberRecordSpan.Root P F c → ℚ) →ₗ[ℚ] ℚ) =
      LinearMap.proj y := (basis P F c).ext (by
        intro r
        change (basis P F c r) x = (basis P F c r) y
        rw [basis_apply]
        exact h r)
  by_contra hxy
  have hc := LinearMap.congr_fun he (fun z => if z = x then (1 : ℚ) else 0)
  simp [Ne.symm hxy] at hc

noncomputable def record (P : Readers) (F : Family) (q : List Bool) : List Bool :=
  ImplicitGraph.word (BoundedAlgebraicFiberRecords.length F (pairFst (pairFst q)))
    (BoundedAlgebraicFiberRankChoice.index P F q)

noncomputable def recordFinish (F : Family) (z : List Bool) : List Bool :=
  ImplicitGraph.word (BoundedAlgebraicFiberRecords.length F (pairFst (pairFst (pairFst z)))) (Nat.fromBitsLE (pairSnd z))

theorem recordFinish_FP {F : Family} (A : F.Access) : recordFinish F ∈ FP := by
  have hf2 := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hf3 : (fun z => pairFst (pairFst (pairFst z))) ∈ FP :=
    mem_FP_comp (f := fun z => pairFst (pairFst z)) (g := pairFst) hf2 pairFst_mem_FP
  have hw := (BoundedAlgebraicFiberRecords.length_unary A).comp hf3
  exact ImplicitGraph.word_computable hw (BinaryFn.fromBits pairSnd_mem_FP)

theorem record_evaluator {P : Readers} (h : P.PolyTime) {F : Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (record P F) := by
  have E := (BoundedAlgebraicFiberRankChoice.evaluator h A ha).withInput.postcompose (recordFinish F) (recordFinish_FP A)
  exact E.congr (funext fun q => by simp only [record, recordFinish, Function.comp_apply, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits])

theorem record_packet (P : Readers) (F : Family) (u : List Bool) (r : Fin (RootCount.count P F u)) :
    record P F (pair u (BinaryNatCode.encode r.val)) =
      ImplicitGraph.word (BoundedAlgebraicFiberRecords.length F (pairFst u)) (selectedIndex P F u r).val := by
  simp only [record, pairFst_pair, selectedIndex, chosen]

theorem record_length (P : Readers) (F : Family) (q : List Bool) :
    (record P F q).length = BoundedAlgebraicFiberRecords.length F (pairFst (pairFst q)) := ImplicitGraph.length_word _ _

theorem record_row (P : Readers) (F : Family) (u : List Bool) (r : Fin (RootCount.count P F u)) :
    BoundedAlgebraicFiberRecordSpan.row P F u (record P F (pair u (BinaryNatCode.encode r.val))) = selected P F u r := by
  rw [record_packet, selected]
  rfl

end LeanCanny.Encoding.BoundedAlgebraicFiberRankBasis
