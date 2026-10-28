/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedFullSampleChildRankChoice
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty

/-! # A basis selected by native prefix-rank queries

There is exactly one rank-increasing row for each rank number. Rows skipped
by the search belong to the previous prefix span. Thus the selected rows
span all rational functions on the regular child roots, and their
cardinality makes them a basis. Selection retains only a binary row index.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedFullSampleChildRankBasis
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open BoundedFullSampleChildPrefixRank BoundedFullSampleChildRankChoice Submodule
open BoundedFullSampleChildSource (Inputs)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedFullSampleChildRecords.length BoundedFullSampleChildThom.labelWidth
  BoundedFullSampleChildCoordinates.parameterDegree BoundedFullSampleChildCoordinates.baseHeight
  BoundedFullSampleChildQueries.roots BoundedFullSampleChildRegularCount.count

noncomputable def chosen (P : Inputs) (c : List Bool) (r : ℕ) : ℕ :=
  index P (pair c (BinaryNatCode.encode r))

theorem chosen_spec (P : Inputs) (c : List Bool) (r : ℕ)
    (hr : r < BoundedFullSampleChildRegularCount.count P c) :
    chosen P c r < 2 ^ BoundedFullSampleChildRecords.length P c ∧
      prefixRank P c (chosen P c r) = r ∧
      prefixRank P c (chosen P c r) < prefixRank P c (chosen P c r + 1) := by
  simpa only [chosen, dimension, pairFst_pair, pairSnd_pair, BinaryNatCode.encode,
    Nat.fromBitsLE_bits] using index_spec P (pair c (BinaryNatCode.encode r)) (by
      simpa only [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits] using hr)

theorem gain_unique (P : Inputs) (c : List Bool) {i j : ℕ}
    (he : prefixRank P c i = prefixRank P c j)
    (hi : prefixRank P c i < prefixRank P c (i + 1))
    (hj : prefixRank P c j < prefixRank P c (j + 1)) : i = j := by
  by_contra hn
  rcases lt_or_gt_of_ne hn with hij | hji
  · have h := prefixRank_mono P c (show i + 1 ≤ j by omega)
    omega
  · have h := prefixRank_mono P c (show j + 1 ≤ i by omega)
    omega

theorem chosen_of_gain (P : Inputs) (c : List Bool) (k : ℕ)
    (hk : k < 2 ^ BoundedFullSampleChildRecords.length P c)
    (hg : prefixRank P c k < prefixRank P c (k + 1)) :
    chosen P c (prefixRank P c k) = k := by
  have hle := prefixRank_mono P c (show k + 1 ≤ 2 ^ BoundedFullSampleChildRecords.length P c by omega)
  rw [prefixRank_full P c _ le_rfl] at hle
  have hr : prefixRank P c k < BoundedFullSampleChildRegularCount.count P c := hg.trans_le hle
  obtain ⟨_, he, hi⟩ := chosen_spec P c (prefixRank P c k) hr
  exact gain_unique P c he hi hg

noncomputable def selectedIndex (P : Inputs) (c : List Bool)
    (r : Fin (BoundedFullSampleChildRegularCount.count P c)) : BoundedFullSampleChildRecordSpan.Index P c :=
  ⟨chosen P c r.val, (chosen_spec P c r.val r.isLt).1⟩

noncomputable def selected (P : Inputs) (c : List Bool)
    (r : Fin (BoundedFullSampleChildRegularCount.count P c)) : BoundedFullSampleChildRecordSpan.Root P c → ℚ :=
  (BoundedFullSampleChildRecordSpan.matrix P c).row (selectedIndex P c r)

noncomputable def prefixSpan (P : Inputs) (c : List Bool) (k : ℕ) :=
  span ℚ (Set.range (prefixRows P c k).row)

theorem prefixSpan_mono (P : Inputs) (c : List Bool) : Monotone (prefixSpan P c) := by
  intro k l hkl
  apply span_le.mpr
  rintro _ ⟨i, rfl⟩
  by_cases hi : i.val < k
  · have he : (prefixRows P c k).row i = (prefixRows P c l).row i := by
      ext x
      simp only [Matrix.row, prefixRows, Matrix.of_apply, hi, hi.trans_le hkl, ite_true]
    rw [he]
    exact subset_span ⟨i, rfl⟩
  · have he : (prefixRows P c k).row i = 0 := by
      ext x
      simp only [Matrix.row, prefixRows, Matrix.of_apply, hi, ite_false, Pi.zero_apply]
    rw [he]
    exact zero_mem _

theorem skipped_mem (P : Inputs) (c : List Bool) (i : BoundedFullSampleChildRecordSpan.Index P c)
    (hg : ¬ prefixRank P c i.val < prefixRank P c (i.val + 1)) :
    (BoundedFullSampleChildRecordSpan.matrix P c).row i ∈ prefixSpan P c i.val := by
  have hle := prefixRank_mono P c (Nat.le_succ i.val)
  have he : prefixSpan P c i.val = prefixSpan P c (i.val + 1) := by
    apply Submodule.eq_of_le_of_finrank_eq (prefixSpan_mono P c (Nat.le_succ i.val))
    unfold prefixSpan
    rw [← prefixRank_eq_span, ← prefixRank_eq_span]
    exact hle.antisymm (Nat.le_of_not_gt hg)
  rw [he]
  have hrow : (BoundedFullSampleChildRecordSpan.matrix P c).row i = (prefixRows P c (i.val + 1)).row i := by
    ext x
    simp only [Matrix.row, prefixRows, Matrix.of_apply, Nat.lt_succ_self, ite_true]
  rw [hrow]
  exact subset_span ⟨i, rfl⟩

theorem selected_mem_of_gain (P : Inputs) (c : List Bool) (i : BoundedFullSampleChildRecordSpan.Index P c)
    (hg : prefixRank P c i.val < prefixRank P c (i.val + 1)) :
    (BoundedFullSampleChildRecordSpan.matrix P c).row i ∈ span ℚ (Set.range (selected P c)) := by
  have hle := prefixRank_mono P c (show i.val + 1 ≤ 2 ^ BoundedFullSampleChildRecords.length P c by omega)
  rw [prefixRank_full P c _ le_rfl] at hle
  let r : Fin (BoundedFullSampleChildRegularCount.count P c) := ⟨prefixRank P c i.val, hg.trans_le hle⟩
  have he : selectedIndex P c r = i := Fin.ext (chosen_of_gain P c i.val i.isLt hg)
  apply subset_span
  exact ⟨r, by rw [selected, he]⟩

theorem prefixSpan_le_selected (P : Inputs) (c : List Bool) (k : ℕ) :
    prefixSpan P c k ≤ span ℚ (Set.range (selected P c)) := by
  induction k with
  | zero =>
    apply span_le.mpr
    rintro _ ⟨i, rfl⟩
    have he : (prefixRows P c 0).row i = 0 := by ext x; simp [Matrix.row, prefixRows]
    rw [he]
    exact zero_mem _
  | succ k ih =>
    apply span_le.mpr
    rintro _ ⟨i, rfl⟩
    by_cases hi : i.val < k
    · have he : (prefixRows P c (k + 1)).row i = (prefixRows P c k).row i := by
        ext x
        simp only [Matrix.row, prefixRows, Matrix.of_apply, hi, hi.trans (Nat.lt_succ_self k), ite_true]
      rw [he]
      exact ih (subset_span ⟨i, rfl⟩)
    · by_cases he : i.val = k
      · have hrow : (prefixRows P c (k + 1)).row i = (BoundedFullSampleChildRecordSpan.matrix P c).row i := by
          ext x
          simp only [Matrix.row, prefixRows, Matrix.of_apply, he, Nat.lt_succ_self, ite_true]
        rw [hrow]
        by_cases hg : prefixRank P c i.val < prefixRank P c (i.val + 1)
        · exact selected_mem_of_gain P c i hg
        · have hm := skipped_mem P c i hg
          rw [he] at hm
          exact ih hm
      · have hn : ¬ i.val < k + 1 := by omega
        have hrow : (prefixRows P c (k + 1)).row i = 0 := by
          ext x
          simp only [Matrix.row, prefixRows, Matrix.of_apply, hn, ite_false, Pi.zero_apply]
        rw [hrow]
        exact zero_mem _

theorem span_selected (P : Inputs) (c : List Bool) : span ℚ (Set.range (selected P c)) = ⊤ := by
  apply top_unique
  rw [← BoundedFullSampleChildRecordSpan.span_matrix_rows P c]
  apply span_le.mpr
  rintro _ ⟨i, rfl⟩
  apply prefixSpan_le_selected P c (i.val + 1)
  have he : (BoundedFullSampleChildRecordSpan.matrix P c).row i = (prefixRows P c (i.val + 1)).row i := by
    ext x
    simp only [Matrix.row, prefixRows, Matrix.of_apply, Nat.lt_succ_self, ite_true]
  rw [he]
  exact subset_span ⟨i, rfl⟩

theorem independent (P : Inputs) (c : List Bool) : LinearIndependent ℚ (selected P c) := by
  apply linearIndependent_of_top_le_span_of_card_eq_finrank
  · rw [span_selected]
  · rw [Fintype.card_fin, Module.finrank_fintype_fun_eq_card]
    rw [Fintype.card_coe]
    exact (BoundedFullSampleChildQueries.roots_card P c).symm

noncomputable def basis (P : Inputs) (c : List Bool) :
    Module.Basis (Fin (BoundedFullSampleChildRegularCount.count P c)) ℚ (BoundedFullSampleChildRecordSpan.Root P c → ℚ) :=
  Module.Basis.mk (independent P c) (by rw [span_selected])

@[simp] theorem basis_apply (P : Inputs) (c : List Bool) (r : Fin (BoundedFullSampleChildRegularCount.count P c)) :
    basis P c r = selected P c r := Module.Basis.mk_apply _ _ _

theorem selected_separates (P : Inputs) (c : List Bool) {x y : BoundedFullSampleChildRecordSpan.Root P c}
    (h : ∀ r, selected P c r x = selected P c r y) : x = y := by
  have he : (LinearMap.proj x : (BoundedFullSampleChildRecordSpan.Root P c → ℚ) →ₗ[ℚ] ℚ) =
      LinearMap.proj y := (basis P c).ext (by
        intro r
        change (basis P c r) x = (basis P c r) y
        rw [basis_apply]
        exact h r)
  by_contra hxy
  have hc := LinearMap.congr_fun he (fun z => if z = x then (1 : ℚ) else 0)
  simp [Ne.symm hxy] at hc

/-- Read one selected short record; no basis table is retained. -/
noncomputable def record (P : Inputs) (q : List Bool) : List Bool :=
  ImplicitGraph.word (BoundedFullSampleChildRecords.length P (pairFst q)) (index P q)

noncomputable def recordFinish (P : Inputs) (z : List Bool) : List Bool :=
  ImplicitGraph.word (BoundedFullSampleChildRecords.length P (pairFst (pairFst z))) (Nat.fromBitsLE (pairSnd z))

theorem recordFinish_FP {P : Inputs} (h : P.PolyTime) : recordFinish P ∈ FP :=
  ImplicitGraph.word_computable ((BoundedFullSampleChildRecords.length_unary h).comp
    (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)) (BinaryFn.fromBits pairSnd_mem_FP)

theorem record_evaluator {P : Inputs} (h : P.PolyTime) : SpaceFunction (record P) := by
  have E := (BoundedFullSampleChildRankChoice.evaluator h).withInput.postcompose (recordFinish P) (recordFinish_FP h)
  exact E.congr (funext fun q => by simp only [record, recordFinish, Function.comp_apply,
    pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits])

theorem record_length (P : Inputs) (q : List Bool) :
    (record P q).length = BoundedFullSampleChildRecords.length P (pairFst q) := ImplicitGraph.length_word _ _

theorem record_packet (P : Inputs) (c : List Bool) (r : ℕ) :
    record P (pair c (BinaryNatCode.encode r)) =
      ImplicitGraph.word (BoundedFullSampleChildRecords.length P c) (chosen P c r) := by
  simp only [record, chosen, pairFst_pair]

theorem record_selected (P : Inputs) (c : List Bool) (r : Fin (BoundedFullSampleChildRegularCount.count P c)) :
    BoundedFullSampleChildRecordSpan.row P c (record P (pair c (BinaryNatCode.encode r.val))) = selected P c r := by
  rw [record_packet]
  rfl

end LeanCanny.Encoding.BoundedFullSampleChildRankBasis
