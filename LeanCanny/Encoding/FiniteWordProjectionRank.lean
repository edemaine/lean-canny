/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BinaryFlagCountSpace
public import LeanCanny.Geometry.FiniteImageRank
public import LeanCanny.Computation.SpaceFunctionBinaryQuantifiers
public import LeanCanny.Computation.PSPACEClosure

/-! # Native distinct projection ranks on finite word sets

Native equality rejects invalid labels. A least-word scan selects one label
per projected value; a binary count then counts the values below the target.
Only the width is unary. Labels, indices, and accumulated counts stay binary.
-/

@[expose] public section
namespace LeanCanny.Encoding.FiniteWordProjectionRank
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

structure Data where
  width : List Bool → ℕ
  valid : Language
  value : List Bool → List Bool → ℝ
  equal : Language
  less : Language
  valid_length : ∀ c w, pair c w ∈ valid → w.length = width c
  equal_iff : ∀ c w v, pair c (pair w v) ∈ equal ↔
    pair c w ∈ valid ∧ pair c v ∈ valid ∧ value c w = value c v
  less_iff : ∀ c w v, pair c (pair w v) ∈ less ↔
    pair c w ∈ valid ∧ pair c v ∈ valid ∧ value c w < value c v

structure Data.Access (D : Data) : Prop where
  width : UnaryFn D.width
  valid : SpaceDecider D.valid
  equal : SpaceDecider D.equal
  less : SpaceDecider D.less

def word (D : Data) (c : List Bool) (k : ℕ) : List Bool := ImplicitGraph.word (D.width c) k

theorem word_value (D : Data) (c : List Bool) (k : ℕ) (hk : k < 2 ^ D.width c) : Nat.fromBitsLE (word D c k) = k := by
  have H := FixedWidthNatVector.decode_block 1 (D.width c) (fun _ => k) 0 (by decide) hk
  have hl : (FixedWidthNatVector.encode 1 (D.width c) (fun _ => k)).length ≤ D.width c := by simp
  simpa only [word, ImplicitGraph.word, Nat.zero_mul, List.drop_zero, List.take_of_length_le hl] using H

def candidate (D : Data) (r : List Bool) : List Bool := word D (pairFst (pairFst r)) (Nat.fromBitsLE (pairSnd r))

theorem candidate_FP {D : Data} (A : D.Access) : candidate D ∈ FP :=
  ImplicitGraph.word_computable (A.width.comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)) (BinaryFn.fromBits pairSnd_mem_FP)

def equalQuery (D : Data) (r : List Bool) : List Bool :=
  pair (pairFst (pairFst r)) (pair (candidate D r) (pairSnd (pairFst r)))
def vertexQuery (D : Data) (r : List Bool) : List Bool := pair (pairFst (pairFst r)) (candidate D r)
def lessQuery (D : Data) (r : List Bool) : List Bool := equalQuery D r
theorem equalQuery_FP {D : Data} (A : D.Access) : equalQuery D ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
    (mem_FP_pair (candidate_FP A) (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP))
theorem vertexQuery_FP {D : Data} (A : D.Access) : vertexQuery D ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) (candidate_FP A)

noncomputable def first (D : Data) : Language :=
  {q | q ∈ D.valid ∧ ∀ k < Nat.fromBitsLE (pairSnd q), equalQuery D (pair q (BinaryNatCode.encode k)) ∉ D.equal}

theorem firstDecider {D : Data} (A : D.Access) : SpaceDecider (first D) := by
  have E := (A.equal.precompose (equalQuery D) (equalQuery_FP A)).flagEvaluator
  have hnot := (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).not.flag_mem_FP
  have N := (E.postcompose _ hnot).forall_binary (BinaryFn.fromBits pairSnd_mem_FP)
  apply (A.valid.flagEvaluator.andFlags N).decider (fun z => decide (z = [true]))
    (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro q
  simp only [first, Set.mem_ofPred_eq, Set.mem_preimage, Function.comp_apply, id_eq, List.cons.injEq, and_true, decide_eq_true_eq]

noncomputable def test (D : Data) (r : List Bool) : List Bool :=
  [decide (vertexQuery D r ∈ first D ∧ lessQuery D r ∈ D.less)]

theorem testEvaluator {D : Data} (A : D.Access) : SpaceFunction (test D) := by
  have F := ((firstDecider A).precompose (vertexQuery D) (vertexQuery_FP A)).flagEvaluator
  have L := (A.less.precompose (lessQuery D) (equalQuery_FP A)).flagEvaluator
  exact (F.andFlags L).congr (funext fun r => by
    apply congrArg List.singleton
    apply Bool.eq_iff_iff.mpr
    simp only [Set.mem_preimage, List.cons.injEq, and_true, decide_eq_true_eq])

noncomputable def rank (D : Data) (q : List Bool) : ℕ :=
  BinaryFlagCountBits.count (test D) q (2 ^ D.width (pairFst q))

theorem evaluator {D : Data} (A : D.Access) : SpaceFunction (fun q => BinaryNatCode.encode (rank D q)) :=
  BinaryFlagCountBits.evaluator (testEvaluator A) ((BinaryFn.const 2).powUnary (A.width.comp pairFst_mem_FP))

noncomputable def indices (D : Data) (c : List Bool) : Finset ℕ :=
  (Finset.range (2 ^ D.width c)).filter (fun k => pair c (word D c k) ∈ D.valid)

noncomputable def projection (D : Data) (c : List Bool) (k : ℕ) : ℝ := D.value c (word D c k)

theorem first_iff_representative (D : Data) (c : List Bool) (k : ℕ) (hk : k < 2 ^ D.width c) :
    pair c (word D c k) ∈ first D ↔ k ∈ Geometry.FiniteImageRank.representatives (indices D c) (projection D c) := by
  simp only [first, Set.mem_ofPred_eq, pairSnd_pair, word_value D c k hk, Geometry.FiniteImageRank.representatives,
    Finset.mem_filter, indices, Finset.mem_range]
  constructor
  · rintro ⟨hvalid, hfirst⟩
    refine ⟨⟨hk, hvalid⟩, ?_⟩
    intro j hj he
    by_contra hn
    have hjk : j < k := lt_of_not_ge hn
    have H := hfirst j hjk
    apply H
    simp only [equalQuery, candidate, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact (D.equal_iff _ _ _).mpr ⟨hj.2, hvalid, he⟩
  · rintro ⟨⟨_, hvalid⟩, hmin⟩
    refine ⟨hvalid, ?_⟩
    intro j hj he
    simp only [equalQuery, candidate, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits] at he
    have H := (D.equal_iff _ _ _).mp he
    have hjmin : k ≤ j := hmin j ⟨hj.trans hk, H.1⟩ H.2.2
    omega

theorem test_packet (D : Data) (c w : List Bool) (hw : pair c w ∈ D.valid) (k : ℕ) :
    test D (pair (pair c w) (BinaryNatCode.encode k)) = [true] ↔
      pair c (word D c k) ∈ first D ∧ D.value c (word D c k) < D.value c w := by
  simp only [test, vertexQuery, lessQuery, equalQuery, candidate, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, List.cons.injEq, and_true, decide_eq_true_eq, D.less_iff]
  constructor
  · rintro ⟨hf, _, _, hlt⟩
    exact ⟨hf, hlt⟩
  · rintro ⟨hf, hlt⟩
    exact ⟨hf, hf.1, hw, hlt⟩

theorem rank_eq (D : Data) (c w : List Bool) (hw : pair c w ∈ D.valid) :
    rank D (pair c w) = Geometry.FiniteImageRank.rank (indices D c) (projection D c) (D.value c w) := by
  unfold rank BinaryFlagCountBits.count Geometry.FiniteImageRank.rank
  rw [pairFst_pair]
  apply congrArg Finset.card
  ext k
  simp only [Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hk, ht⟩
    have H := (test_packet D c w hw k).mp ht
    exact ⟨(first_iff_representative D c k hk).mp H.1, H.2⟩
  · rintro ⟨hk, hlt⟩
    have hin := (Finset.mem_filter.mp hk).1
    have hb := Finset.mem_range.mp (Finset.mem_filter.mp hin).1
    exact ⟨hb, (test_packet D c w hw k).mpr ⟨(first_iff_representative D c k hb).mpr hk, hlt⟩⟩

theorem image_rank (D : Data) (c w : List Bool) (hw : pair c w ∈ D.valid) :
    rank D (pair c w) = (((indices D c).image (projection D c)).filter (fun x => x < D.value c w)).card :=
  (rank_eq D c w hw).trans (Geometry.FiniteImageRank.rank_eq _ _ _)

theorem rank_bound (D : Data) (q : List Bool) : rank D q ≤ 2 ^ D.width (pairFst q) :=
  BinaryFlagCountBits.count_le _ _ _

theorem rank_bits (D : Data) (q : List Bool) : (rank D q).size ≤ D.width (pairFst q) + 1 := by
  apply Nat.size_le.mpr
  exact (rank_bound D q).trans_lt (Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _))

end LeanCanny.Encoding.FiniteWordProjectionRank
