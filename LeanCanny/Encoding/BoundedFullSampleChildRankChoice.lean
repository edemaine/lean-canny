/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedFullSampleChildPrefixRank
public import LeanCanny.Computation.BoundedChoice

/-! # Selecting an regular-child sign row by its rank number

Adding a row increases prefix rank by at most one. Every rank below the full
root count therefore occurs at a rank-increasing row. A native bounded search
returns that row's short binary index without retaining a basis table.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedFullSampleChildRankChoice
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open BoundedFullSampleChildPrefixRank Submodule
open BoundedFullSampleChildSource (Inputs)
open scoped Classical

theorem prefixRank_eq_span (P : Inputs) (c : List Bool) (k : ℕ) :
    prefixRank P c k = Module.finrank ℚ (span ℚ (Set.range (prefixRows P c k).row)) := by
  rw [prefixRank, Matrix.rank_self_mul_transpose, Matrix.rank_eq_finrank_span_row]

theorem prefixRank_step (P : Inputs) (c : List Bool) (k : ℕ) :
    prefixRank P c (k + 1) ≤ prefixRank P c k + 1 := by
  by_cases hk : k < 2 ^ BoundedFullSampleChildRecords.length P c
  · let j : BoundedFullSampleChildRecordSpan.Index P c := ⟨k, hk⟩
    let W := span ℚ (Set.range (prefixRows P c k).row)
    let v := (BoundedFullSampleChildRecordSpan.matrix P c).row j
    have hspan : span ℚ (Set.range (prefixRows P c (k + 1)).row) ≤ W ⊔ span ℚ {v} := by
      apply span_le.mpr
      rintro _ ⟨i, rfl⟩
      by_cases hi : i.val < k
      · have hrow : (prefixRows P c (k + 1)).row i = (prefixRows P c k).row i := by
          ext x
          simp only [Matrix.row, prefixRows, Matrix.of_apply, hi, hi.trans (Nat.lt_succ_self k), ite_true]
        rw [hrow]
        exact (show W ≤ W ⊔ span ℚ {v} from le_sup_left) (subset_span ⟨i, rfl⟩)
      · by_cases he : i.val = k
        · have hij : i = j := Fin.ext he
          subst i
          have hrow : (prefixRows P c (k + 1)).row j = v := by
            ext x
            simp only [Matrix.row, prefixRows, Matrix.of_apply, j, Nat.lt_succ_self, ite_true, v]
          rw [hrow]
          exact (show span ℚ {v} ≤ W ⊔ span ℚ {v} from le_sup_right) (mem_span_singleton_self v)
        · have hnot : ¬ i.val < k + 1 := by omega
          have hrow : (prefixRows P c (k + 1)).row i = 0 := by
            ext x
            simp only [Matrix.row, prefixRows, Matrix.of_apply, hnot, ite_false, Pi.zero_apply]
          rw [hrow]
          exact zero_mem _
    have hfin := Submodule.finrank_mono hspan
    rw [prefixRank_eq_span, prefixRank_eq_span]
    change _ ≤ Module.finrank ℚ W + 1
    by_cases hv : v ∈ W
    · have he : span ℚ {v} ≤ W := (span_singleton_le_iff_mem v W).mpr hv
      rw [sup_eq_left.mpr he] at hfin
      omega
    · exact hfin.trans_eq (Submodule.finrank_sup_span_singleton hv)
  · have hn : 2 ^ BoundedFullSampleChildRecords.length P c ≤ k := by omega
    rw [prefixRank_full P c k hn, prefixRank_full P c (k + 1) (by omega)]
    omega

theorem exists_row (P : Inputs) (c : List Bool) (r : ℕ) (hr : r < BoundedFullSampleChildRegularCount.count P c) :
    ∃ i < 2 ^ BoundedFullSampleChildRecords.length P c,
      prefixRank P c i = r ∧ prefixRank P c i < prefixRank P c (i + 1) := by
  have hex : ∃ j, r < prefixRank P c j :=
    ⟨2 ^ BoundedFullSampleChildRecords.length P c, by rw [prefixRank_full P c _ le_rfl]; exact hr⟩
  have hj := Nat.find_spec hex
  have hjN : Nat.find hex ≤ 2 ^ BoundedFullSampleChildRecords.length P c :=
    Nat.find_min' hex (by rw [prefixRank_full P c _ le_rfl]; exact hr)
  have hj0 : 0 < Nat.find hex := by
    by_contra hn
    have hz : Nat.find hex = 0 := by omega
    rw [hz, prefixRank_zero] at hj
    omega
  let i := Nat.find hex - 1
  have he : i + 1 = Nat.find hex := by omega
  have hsmall : prefixRank P c i ≤ r := Nat.le_of_not_gt (Nat.find_min hex (by omega))
  have hbig : r < prefixRank P c (i + 1) := by rw [he]; exact hj
  have hstep := prefixRank_step P c i
  exact ⟨i, by omega, by omega, by omega⟩

def rankQuery (q : List Bool) : List Bool := pair (pairFst (pairFst q)) (pairSnd q)
theorem rankQuery_FP : rankQuery ∈ FP := mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP

noncomputable def language (P : Inputs) : Language := {q |
  prefixRank P (pairFst (pairFst q)) (Nat.fromBitsLE (pairSnd q)) = Nat.fromBitsLE (pairSnd (pairFst q)) ∧
    prefixRank P (pairFst (pairFst q)) (Nat.fromBitsLE (pairSnd q)) <
      prefixRank P (pairFst (pairFst q)) (Nat.fromBitsLE (pairSnd q) + 1)}

def accept (z : List Bool) : Bool :=
  decide (Nat.fromBitsLE (pairFst (pairSnd z)) = Nat.fromBitsLE (pairSnd (pairFst (pairFst z))) ∧
    Nat.fromBitsLE (pairFst (pairSnd z)) < Nat.fromBitsLE (pairSnd (pairSnd z)))
theorem accept_FP : (fun z => [accept z]) ∈ FP := by
  have hL := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
  have hR := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
  have hr := BinaryFn.fromBits (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP)
  exact ((hL.eq hr).and (hL.lt hR)).flag_mem_FP

theorem decider {P : Inputs} (h : P.PolyTime) : SpaceDecider (language P) := by
  have E := BoundedFullSampleChildPrefixRank.evaluator h
  have L := E.precompose rankQuery rankQuery_FP
  have R := E.precompose (successor ∘ rankQuery) (mem_FP_comp rankQuery_FP successor_FP)
  have Q := (L.pairOutputs R).withInput
  apply Q.decider accept accept_FP
  intro q
  simp only [language, accept, Set.mem_ofPred_eq, Function.comp_apply, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, decide_eq_true_eq, rank_as_prefix, rankQuery, successor,
    BinaryNat.succ_eq_bits]

noncomputable def index (P : Inputs) (u : List Bool) : ℕ := BoundedChoice.search (language P) u (dimension P u) - 1

theorem evaluator {P : Inputs} (h : P.PolyTime) :
    SpaceFunction (fun u => BinaryNatCode.encode (index P u)) := by
  have E := BoundedChoice.evaluator (decider h)
    (fun u => BinaryNatCode.encode (dimension P u)) (BinaryFn.bits_mem_FP (dimension_binary h))
  exact E.congr (funext fun _ => by simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, index])

theorem index_spec (P : Inputs) (u : List Bool)
    (hr : Nat.fromBitsLE (pairSnd u) < BoundedFullSampleChildRegularCount.count P (pairFst u)) :
    index P u < dimension P u ∧ prefixRank P (pairFst u) (index P u) = Nat.fromBitsLE (pairSnd u) ∧
      prefixRank P (pairFst u) (index P u) < prefixRank P (pairFst u) (index P u + 1) := by
  have hex : ∃ i < dimension P u, pair u (BinaryNatCode.encode i) ∈ language P := by
    obtain ⟨i, hi, he, hg⟩ := exists_row P (pairFst u) (Nat.fromBitsLE (pairSnd u)) hr
    refine ⟨i, hi, ?_⟩
    simpa only [language, Set.mem_ofPred_eq, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits] using ⟨he, hg⟩
  obtain ⟨hi, hm⟩ := BoundedChoice.witness (language P) u (dimension P u) hex
  refine ⟨hi, ?_⟩
  simpa only [language, Set.mem_ofPred_eq, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, index] using hm

end LeanCanny.Encoding.BoundedFullSampleChildRankChoice
