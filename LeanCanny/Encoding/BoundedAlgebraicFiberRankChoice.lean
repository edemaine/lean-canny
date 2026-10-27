/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicFiberPrefixRank
public import LeanCanny.Computation.BoundedChoice

/-! # Selecting a fiber-sign row by its rank number

Adding a row increases prefix rank by at most one. Every rank below the full
fiber-root count therefore occurs at a rank-increasing row. A native bounded search
returns that row's short binary index without retaining a basis table.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicFiberRankChoice
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open BoundedAlgebraicSlice BoundedAlgebraicFiberPrefixRank Submodule
open scoped Classical

theorem prefixRank_eq_span (P : Readers) (F : Family) (c : List Bool) (k : ℕ) :
    prefixRank P F c k = Module.finrank ℚ (span ℚ (Set.range (prefixRows P F c k).row)) := by
  rw [prefixRank, Matrix.rank_self_mul_transpose, Matrix.rank_eq_finrank_span_row]

theorem prefixRank_step (P : Readers) (F : Family) (c : List Bool) (k : ℕ) :
    prefixRank P F c (k + 1) ≤ prefixRank P F c k + 1 := by
  by_cases hk : k < 2 ^ BoundedAlgebraicFiberRecords.length F (pairFst c)
  · let j : BoundedAlgebraicFiberRecordSpan.Index F c := ⟨k, hk⟩
    let W := span ℚ (Set.range (prefixRows P F c k).row)
    let v := (BoundedAlgebraicFiberRecordSpan.matrix P F c).row j
    have hspan : span ℚ (Set.range (prefixRows P F c (k + 1)).row) ≤ W ⊔ span ℚ {v} := by
      apply span_le.mpr
      rintro _ ⟨i, rfl⟩
      by_cases hi : i.val < k
      · have hrow : (prefixRows P F c (k + 1)).row i = (prefixRows P F c k).row i := by
          ext x
          simp only [Matrix.row, prefixRows, hi, hi.trans (Nat.lt_succ_self k), ite_true]
        rw [hrow]
        exact (show W ≤ W ⊔ span ℚ {v} from le_sup_left) (subset_span ⟨i, rfl⟩)
      · by_cases he : i.val = k
        · have hij : i = j := Fin.ext he
          subst i
          have hrow : (prefixRows P F c (k + 1)).row j = v := by
            ext x
            simp only [Matrix.row, prefixRows, j, Nat.lt_succ_self, ite_true, v]
          rw [hrow]
          exact (show span ℚ {v} ≤ W ⊔ span ℚ {v} from le_sup_right) (mem_span_singleton_self v)
        · have hnot : ¬ i.val < k + 1 := by omega
          have hrow : (prefixRows P F c (k + 1)).row i = 0 := by
            ext x
            simp only [Matrix.row, prefixRows, hnot, ite_false, Pi.zero_apply]
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
  · have hn : 2 ^ BoundedAlgebraicFiberRecords.length F (pairFst c) ≤ k := by omega
    rw [prefixRank_full P F c k hn, prefixRank_full P F c (k + 1) (by omega)]
    omega

theorem exists_row (P : Readers) (F : Family) (c : List Bool) (r : ℕ) (hr : r < RootCount.count P F c) :
    ∃ i < 2 ^ BoundedAlgebraicFiberRecords.length F (pairFst c),
      prefixRank P F c i = r ∧ prefixRank P F c i < prefixRank P F c (i + 1) := by
  have hex : ∃ j, r < prefixRank P F c j :=
    ⟨2 ^ BoundedAlgebraicFiberRecords.length F (pairFst c), by rw [prefixRank_full P F c _ le_rfl]; exact hr⟩
  have hj := Nat.find_spec hex
  have hjN : Nat.find hex ≤ 2 ^ BoundedAlgebraicFiberRecords.length F (pairFst c) :=
    Nat.find_min' hex (by rw [prefixRank_full P F c _ le_rfl]; exact hr)
  have hj0 : 0 < Nat.find hex := by
    by_contra hn
    have hz : Nat.find hex = 0 := by omega
    rw [hz, prefixRank_zero] at hj
    omega
  let i := Nat.find hex - 1
  have he : i + 1 = Nat.find hex := by omega
  have hsmall : prefixRank P F c i ≤ r := Nat.le_of_not_gt (Nat.find_min hex (by omega))
  have hbig : r < prefixRank P F c (i + 1) := by rw [he]; exact hj
  have hstep := prefixRank_step P F c i
  exact ⟨i, by omega, by omega, by omega⟩

def rankQuery (q : List Bool) : List Bool := pair (pairFst (pairFst q)) (pairSnd q)
theorem rankQuery_FP : rankQuery ∈ FP := mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP

noncomputable def language (P : Readers) (F : Family) : Language := {q |
  prefixRank P F (pairFst (pairFst q)) (Nat.fromBitsLE (pairSnd q)) = Nat.fromBitsLE (pairSnd (pairFst q)) ∧
    prefixRank P F (pairFst (pairFst q)) (Nat.fromBitsLE (pairSnd q)) <
      prefixRank P F (pairFst (pairFst q)) (Nat.fromBitsLE (pairSnd q) + 1)}

def accept (z : List Bool) : Bool :=
  decide (Nat.fromBitsLE (pairFst (pairSnd z)) = Nat.fromBitsLE (pairSnd (pairFst (pairFst z))) ∧
    Nat.fromBitsLE (pairFst (pairSnd z)) < Nat.fromBitsLE (pairSnd (pairSnd z)))
theorem accept_FP : (fun z => [accept z]) ∈ FP := by
  have hL := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
  have hR := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
  have hr := BinaryFn.fromBits (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP)
  exact ((hL.eq hr).and (hL.lt hR)).flag_mem_FP

theorem decider {P : Readers} (h : P.PolyTime) {F : Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceDecider (language P F) := by
  have E := BoundedAlgebraicFiberPrefixRank.evaluator h A ha
  have L := E.precompose rankQuery rankQuery_FP
  have R := E.precompose (successor ∘ rankQuery) (mem_FP_comp rankQuery_FP successor_FP)
  have Q := (L.pairOutputs R).withInput
  apply Q.decider accept accept_FP
  intro q
  simp only [language, accept, Set.mem_ofPred_eq, Function.comp_apply, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, decide_eq_true_eq, rank_as_prefix, rankQuery, successor,
    BinaryNat.succ_eq_bits]

noncomputable def index (P : Readers) (F : Family) (u : List Bool) : ℕ := BoundedChoice.search (language P F) u (dimension F u) - 1

theorem evaluator {P : Readers} (h : P.PolyTime) {F : Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun u => BinaryNatCode.encode (index P F u)) := by
  have E := BoundedChoice.evaluator (decider h A ha)
    (fun u => BinaryNatCode.encode (dimension F u)) (BinaryFn.bits_mem_FP (dimension_binary A))
  exact E.congr (funext fun _ => by simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, index])

theorem index_spec (P : Readers) (F : Family) (u : List Bool)
    (hr : Nat.fromBitsLE (pairSnd u) < RootCount.count P F (pairFst u)) :
    index P F u < dimension F u ∧ prefixRank P F (pairFst u) (index P F u) = Nat.fromBitsLE (pairSnd u) ∧
      prefixRank P F (pairFst u) (index P F u) < prefixRank P F (pairFst u) (index P F u + 1) := by
  have hex : ∃ i < dimension F u, pair u (BinaryNatCode.encode i) ∈ language P F := by
    obtain ⟨i, hi, he, hg⟩ := exists_row P F (pairFst u) (Nat.fromBitsLE (pairSnd u)) hr
    refine ⟨i, hi, ?_⟩
    simpa only [language, Set.mem_ofPred_eq, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits] using ⟨he, hg⟩
  obtain ⟨hi, hm⟩ := BoundedChoice.witness (language P F) u (dimension F u) hex
  refine ⟨hi, ?_⟩
  simpa only [language, Set.mem_ofPred_eq, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, index] using hm

end LeanCanny.Encoding.BoundedAlgebraicFiberRankChoice
