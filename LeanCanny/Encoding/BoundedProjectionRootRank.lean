/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedProjectionRootOrder

/-! # Native real-order ranks of hash-enumerated projection roots

The actual root count is computed internally. A streamed sum of native
comparisons counts the roots strictly below the specified hash label.
This converts the short symbolic labels to the geometric ordered labels.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedProjectionRootRank
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open BoundedProjectionRootOrder
open scoped Classical BigOperators

theorem rank_lt (P : Readers) (c : List Bool) (a : Fin (BoundedProjectionRootCount.count P c)) :
    rank P c a < BoundedProjectionRootCount.count P c :=
  (((BoundedCriticalLabels.rootSet P c).orderIsoOfFin rfl).symm (BoundedProjectionHashEnumeration.root P c a)).isLt

theorem rank_injective (P : Readers) (c : List Bool) : Function.Injective (rank P c) := by
  intro a b he
  apply BoundedProjectionHashEnumeration.root_injective P c
  exact ((BoundedCriticalLabels.rootSet P c).orderIsoOfFin rfl).symm.injective (Fin.ext he)

theorem exists_rank (P : Readers) (c : List Bool) (n : ℕ) (hn : n < BoundedProjectionRootCount.count P c) :
    ∃ a, rank P c a = n := by
  let x := (BoundedCriticalLabels.rootSet P c).orderIsoOfFin rfl ⟨n, hn⟩
  obtain ⟨a, ha⟩ := BoundedProjectionHashEnumeration.root_surjective P c x
  refine ⟨a, ?_⟩
  unfold rank
  rw [ha]
  simp only [x, OrderIso.symm_apply_apply]

theorem card_below (P : Readers) (c : List Bool) (a : Fin (BoundedProjectionRootCount.count P c)) :
    ((Finset.univ : Finset (Fin (BoundedProjectionRootCount.count P c))).filter
      (fun j => (BoundedProjectionHashEnumeration.root P c j).val < (BoundedProjectionHashEnumeration.root P c a).val)).card =
        rank P c a := by
  rw [← Finset.card_range (rank P c a)]
  apply Finset.card_bij (fun j _ => rank P c j)
  · intro j hj
    exact Finset.mem_range.mpr ((rank_lt_iff P c j a).mpr (Finset.mem_filter.mp hj).2)
  · intro j _ k _ hjk
    exact rank_injective P c hjk
  · intro n hn
    have hna := Finset.mem_range.mp hn
    obtain ⟨j, hj⟩ := exists_rank P c n (hna.trans (rank_lt P c a))
    have hja : rank P c j < rank P c a := by rw [hj]; exact hna
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (rank_lt_iff P c j a).mp hja⟩, hj⟩

noncomputable def descriptor (P : Readers) (u : List Bool) : List Bool :=
  pair u (BinaryNatCode.encode (BoundedProjectionRootCount.count P (pairFst u)))
theorem descriptor_evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (descriptor P) :=
  ((BoundedProjectionRootCount.evaluator h ha).precompose pairFst pairFst_mem_FP).withInput

def compareQuery (q : List Bool) : List Bool :=
  pair (pairFst (pairFst (pairFst q))) (pair (pairSnd q) (pairSnd (pairFst (pairFst q))))
theorem compareQuery_FP : compareQuery ∈ FP := by
  have hu := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hc := mem_FP_comp hu pairFst_mem_FP
  have ha := mem_FP_comp hu pairSnd_mem_FP
  exact mem_FP_pair hc (mem_FP_pair pairSnd_mem_FP ha)

def indicator (z : List Bool) : List Bool :=
  if z = [true] then SignStatisticBits.integerCode 1 else SignStatisticBits.integerCode 0
theorem indicator_FP : indicator ∈ FP :=
  (Brackets.stringEq_fppred id_mem_FP (constFn_mem_FP [true])).ite_mem_FP (constFn_mem_FP _) (constFn_mem_FP _)

noncomputable def summand (P : Readers) (q : List Bool) : ℤ :=
  if BoundedProjectionRootOrder.value P (compareQuery q) = [true] then 1 else 0
theorem summand_evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun q => SignStatisticBits.integerCode (summand P q)) := by
  have E := ((BoundedProjectionRootOrder.evaluator h ha).precompose compareQuery compareQuery_FP).postcompose indicator indicator_FP
  apply E.congr
  funext q
  simp only [Function.comp_apply, indicator, summand]
  split_ifs <;> rfl

noncomputable def total (P : Readers) (z : List Bool) : ℤ :=
  ∑ j ∈ Finset.range (Nat.fromBitsLE (pairSnd z)), summand P (pair z (BinaryNatCode.encode j))
theorem total_evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun z => SignStatisticBits.integerCode (total P z)) :=
  IntegerSumBits.evaluator (summand_evaluator h ha) pairSnd pairSnd_mem_FP
    (fun z j => summand P (pair z (BinaryNatCode.encode j))) (fun _ _ => rfl)

noncomputable def value (P : Readers) (u : List Bool) : ℕ := (total P (descriptor P u)).toNat

attribute [local irreducible] total summand descriptor

theorem evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun u => BinaryNatCode.encode (value P u)) := by
  have E := ((descriptor_evaluator h ha).chain (total_evaluator h ha)).postcompose pairFst pairFst_mem_FP
  exact E.congr (funext fun u => by
    simp only [Function.comp_apply, SignStatisticBits.integerCode, pairFst_pair, value])

theorem summand_packet (P : Readers) (c : List Bool) (a b : Fin (BoundedProjectionRootCount.count P c)) :
    summand P (pair (descriptor P (pair c (BinaryNatCode.encode a.val))) (BinaryNatCode.encode b.val)) =
      if (BoundedProjectionHashEnumeration.root P c b).val < (BoundedProjectionHashEnumeration.root P c a).val then 1 else 0 := by
  have hq : compareQuery (pair (descriptor P (pair c (BinaryNatCode.encode a.val))) (BinaryNatCode.encode b.val)) =
      pair c (pair (BinaryNatCode.encode b.val) (BinaryNatCode.encode a.val)) := by
    simp only [compareQuery, descriptor, pairFst_pair, pairSnd_pair]
  rw [summand, hq, BoundedProjectionRootOrder.value_packet]
  simp only [List.cons.injEq, and_true, decide_eq_true_eq]

theorem value_packet (P : Readers) (c : List Bool) (a : Fin (BoundedProjectionRootCount.count P c)) :
    value P (pair c (BinaryNatCode.encode a.val)) = rank P c a := by
  have hn : Nat.fromBitsLE (pairSnd (descriptor P (pair c (BinaryNatCode.encode a.val)))) =
      BoundedProjectionRootCount.count P c := by
    simp only [descriptor, pairSnd_pair, pairFst_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have hs : total P (descriptor P (pair c (BinaryNatCode.encode a.val))) = (rank P c a : ℤ) := by
    rw [total, hn, ← Fin.sum_univ_eq_sum_range]
    simp_rw [summand_packet]
    rw [Finset.sum_boole, card_below]
  rw [value, hs, Int.toNat_natCast]

/-- On a genuine critical sample, the native rank is exactly its original
ordered projection label index. Extraneous projection roots remain counted. -/
theorem sample_packet (P : Readers) (c : List Bool) (x : BoundedFullCriticalSamples.Samples P c)
    (a : Fin (BoundedProjectionRootCount.count P c))
    (ha : BoundedProjectionHashEnumeration.root P c a = BoundedCriticalLabels.projectedRoot P c x) :
    value P (pair c (BinaryNatCode.encode a.val)) = BoundedCriticalLabels.rank P c x := by
  rw [value_packet, rank, ha]
  rfl

end LeanCanny.Encoding.BoundedProjectionRootRank
