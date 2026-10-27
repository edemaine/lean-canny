/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleFiberRootOrder

/-! # Native real-order ranks of hash-enumerated fiber roots

The actual root count is computed internally. A streamed sum of native
comparisons counts the roots strictly below the specified hash label.
This converts the short symbolic labels to the geometric ordered labels.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleFiberRootRank
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open BoundedCriticalSampleFiberRootOrder
open scoped Classical BigOperators

theorem rank_lt (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) (a : Fin (BoundedCriticalSampleSlice.RootCount.count P F c)) :
    rank P F c a < BoundedCriticalSampleSlice.RootCount.count P F c :=
  (((BoundedCriticalSampleSlice.RootCount.roots P F c).orderIsoOfFin rfl).symm (BoundedCriticalSampleFiberHashEnumeration.root P F c a)).isLt

theorem rank_injective (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) : Function.Injective (rank P F c) := by
  intro a b he
  apply BoundedCriticalSampleFiberHashEnumeration.root_injective P F c
  exact ((BoundedCriticalSampleSlice.RootCount.roots P F c).orderIsoOfFin rfl).symm.injective (Fin.ext he)

theorem exists_rank (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) (n : ℕ) (hn : n < BoundedCriticalSampleSlice.RootCount.count P F c) :
    ∃ a, rank P F c a = n := by
  let x := (BoundedCriticalSampleSlice.RootCount.roots P F c).orderIsoOfFin rfl ⟨n, hn⟩
  obtain ⟨a, ha⟩ := BoundedCriticalSampleFiberHashEnumeration.root_surjective P F c x
  refine ⟨a, ?_⟩
  unfold rank
  rw [ha]
  simp only [x, OrderIso.symm_apply_apply]

theorem card_below (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) (a : Fin (BoundedCriticalSampleSlice.RootCount.count P F c)) :
    ((Finset.univ : Finset (Fin (BoundedCriticalSampleSlice.RootCount.count P F c))).filter
      (fun j => (BoundedCriticalSampleFiberHashEnumeration.root P F c j).val < (BoundedCriticalSampleFiberHashEnumeration.root P F c a).val)).card =
        rank P F c a := by
  rw [← Finset.card_range (rank P F c a)]
  apply Finset.card_bij (fun j _ => rank P F c j)
  · intro j hj
    exact Finset.mem_range.mpr ((rank_lt_iff P F c j a).mpr (Finset.mem_filter.mp hj).2)
  · intro j _ k _ hjk
    exact rank_injective P F c hjk
  · intro n hn
    have hna := Finset.mem_range.mp hn
    obtain ⟨j, hj⟩ := exists_rank P F c n (hna.trans (rank_lt P F c a))
    have hja : rank P F c j < rank P F c a := by rw [hj]; exact hna
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (rank_lt_iff P F c j a).mp hja⟩, hj⟩

noncomputable def descriptor (P : Readers) (F : BoundedAlgebraicSlice.Family) (u : List Bool) : List Bool :=
  pair u (BinaryNatCode.encode (BoundedCriticalSampleSlice.RootCount.count P F (pairFst u)))
theorem descriptor_evaluator {P : Readers} (h : P.PolyTime) {F : BoundedAlgebraicSlice.Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (descriptor P F) :=
  ((BoundedCriticalSampleSlice.RootCount.count_evaluator h A ha).precompose pairFst pairFst_mem_FP).withInput

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

noncomputable def summand (P : Readers) (F : BoundedAlgebraicSlice.Family) (q : List Bool) : ℤ :=
  if BoundedCriticalSampleFiberRootOrder.value P F (compareQuery q) = [true] then 1 else 0
theorem summand_evaluator {P : Readers} (h : P.PolyTime) {F : BoundedAlgebraicSlice.Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun q => SignStatisticBits.integerCode (summand P F q)) := by
  have E := ((BoundedCriticalSampleFiberRootOrder.evaluator h A ha).precompose compareQuery compareQuery_FP).postcompose indicator indicator_FP
  apply E.congr
  funext q
  simp only [Function.comp_apply, indicator, summand]
  split_ifs <;> rfl

noncomputable def total (P : Readers) (F : BoundedAlgebraicSlice.Family) (z : List Bool) : ℤ :=
  ∑ j ∈ Finset.range (Nat.fromBitsLE (pairSnd z)), summand P F (pair z (BinaryNatCode.encode j))
theorem total_evaluator {P : Readers} (h : P.PolyTime) {F : BoundedAlgebraicSlice.Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun z => SignStatisticBits.integerCode (total P F z)) :=
  IntegerSumBits.evaluator (summand_evaluator h A ha) pairSnd pairSnd_mem_FP
    (fun z j => summand P F (pair z (BinaryNatCode.encode j))) (fun _ _ => rfl)

noncomputable def value (P : Readers) (F : BoundedAlgebraicSlice.Family) (u : List Bool) : ℕ := (total P F (descriptor P F u)).toNat

attribute [local irreducible] total summand descriptor

theorem evaluator {P : Readers} (h : P.PolyTime) {F : BoundedAlgebraicSlice.Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun u => BinaryNatCode.encode (value P F u)) := by
  have E := ((descriptor_evaluator h A ha).chain (total_evaluator h A ha)).postcompose pairFst pairFst_mem_FP
  exact E.congr (funext fun u => by
    simp only [Function.comp_apply, SignStatisticBits.integerCode, pairFst_pair, value])

theorem summand_packet (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) (a b : Fin (BoundedCriticalSampleSlice.RootCount.count P F c)) :
    summand P F (pair (descriptor P F (pair c (BinaryNatCode.encode a.val))) (BinaryNatCode.encode b.val)) =
      if (BoundedCriticalSampleFiberHashEnumeration.root P F c b).val < (BoundedCriticalSampleFiberHashEnumeration.root P F c a).val then 1 else 0 := by
  have hq : compareQuery (pair (descriptor P F (pair c (BinaryNatCode.encode a.val))) (BinaryNatCode.encode b.val)) =
      pair c (pair (BinaryNatCode.encode b.val) (BinaryNatCode.encode a.val)) := by
    simp only [compareQuery, descriptor, pairFst_pair, pairSnd_pair]
  rw [summand, hq, BoundedCriticalSampleFiberRootOrder.value_packet]
  simp only [List.cons.injEq, and_true, decide_eq_true_eq]

theorem value_packet (P : Readers) (F : BoundedAlgebraicSlice.Family) (c : List Bool) (a : Fin (BoundedCriticalSampleSlice.RootCount.count P F c)) :
    value P F (pair c (BinaryNatCode.encode a.val)) = rank P F c a := by
  have hn : Nat.fromBitsLE (pairSnd (descriptor P F (pair c (BinaryNatCode.encode a.val)))) =
      BoundedCriticalSampleSlice.RootCount.count P F c := by
    simp only [descriptor, pairSnd_pair, pairFst_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have hs : total P F (descriptor P F (pair c (BinaryNatCode.encode a.val))) = (rank P F c a : ℤ) := by
    rw [total, hn, ← Fin.sum_univ_eq_sum_range]
    simp_rw [summand_packet]
    rw [Finset.sum_boole, card_below]
  rw [value, hs, Int.toNat_natCast]

end LeanCanny.Encoding.BoundedCriticalSampleFiberRootRank
