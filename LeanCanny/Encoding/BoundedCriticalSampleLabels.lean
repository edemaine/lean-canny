/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleCount
public import LeanCanny.Computation.ImplicitGraphPSPACE

/-! # Dense ordered labels for the actual full critical samples

Filtered parameter roots are ordered on the real line. Every ordinal below
the native exact sample count denotes one sample, using the existing unary
label-width bound. Native validity checks both the width and the ordinal.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSampleLabels
open LeanCanny.ETR LeanCanny.Algebra LeanCanny.Computation BoundedFullWriter
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedCriticalRationalCoordinates.parameter

noncomputable def rootSet (P : Readers) (c : List Bool) : Finset ℝ :=
  (((BoundedCriticalRationalCoordinates.parameter P c).map (Int.castRingHom ℝ)).roots.toFinset).filter
    (BoundedCriticalFilters.Valid P c)

theorem mapped_ne_zero (P : Readers) (c : List Bool) :
    (BoundedCriticalRationalCoordinates.parameter P c).map (Int.castRingHom ℝ) ≠ 0 :=
  (Polynomial.map_ne_zero_iff Int.cast_injective).mpr (BoundedCriticalRationalCoordinates.parameter_ne_zero P c)

theorem mem_rootSet (P : Readers) (c : List Bool) (theta : ℝ) :
    theta ∈ rootSet P c ↔ BoundedCriticalFilters.Valid P c theta := by
  rw [rootSet, Finset.mem_filter]
  constructor
  · exact And.right
  · intro h
    refine ⟨?_, h⟩
    rw [Multiset.mem_toFinset, Polynomial.mem_roots (mapped_ne_zero P c), Polynomial.IsRoot.def, Polynomial.eval_map]
    exact h.1

noncomputable def rootEquiv (P : Readers) (c : List Bool) :
    {theta : ℝ // theta ∈ rootSet P c} ≃ BoundedFullCriticalSamples.Samples P c :=
  (Equiv.subtypeEquivRight (mem_rootSet P c)).trans (BoundedCriticalFilters.realEquiv P c)

theorem rootSet_card (P : Readers) (c : List Bool) : (rootSet P c).card = BoundedCriticalSampleCount.count P c := by
  calc
    _ = Nat.card {theta : ℝ // theta ∈ rootSet P c} := by simp only [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = _ := Nat.card_congr (rootEquiv P c)

noncomputable def parameter (P : Readers) (c : List Bool) (x : BoundedFullCriticalSamples.Samples P c) :
    {theta : ℝ // theta ∈ rootSet P c} := (rootEquiv P c).symm x

noncomputable def rank (P : Readers) (c : List Bool) (x : BoundedFullCriticalSamples.Samples P c) : ℕ :=
  (((rootSet P c).orderIsoOfFin (rootSet_card P c)).symm (parameter P c x)).val

theorem rank_lt_count (P : Readers) (c : List Bool) (x : BoundedFullCriticalSamples.Samples P c) :
    rank P c x < BoundedCriticalSampleCount.count P c :=
  (((rootSet P c).orderIsoOfFin (rootSet_card P c)).symm (parameter P c x)).isLt

theorem rank_injective (P : Readers) (c : List Bool) : Function.Injective (rank P c) := by
  intro x y h
  apply (rootEquiv P c).symm.injective
  apply ((rootSet P c).orderIsoOfFin (rootSet_card P c)).symm.injective
  exact Fin.ext h

theorem exists_rank (P : Readers) (c : List Bool) (i : Fin (BoundedCriticalSampleCount.count P c)) :
    ∃ x : BoundedFullCriticalSamples.Samples P c, rank P c x = i.val := by
  let t := (rootSet P c).orderIsoOfFin (rootSet_card P c) i
  refine ⟨rootEquiv P c t, ?_⟩
  simp only [rank, parameter, Equiv.symm_apply_apply, t, OrderIso.symm_apply_apply]

private theorem ordered_rank {α : Type*} [LinearOrder α] (s : Finset α) {n : ℕ} (hn : s.card = n) (x : {a // a ∈ s}) :
    ((s.orderIsoOfFin hn).symm x).val = (s.filter (fun a => a < x.val)).card := by
  let e := (s.orderIsoOfFin hn).symm
  rw [← Finset.card_range (e x).val]
  symm
  apply Finset.card_bij (fun y hy => (e ⟨y, (Finset.mem_filter.mp hy).1⟩).val)
  · intro y hy
    rw [Finset.mem_range]
    exact e.lt_iff_lt.mpr (Finset.mem_filter.mp hy).2
  · intro a ha b hb hab
    exact congrArg Subtype.val (e.injective (Fin.ext hab))
  · intro j hj
    have hj' : j < (e x).val := Finset.mem_range.mp hj
    let i : Fin n := ⟨j, hj'.trans (e x).isLt⟩
    refine ⟨(e.symm i).val, Finset.mem_filter.mpr ⟨(e.symm i).property, ?_⟩, ?_⟩
    · change e.symm i < x
      have h := e.symm.strictMono (show i < e x from hj')
      rw [e.symm_apply_apply] at h
      exact h
    · simp only [e.apply_symm_apply]
      rfl

theorem rank_eq_card_below (P : Readers) (c : List Bool) (x : BoundedFullCriticalSamples.Samples P c) :
    rank P c x = ((rootSet P c).filter (fun theta => theta < (parameter P c x).val)).card :=
  ordered_rank _ _ _

noncomputable def label (P : Readers) (c : List Bool) (x : BoundedFullCriticalSamples.Samples P c) : List Bool :=
  ImplicitGraph.word (BoundedFullCriticalSamples.labelWidth P c) (rank P c x)

theorem label_length (P : Readers) (c : List Bool) (x : BoundedFullCriticalSamples.Samples P c) :
    (label P c x).length = BoundedFullCriticalSamples.labelWidth P c := ImplicitGraph.length_word _ _

theorem label_value (P : Readers) (c : List Bool) (x : BoundedFullCriticalSamples.Samples P c) :
    Nat.fromBitsLE (label P c x) = rank P c x := by
  have hr := (rank_lt_count P c x).trans_le (BoundedFullCriticalSamples.finite_samples P c).2
  have H := FixedWidthNatVector.decode_block 1 (BoundedFullCriticalSamples.labelWidth P c)
    (fun _ => rank P c x) 0 (by decide) hr
  simp only [Nat.zero_mul, List.drop_zero] at H
  change Nat.fromBitsLE ((label P c x).take (BoundedFullCriticalSamples.labelWidth P c)) = _ at H
  simpa only [List.take_of_length_le (label_length P c x).le] using H

theorem label_injective (P : Readers) (c : List Bool) : Function.Injective (label P c) := by
  intro x y h
  exact rank_injective P c (by simpa only [label_value] using congrArg Nat.fromBitsLE h)

theorem label_eq_iff (P : Readers) (c w : List Bool) (x : BoundedFullCriticalSamples.Samples P c) :
    label P c x = w ↔ w.length = BoundedFullCriticalSamples.labelWidth P c ∧ Nat.fromBitsLE w = rank P c x := by
  constructor
  · rintro rfl
    exact ⟨label_length P c x, label_value P c x⟩
  · rintro ⟨hl, hv⟩
    rw [label, ← hv, ← hl, ImplicitGraph.word_fromBitsLE]

theorem valid_iff (P : Readers) (c w : List Bool) :
    (∃ x : BoundedFullCriticalSamples.Samples P c, label P c x = w) ↔
      w.length = BoundedFullCriticalSamples.labelWidth P c ∧ Nat.fromBitsLE w < BoundedCriticalSampleCount.count P c := by
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨label_length P c x, by rw [label_value]; exact rank_lt_count P c x⟩
  · rintro ⟨hl, hv⟩
    obtain ⟨x, hx⟩ := exists_rank P c ⟨Nat.fromBitsLE w, hv⟩
    exact ⟨x, (label_eq_iff P c w x).mpr ⟨hl, hx.symm⟩⟩

def validLanguage (P : Readers) : Language := {q | ∃ x, label P (pairFst q) x = pairSnd q}
noncomputable def compare (P : Readers) (z : List Bool) : Bool := decide
  ((pairSnd (pairFst z)).length = BoundedFullCriticalSamples.labelWidth P (pairFst (pairFst z)) ∧
    Nat.fromBitsLE (pairSnd (pairFst z)) < Nat.fromBitsLE (pairSnd z))

theorem compare_FP {P : Readers} (h : P.PolyTime) : (fun z => [compare P z]) ∈ FP := by
  have hw := (BoundedFullCriticalSamples.labelWidth_unary h).comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  have hr := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  exact ((FPPred.eq (UnaryFn.length hr) hw).and
    ((BinaryFn.fromBits hr).lt (BinaryFn.fromBits pairSnd_mem_FP))).flag_mem_FP

theorem valid_decider {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceDecider (validLanguage P) := by
  have E := ((BoundedCriticalSampleCount.evaluator h ha).precompose pairFst pairFst_mem_FP).withInput
  apply E.decider (compare P) (compare_FP h)
  intro q
  simp only [validLanguage, Set.mem_ofPred_eq, valid_iff, compare, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, decide_eq_true_eq, Function.comp_apply]

theorem valid_mem_PSPACE {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : validLanguage P ∈ PSPACE :=
  (valid_decider h ha).mem_PSPACE

end LeanCanny.Encoding.BoundedCriticalSampleLabels
