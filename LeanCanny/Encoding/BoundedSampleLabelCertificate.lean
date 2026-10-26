/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedSampleInterval
public import LeanCanny.Encoding.BoundedProjectionRationalCount
public import LeanCanny.Algebra.RationalIsolatingInterval

/-! # Native verification of rational isolating certificates for sample labels

A certificate supplies two rational cuts. Their strict root counts must be r
and r+1. The half-open interval then identifies root r, and an actual critical
sample query rejects extraneous roots. This file verifies supplied certificates;
a polynomial-space construction of isolating certificates remains required.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedSampleLabelCertificate
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open Brackets
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def context (payload : List Bool → List Bool) (c : List Bool) : List Bool := pair c (payload c)

theorem context_FP {payload : List Bool → List Bool} (h : payload ∈ FP) : context payload ∈ FP :=
  mem_FP_pair id_mem_FP h

noncomputable def cutCount (P : Readers) (payload : List Bool → List Bool) (c : List Bool) : ℕ :=
  BoundedProjectionRationalCount.count P (context payload c)

theorem count_evaluator {P : Readers} {payload : List Bool → List Bool} (h : P.PolyTime) (hp : payload ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun c => BinaryNatCode.encode (cutCount P payload c)) :=
  (BoundedProjectionRationalCount.evaluator h ha).precompose (context payload) (context_FP hp)

theorem rank_lt_cutCount_iff (P : Readers) (c payload : List Bool) (x : BoundedFullCriticalSamples.Samples P c) :
    BoundedCriticalLabels.rank P c x < BoundedProjectionRationalCount.count P (pair c payload) ↔
      BoundedCriticalSeparator.value P (BoundedCriticalSeparator.record P) c x.val <
        RationalCutBits.threshold (pair c payload) := by
  generalize hz : pair c payload = z
  have hc : pairFst z = c := by rw [← hz, pairFst_pair]
  subst c
  exact BoundedProjectionRationalCount.rank_lt_count_iff P z x

theorem interval_iff_rank_bounds (P : Readers) (lower upper : List Bool → List Bool)
    (c : List Bool) (x : BoundedFullCriticalSamples.Samples P c) :
    BoundedSampleInterval.InInterval P (BoundedCriticalSeparator.record P) (context lower) (context upper) c x ↔
      cutCount P lower c ≤ BoundedCriticalLabels.rank P c x ∧
        BoundedCriticalLabels.rank P c x < cutCount P upper c := by
  have hL := rank_lt_cutCount_iff P c (lower c) x
  have hU := rank_lt_cutCount_iff P c (upper c) x
  constructor
  · rintro ⟨hl, hu⟩
    exact ⟨le_of_not_gt (fun hr => not_lt_of_ge hl (hL.mp hr)), hU.mpr hu⟩
  · rintro ⟨hl, hu⟩
    exact ⟨le_of_not_gt (fun hr => not_lt_of_ge hl (hL.mpr hr)), hU.mp hu⟩

noncomputable def Isolates (P : Readers) (lower upper word : List Bool → List Bool) (c : List Bool) : Prop :=
  (word c).length = BoundedCriticalProjection.labelWidth P c ∧
    cutCount P lower c = Nat.fromBitsLE (word c) ∧ cutCount P upper c = Nat.fromBitsLE (word c) + 1

theorem interval_iff_label (P : Readers) (lower upper word : List Bool → List Bool) (c : List Bool)
    (hI : Isolates P lower upper word c) (x : BoundedFullCriticalSamples.Samples P c) :
    BoundedSampleInterval.InInterval P (BoundedCriticalSeparator.record P) (context lower) (context upper) c x ↔
      BoundedCriticalLabels.label P c x = word c := by
  rw [interval_iff_rank_bounds, hI.2.1, hI.2.2, BoundedCriticalLabels.label_eq_iff]
  constructor
  · rintro ⟨hl, hu⟩
    exact ⟨hI.1, by omega⟩
  · rintro ⟨_, hr⟩
    omega

noncomputable def compare (P : Readers) (word : List Bool → List Bool) (z : List Bool) : Bool :=
  decide ((word (pairFst z)).length = BoundedCriticalProjection.labelWidth P (pairFst z) ∧
    Nat.fromBitsLE (pairFst (pairSnd z)) = Nat.fromBitsLE (word (pairFst z)) ∧
      Nat.fromBitsLE (pairSnd (pairSnd z)) = Nat.fromBitsLE (word (pairFst z)) + 1)

theorem compare_FP {P : Readers} {word : List Bool → List Bool} (h : P.PolyTime) (hw : word ∈ FP) :
    (fun z => [compare P word z]) ∈ FP := by
  have hr := mem_FP_comp pairFst_mem_FP hw
  have hn := BinaryFn.fromBits hr
  have hL := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
  have hU := BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)
  have he := FPPred.eq (UnaryFn.length hr) ((BoundedCriticalProjection.labelWidth_unary h).comp pairFst_mem_FP)
  exact (he.and ((hL.eq hn).and (hU.eq (hn.add (BinaryFn.const 1))))).flag_mem_FP

theorem isolation_evaluator {P : Readers} {lower upper word : List Bool → List Bool}
    (h : P.PolyTime) (hl : lower ∈ FP) (hu : upper ∈ FP) (hw : word ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun c => [decide (Isolates P lower upper word c)]) := by
  have E := ((count_evaluator h hl ha).pairOutputs (count_evaluator h hu ha)).withInput.postcompose
    (fun z => [compare P word z]) (compare_FP h hw)
  apply E.congr
  funext c
  simp only [Function.comp_apply, compare, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, Isolates]
  exact congrArg List.singleton (decide_eq_decide.mpr Iff.rfl)

noncomputable def Certified (P : Readers) (lower upper word : List Bool → List Bool) (p : List Bool → Formula)
    (c : List Bool) : Prop :=
  Isolates P lower upper word c ∧ BoundedSampleInterval.Feasible P (context lower) (context upper) p c

theorem certified_iff (P : Readers) (lower upper word : List Bool → List Bool) (p : List Bool → Formula)
    (c : List Bool) : Certified P lower upper word p c ↔
      Isolates P lower upper word c ∧ ∃ x : BoundedFullCriticalSamples.Samples P c,
        BoundedCriticalLabels.label P c x = word c ∧ BoundedCriticalSampleQuery.Matches P c (p c) x := by
  constructor
  · rintro ⟨hI, x, hx, hp⟩
    exact ⟨hI, x, (interval_iff_label P lower upper word c hI x).mp hx, hp⟩
  · rintro ⟨hI, x, hx, hp⟩
    exact ⟨hI, x, (interval_iff_label P lower upper word c hI x).mpr hx, hp⟩

theorem evaluator {P : Readers} {lower upper word : List Bool → List Bool} {p : List Bool → Formula}
    (h : P.PolyTime) (hl : lower ∈ FP) (hu : upper ∈ FP) (hw : word ∈ FP)
    (hp : (fun c => (p c).encode) ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun c => [decide (Certified P lower upper word p c)]) := by
  have E := (isolation_evaluator h hl hu hw ha).andFlags
    (BoundedSampleInterval.evaluator h (context_FP hl) (context_FP hu) hp ha)
  apply E.congr
  funext c
  simp only [List.cons.injEq, and_true, decide_eq_true_eq, Certified]
  exact decide_eq_decide.mpr Iff.rfl

theorem decider {P : Readers} {lower upper word : List Bool → List Bool} {p : List Bool → Formula}
    (h : P.PolyTime) (hl : lower ∈ FP) (hu : upper ∈ FP) (hw : word ∈ FP)
    (hp : (fun c => (p c).encode) ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceDecider {c | Certified P lower upper word p c} := by
  apply (evaluator h hl hu hw hp ha).decider (fun w => decide (w = [true]))
    (stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro c
  simp only [Set.mem_ofPred_eq, decide_eq_true_eq, List.cons.injEq, and_true]

theorem accepted_valid (P : Readers) (lower upper word : List Bool → List Bool) (p : List Bool → Formula)
    (c : List Bool) (hc : Certified P lower upper word p c) : BoundedCriticalLabels.Valid P c (word c) := by
  obtain ⟨_, x, hx, _⟩ := (certified_iff P lower upper word p c).mp hc
  exact ⟨x, hx⟩

theorem accepted_unique (P : Readers) (lower upper word : List Bool → List Bool) (p : List Bool → Formula)
    (c : List Bool) (hc : Certified P lower upper word p c) :
    ∃! x : BoundedFullCriticalSamples.Samples P c,
      BoundedCriticalLabels.label P c x = word c ∧ BoundedCriticalSampleQuery.Matches P c (p c) x := by
  obtain ⟨_, x, hx, hp⟩ := (certified_iff P lower upper word p c).mp hc
  refine ⟨x, ⟨hx, hp⟩, ?_⟩
  intro y hy
  exact BoundedCriticalLabels.label_injective P c (hy.1.trans hx.symm)

theorem exists_certificate (P : Readers) (c : List Bool) (x : BoundedFullCriticalSamples.Samples P c)
    (p : Formula) (hp : BoundedCriticalSampleQuery.Matches P c p x) :
    ∃ lower upper : List Bool, Certified P (fun _ => lower) (fun _ => upper)
      (fun _ => BoundedCriticalLabels.label P c x) (fun _ => p) c := by
  let s := BoundedCriticalLabels.rootSet P c
  let v := BoundedCriticalSeparator.value P (BoundedCriticalSeparator.record P) c x.val
  have hv : v ∈ s := (BoundedCriticalLabels.projectedRoot P c x).property
  obtain ⟨a, b, _, _, hL, hU⟩ := RationalCutBits.exists_isolating_cuts s v hv
  have hr : BoundedCriticalLabels.rank P c x = (s.filter (fun t => t < v)).card :=
    BoundedProjectionRootCount.rank_eq_card_below P c x
  have hl : cutCount P (fun _ => RationalCutBits.payload a) c = BoundedCriticalLabels.rank P c x := by
    change BoundedProjectionRationalCount.count P (pair c (RationalCutBits.payload a)) = _
    simp only [BoundedProjectionRationalCount.count, pairFst_pair, RationalCutBits.threshold_payload]
    rw [hL, ← hr]
  have hu : cutCount P (fun _ => RationalCutBits.payload b) c = BoundedCriticalLabels.rank P c x + 1 := by
    change BoundedProjectionRationalCount.count P (pair c (RationalCutBits.payload b)) = _
    simp only [BoundedProjectionRationalCount.count, pairFst_pair, RationalCutBits.threshold_payload]
    rw [hU, Finset.card_insert_of_notMem (by simp), ← hr]
  have hI : Isolates P (fun _ => RationalCutBits.payload a) (fun _ => RationalCutBits.payload b)
      (fun _ => BoundedCriticalLabels.label P c x) c := by
    refine ⟨BoundedCriticalLabels.label_length P c x, ?_, ?_⟩ <;>
      simp only [BoundedCriticalLabels.label_value] <;> assumption
  refine ⟨RationalCutBits.payload a, RationalCutBits.payload b, hI, x, ?_, hp⟩
  exact (interval_iff_label P _ _ _ c hI x).mpr rfl

/-- Exact semantic completeness of the certificate scheme. No bound on the
two rational payload lengths is asserted here. -/
theorem matching_label_iff_exists_certificate (P : Readers) (c word : List Bool) (p : Formula) :
    (∃ x : BoundedFullCriticalSamples.Samples P c,
      BoundedCriticalLabels.label P c x = word ∧ BoundedCriticalSampleQuery.Matches P c p x) ↔
    ∃ lower upper : List Bool, Certified P (fun _ => lower) (fun _ => upper) (fun _ => word) (fun _ => p) c := by
  constructor
  · rintro ⟨x, hx, hp⟩
    obtain ⟨lower, upper, hC⟩ := exists_certificate P c x p hp
    exact ⟨lower, upper, hx ▸ hC⟩
  · rintro ⟨lower, upper, hC⟩
    exact ((certified_iff P _ _ _ _ c).mp hC).2

end LeanCanny.Encoding.BoundedSampleLabelCertificate
