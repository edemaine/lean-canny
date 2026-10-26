/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedSelectedSampleQuery
public import LeanCanny.ETR.WeightedProjectionFP
public import LeanCanny.Algebra.RationalCutSpace

/-! # Actual critical-sample queries in rational projection intervals

Intervals are closed on the left and open on the right, matching differences
of strict root counts. Additional formula witnesses remain independent of the
critical circuit's auxiliary wires. Both selected records are computed natively.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedSampleInterval
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open Brackets
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

noncomputable def expression (P : Readers) (record endpoint : List Bool → List Bool) (c : List Bool) : Term :=
  WeightedProjection.cut (P.dim c + 4) (BoundedCriticalSeparator.weight P record c)
    (Nat.fromBitsLE (RationalCutBits.positive (endpoint c)))
    (Nat.fromBitsLE (RationalCutBits.negative (endpoint c))) (RationalCutBits.divisor (endpoint c))

noncomputable def formula (P : Readers) (record lower upper : List Bool → List Bool) (c : List Bool) : Formula :=
  .and (.not (.ltZero (expression P record lower c))) (.ltZero (expression P record upper c))

theorem expression_FP {P : Readers} {record endpoint : List Bool → List Bool} (h : P.PolyTime)
    (hr : record ∈ FP) (he : endpoint ∈ FP) : (fun c => (expression P record endpoint c).toData.toBits) ∈ FP := by
  have hp := BinaryFn.fromBits (mem_FP_comp he RationalCutBits.positive_FP)
  have hm := BinaryFn.fromBits (mem_FP_comp he RationalCutBits.negative_FP)
  have hd := (BinaryFn.fromBits (mem_FP_comp he RationalCutBits.denominatorMinusOne_FP)).add (BinaryFn.const 1)
  have hE := WeightedProjection.cut_FP (h.dim.add (UnaryFn.const 4))
    (BoundedCriticalSeparator.weight_binary h hr) hp hm hd
  exact mem_FP_of_eq hE (fun _ => rfl)

theorem formula_FP {P : Readers} {record lower upper : List Bool → List Bool} (h : P.PolyTime)
    (hr : record ∈ FP) (hl : lower ∈ FP) (hu : upper ∈ FP) :
    (fun c => (formula P record lower upper c).encode) ∈ FP := by
  have hF := Codec.taggedTwo_mem_FP 4
    (Codec.taggedOne_mem_FP 3 (Codec.taggedOne_mem_FP 2 (expression_FP h hr hl)))
    (Codec.taggedOne_mem_FP 2 (expression_FP h hr hu))
  exact mem_FP_of_eq hF (fun _ => by simp only [formula, Formula.encode, Formula.toData,
    Codec.taggedOne_toBits, Codec.taggedTwo_toBits])

theorem expression_eval (P : Readers) (record endpoint : List Bool → List Bool) (c : List Bool) (x : ℕ → ℝ) :
    (expression P record endpoint c).eval x =
      ((RationalCutBits.polynomial (endpoint c)).map (algebraMap ℤ ℝ)).eval
        (ProjectionCollision.projection (P.dim c + 4) (BoundedCriticalSeparator.weight P record c) x) := by
  rw [expression, WeightedProjection.eval_cut, RationalCutBits.eval_real]
  simp only [RationalCutBits.numerator, Int.cast_sub, Int.cast_natCast]
  ring

theorem formula_holds (P : Readers) (record lower upper : List Bool → List Bool) (c : List Bool) (x : ℕ → ℝ) :
    (formula P record lower upper c).Holds x ↔
      RationalCutBits.threshold (lower c) ≤
        ProjectionCollision.projection (P.dim c + 4) (BoundedCriticalSeparator.weight P record c) x ∧
      ProjectionCollision.projection (P.dim c + 4) (BoundedCriticalSeparator.weight P record c) x <
        RationalCutBits.threshold (upper c) := by
  have hs (e : List Bool → List Bool) : (expression P record e c).eval x < 0 ↔
      ProjectionCollision.projection (P.dim c + 4) (BoundedCriticalSeparator.weight P record c) x <
        RationalCutBits.threshold (e c) := by
    rw [expression_eval, ← sign_eq_neg_one_iff, ← SignType.neg_eq_neg_one]
    exact RationalCutBits.sign_neg_iff _ _
  simp only [formula, Formula.Holds, hs, not_lt]

noncomputable def InInterval (P : Readers) (record lower upper : List Bool → List Bool) (c : List Bool)
    (y : BoundedFullCriticalSamples.Samples P c) : Prop :=
  RationalCutBits.threshold (lower c) ≤ BoundedCriticalSeparator.value P record c y.val ∧
    BoundedCriticalSeparator.value P record c y.val < RationalCutBits.threshold (upper c)

theorem projection_value (P : Readers) (record : List Bool → List Bool) (c : List Bool)
    (x : ℕ → ℝ) (y : Fin (P.dim c + 4) → ℝ) (hx : ∀ i, x i.val = y i) :
    ProjectionCollision.projection (P.dim c + 4) (BoundedCriticalSeparator.weight P record c) x =
      BoundedCriticalSeparator.value P record c y := by
  rw [ProjectionCollision.projection, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [hx i, mul_comm]

theorem matches_formula (P : Readers) (record lower upper : List Bool → List Bool) (c : List Bool)
    (p : Formula) (y : BoundedFullCriticalSamples.Samples P c) :
    BoundedCriticalSampleQuery.Matches P c (.and (formula P record lower upper c) p) y ↔
      InInterval P record lower upper c y ∧ BoundedCriticalSampleQuery.Matches P c p y := by
  constructor
  · rintro ⟨x, hx, hF, hp⟩
    have hi := (formula_holds P record lower upper c x).mp hF
    rw [projection_value P record c x y.val hx] at hi
    exact ⟨hi, x, hx, hp⟩
  · rintro ⟨hi, x, hx, hp⟩
    refine ⟨x, hx, (formula_holds P record lower upper c x).mpr ?_, hp⟩
    rw [projection_value P record c x y.val hx]
    exact hi

theorem formula_packet (P : Readers) (record lower upper : List Bool → List Bool) (c : List Bool) :
    formula (P.comp pairFst) pairSnd (lower ∘ pairFst) (upper ∘ pairFst) (pair c (record c)) =
      formula P record lower upper c := by
  unfold formula expression BoundedCriticalSeparator.weight FixedWidthQuery.coordinate
  simp only [BoundedCriticalSeparator.width_comp]
  simp only [Readers.comp, Function.comp_apply, pairFst_pair, pairSnd_pair]

noncomputable def Feasible (P : Readers) (lower upper : List Bool → List Bool) (p : List Bool → Formula)
    (c : List Bool) : Prop :=
  ∃ y : BoundedFullCriticalSamples.Samples P c,
    InInterval P (BoundedCriticalSeparator.record P) lower upper c y ∧ BoundedCriticalSampleQuery.Matches P c (p c) y

theorem evaluator {P : Readers} {lower upper : List Bool → List Bool} {p : List Bool → Formula}
    (h : P.PolyTime) (hl : lower ∈ FP) (hu : upper ∈ FP) (hp : (fun c => (p c).encode) ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun c => [decide (Feasible P lower upper p c)]) := by
  let q : List Bool → Formula := fun z => .and
    (formula (P.comp pairFst) pairSnd (lower ∘ pairFst) (upper ∘ pairFst) z) (p (pairFst z))
  have hq : (fun z => (q z).encode) ∈ FP := by
    have hF := Codec.taggedTwo_mem_FP 4
      (formula_FP (h.comp pairFst_mem_FP) pairSnd_mem_FP (mem_FP_comp pairFst_mem_FP hl) (mem_FP_comp pairFst_mem_FP hu))
      (mem_FP_comp pairFst_mem_FP hp)
    exact mem_FP_of_eq hF (fun _ => by simp only [q, Function.comp_apply, Formula.encode, Formula.toData, Codec.taggedTwo_toBits])
  have E := BoundedSelectedSampleQuery.evaluator h hq ha
  apply E.congr
  funext c
  apply congrArg List.singleton
  apply decide_eq_decide.mpr
  simp only [q, formula_packet, pairFst_pair]
  rw [BoundedCriticalSampleQuery.selected_iff_samples]
  exact exists_congr (fun y => matches_formula P _ lower upper c (p c) y)

theorem decider {P : Readers} {lower upper : List Bool → List Bool} {p : List Bool → Formula}
    (h : P.PolyTime) (hl : lower ∈ FP) (hu : upper ∈ FP) (hp : (fun c => (p c).encode) ∈ FP)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceDecider {c | Feasible P lower upper p c} := by
  apply (evaluator h hl hu hp ha).decider (fun w => decide (w = [true]))
    (stringEq_fppred id_mem_FP (constFn_mem_FP [true])).flag_mem_FP
  intro c
  simp only [Set.mem_ofPred_eq, decide_eq_true_eq, List.cons.injEq, and_true]

end LeanCanny.Encoding.BoundedSampleInterval
