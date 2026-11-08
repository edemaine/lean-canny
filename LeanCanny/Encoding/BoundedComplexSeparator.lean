/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedComplexPairQuery
public import LeanCanny.ETR.ComplexProjectionCollision

/-! # Native bounded separation of all complex critical samples

Collision tests compare both complex components on two independent copies of
the actual critical equations. A unary scan checks every spatial coordinate,
and bounded word search selects a polynomial-length integer projection record.
The existing critical-direction computation is charged in polynomial space.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedComplexSeparator
open LeanCanny.ETR LeanCanny.ETR.ComplexCircuit LeanCanny.Computation LeanCanny.Algebra
open BoundedFullWriter RealQuery.Interleaved LeanCanny.Encoding.Brackets Turing.MultiTapeTM
open BoundedFullComplexSamples (Good)
open scoped Classical BigOperators

noncomputable def collision (P : Readers) (record : List Bool → List Bool) (c : List Bool) (i : ℕ) : Prop :=
  ∃ x : ℕ → ℂ,
    BoundedComplexSampleQuery.Condition P (BoundedFullDirectionChoice.record P) c (x ∘ even) ∧
    BoundedComplexSampleQuery.Condition P (BoundedFullDirectionChoice.record P) c (x ∘ odd) ∧
    (ComplexProjectionCollision.formula (P.dim c + 4) (BoundedCriticalSeparator.weight P record c) i).Holds (realEnv x)

theorem projection_eq (P : Readers) (record : List Bool → List Bool) (c : List Bool)
    (x : ℕ → ℂ) (a : Fin (P.dim c + 4) → ℂ) (hx : ∀ i, x i.val = a i) :
    ComplexProjectionCollision.projection (P.dim c + 4) (BoundedCriticalSeparator.weight P record c) x =
      BoundedFullComplexSamples.value P record c a := by
  rw [ComplexProjectionCollision.projection, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [hx i, mul_comm]

theorem collision_iff (P : Readers) (record : List Bool → List Bool) (c : List Bool) (i : Fin (P.dim c + 4)) :
    collision P record c i.val ↔ ∃ a b : BoundedFullComplexSamples.Samples P c,
      BoundedFullComplexSamples.value P record c a.val = BoundedFullComplexSamples.value P record c b.val ∧ a.val i ≠ b.val i := by
  rw [collision, BoundedComplexPairQuery.selected_iff_samples]
  constructor
  · rintro ⟨a, b, x, ha, hb, hx⟩
    rw [ComplexProjectionCollision.formula_holds,
      projection_eq P record c (x ∘ even) a.val ha, projection_eq P record c (x ∘ odd) b.val hb] at hx
    exact ⟨a, b, hx.1, by simpa only [Function.comp_apply, ha i, hb i] using hx.2⟩
  · rintro ⟨a, b, he, hn⟩
    let x := RealQuery.Paired.merge (BoundedComplexSampleQuery.extend a.val) (BoundedComplexSampleQuery.extend b.val)
    have ha (j : Fin (P.dim c + 4)) : x (even j.val) = a.val j := by
      simp only [x, RealQuery.Paired.merge_even, BoundedComplexSampleQuery.extend_at]
    have hb (j : Fin (P.dim c + 4)) : x (odd j.val) = b.val j := by
      simp only [x, RealQuery.Paired.merge_odd, BoundedComplexSampleQuery.extend_at]
    refine ⟨a, b, x, ha, hb, ?_⟩
    rw [ComplexProjectionCollision.formula_holds,
      projection_eq P record c (x ∘ even) a.val ha, projection_eq P record c (x ∘ odd) b.val hb, ha i, hb i]
    exact ⟨he, hn⟩

noncomputable def check (P : Readers) (record : List Bool → List Bool) (c : List Bool) : List Bool :=
  [decide (∀ i < P.dim c + 4, ¬ collision P record c i)]

theorem check_correct (P : Readers) (record : List Bool → List Bool) (c : List Bool) :
    check P record c = [true] ↔ Good P c (record c) := by
  simp only [check, List.cons.injEq, and_true, decide_eq_true_eq]
  constructor
  · intro h a b hab
    apply Subtype.ext
    funext i
    by_contra hn
    exact h i.val i.isLt ((collision_iff P record c i).mpr ⟨a, b, hab, hn⟩)
  · intro h i hi hc
    obtain ⟨a, b, he, hn⟩ := (collision_iff P record c ⟨i, hi⟩).mp hc
    exact hn (congrArg (fun z : BoundedFullComplexSamples.Samples P c => z.val ⟨i, hi⟩) (h he))

def selected (P : Readers) (p : List Bool) : ℕ := min (pairSnd p).length (P.dim (pairFst p) + 3)
theorem selected_unary {P : Readers} (h : P.PolyTime) : UnaryFn (selected P) :=
  (UnaryFn.length pairSnd_mem_FP).min ((h.dim.comp pairFst_mem_FP).add (UnaryFn.const 3))
theorem selected_lt (P : Readers) (p : List Bool) : selected P p < P.dim (pairFst p) + 4 := by unfold selected; omega

noncomputable def collisionFlag (P : Readers) (record : List Bool → List Bool) (p : List Bool) : List Bool :=
  [decide (collision P record (pairFst p) (selected P p))]

theorem collision_evaluator {P : Readers} {record : List Bool → List Bool} (h : P.PolyTime) (hr : record ∈ FP)
    (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (collisionFlag P record) := by
  have hP := h.comp pairFst_mem_FP
  have hw := BoundedCriticalSeparator.weight_binary hP (mem_FP_comp pairFst_mem_FP hr)
  have hp := ComplexProjectionCollision.formula_FP (hP.dim.add (UnaryFn.const 4)) (selected_unary h) hw
  have E := BoundedComplexPairQuery.selected_evaluator hP hp (fun p => ht (pairFst p))
    (fun p => ComplexProjectionCollision.formula_scope _ _ _ (selected_lt P p))
  apply E.congr
  funext p
  apply congrArg List.singleton
  apply decide_eq_decide.mpr
  simp only [collision, BoundedComplexSampleQuery.Condition, BoundedFullDirectionChoice.record_comp]
  rfl

theorem check_evaluator {P : Readers} {record : List Bool → List Bool} (h : P.PolyTime) (hr : record ∈ FP)
    (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (check P record) := by
  have hn := (collision_evaluator h hr ht).postcompose _
    (stringEq_fppred id_mem_FP (constFn_mem_FP [true])).not.flag_mem_FP
  have H := hn.forall_unary (h.dim.add (UnaryFn.const 4))
  apply H.congr
  funext c
  simp only [check, collisionFlag, Function.comp_apply, id_eq, pairFst_pair, pairSnd_pair, List.length_replicate,
    List.cons.injEq, and_true, decide_eq_true_eq, selected]
  apply decide_eq_decide.mpr
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  rw [Nat.min_eq_left (by omega : i ≤ P.dim c + 3)]

noncomputable def test (P : Readers) (p : List Bool × List Bool) : Bool :=
  decide (check (P.comp pairFst) pairSnd (pair p.1 p.2) = [true])

noncomputable def record (P : Readers) : List Bool → List Bool :=
  ImplicitGraph.findWord (test P) (fun c => (P.dim c + 4) * BoundedCriticalSeparator.width P c)

theorem test_computable {P : Readers} (h : P.PolyTime) (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    ComputableInPolySpace (test P) (encPair encBits encBits) encBool := by
  have hc := check_evaluator (h.comp pairFst_mem_FP) pairSnd_mem_FP (fun p => ht (pairFst p))
  have hp := pair_computable (ComputableTidilyInPolyTime.fst encBits encBits) (ComputableTidilyInPolyTime.snd encBits encBits)
  have heq := (stringEq_fppred id_mem_FP (constFn_mem_FP [true])).computable
  have E := (ComputableInPolySpace.of_tidyPolyTime heq).comp (hc.computable.comp (.of_tidyPolyTime hp))
  apply E.congr
  intro p
  apply Bool.eq_iff_iff.mpr
  simp only [test, decide_eq_true_eq, id_eq]

theorem evaluator {P : Readers} (h : P.PolyTime) (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (record P) :=
  ⟨ImplicitGraph.findWord_computable (test_computable h ht) (BoundedCriticalSeparator.recordLength_unary h)⟩

theorem record_length (P : Readers) (c : List Bool) :
    (record P c).length = (P.dim c + 4) * BoundedCriticalSeparator.width P c := ImplicitGraph.findWord_length _ _ _

theorem test_correct (P : Readers) (c r : List Bool) : test P (c, r) = true ↔ Good P c r := by
  have hw : BoundedCriticalSeparator.weight (P.comp pairFst) pairSnd (pair c r) =
      BoundedCriticalSeparator.weight P (fun _ => r) c := by
    funext i
    simp only [BoundedCriticalSeparator.weight, FixedWidthQuery.coordinate, BoundedCriticalSeparator.width_comp, pairFst_pair, pairSnd_pair]
  have he : check (P.comp pairFst) pairSnd (pair c r) = check P (fun _ => r) c := by
    apply congrArg List.singleton
    apply decide_eq_decide.mpr
    simp only [collision, BoundedComplexSampleQuery.Condition, BoundedFullDirectionChoice.record_comp]
    rw [hw]
    simp only [Readers.comp, Function.comp_apply, pairFst_pair]
  simp only [test, decide_eq_true_eq, he, check_correct]

theorem test_comp (P : Readers) (f : List Bool → List Bool) (c r : List Bool) : test (P.comp f) (c, r) = test P (f c, r) := by
  have hw : BoundedCriticalSeparator.weight ((P.comp f).comp pairFst) pairSnd (pair c r) =
      BoundedCriticalSeparator.weight (P.comp pairFst) pairSnd (pair (f c) r) := by
    funext i
    simp only [BoundedCriticalSeparator.weight, FixedWidthQuery.coordinate, BoundedCriticalSeparator.width_comp, pairFst_pair, pairSnd_pair]
  apply Bool.eq_iff_iff.mpr
  simp only [test, decide_eq_true_eq, check, List.cons.injEq, and_true, collision, BoundedComplexSampleQuery.Condition,
    BoundedFullDirectionChoice.record_comp]
  rw [hw]
  simp only [Readers.comp, Function.comp_apply, pairFst_pair]

@[simp] theorem record_comp (P : Readers) (f : List Bool → List Bool) (c : List Bool) : record (P.comp f) c = record P (f c) := by
  unfold record
  apply ImplicitGraph.findWord_congr (c := c) (c' := f c)
    (width := fun z => ((P.comp f).dim z + 4) * BoundedCriticalSeparator.width (P.comp f) z)
    (width' := fun z => (P.dim z + 4) * BoundedCriticalSeparator.width P z) rfl
  exact test_comp P f c

theorem record_good (P : Readers) (c : List Bool) : Good P c (record P c) := by
  apply (test_correct P c _).mp
  apply ImplicitGraph.findWord_correct
  obtain ⟨r, hr, hg⟩ := BoundedFullComplexSamples.exists_record P c
  exact ⟨r, hr, (test_correct P c r).mpr hg⟩

theorem record_good_real (P : Readers) (c : List Bool) : BoundedCriticalSeparator.Good P c (record P c) :=
  BoundedFullComplexSamples.good_real P c _ (record_good P c)

theorem value_injective (P : Readers) (c : List Bool) :
    Function.Injective (fun x : BoundedFullComplexSamples.Samples P c => BoundedFullComplexSamples.value P (record P) c x.val) :=
  record_good P c

theorem selected_pair_evaluator {P : Readers} {p : List Bool → Formula} (h : P.PolyTime)
    (hp : (fun c => (p c).encode) ∈ FP) (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c)
    (hs : ∀ z, (p z).arity ≤ 4 * (P.dim (pairFst z) + 4)) :
    SpaceFunction (fun c => [decide (∃ x : ℕ → ℂ,
      BoundedComplexSampleQuery.Condition P (BoundedFullDirectionChoice.record P) c (x ∘ even) ∧
        BoundedComplexSampleQuery.Condition P (BoundedFullDirectionChoice.record P) c (x ∘ odd) ∧
          (p (pair c (record P c))).Holds (realEnv x))]) := by
  have E := BoundedComplexPairQuery.selected_evaluator (h.comp pairFst_mem_FP) hp (fun z => ht (pairFst z)) hs
  have H : SpaceFunction _ := ⟨E.computable.comp (evaluator h ht).withInput.computable⟩
  apply H.congr
  funext c
  apply congrArg List.singleton
  apply decide_eq_decide.mpr
  simp only [BoundedComplexSampleQuery.Condition]
  simp only [BoundedFullDirectionChoice.record_comp]
  simp only [Readers.comp, Function.comp_apply, pairFst_pair]

end LeanCanny.Encoding.BoundedComplexSeparator
