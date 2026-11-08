/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalPairQuery
public import LeanCanny.ETR.ProjectionCollisionFP
public import LeanCanny.Algebra.AffineGridAvoidance

/-! # Bounded separating projections of the actual critical samples

The finite sample bound gives polynomially many bits per weight. A native
pair query detects collisions, and bounded search retains a separating word.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalSeparator
open LeanCanny.ETR LeanCanny.ETR.ComplexCircuit LeanCanny.Computation LeanCanny.Algebra
open BoundedFullWriter RealQuery.Interleaved LeanCanny.Encoding.Brackets Turing.MultiTapeTM
open scoped Classical BigOperators

noncomputable def width (P : Readers) (c : List Bool) : ℕ :=
  2 * BoundedFullCriticalSamples.labelWidth P c + 1

noncomputable def weight (P : Readers) (record : List Bool → List Bool) (c : List Bool) : ℕ → ℕ :=
  FixedWidthQuery.coordinate (width P) record c

theorem width_comp (P : Readers) (f : List Bool → List Bool) (c : List Bool) :
    width (P.comp f) c = width P (f c) := rfl

noncomputable def value (P : Readers) (record : List Bool → List Bool) (c : List Bool)
    (x : Fin (P.dim c + 4) → ℝ) : ℝ := ∑ i, x i * (weight P record c i.val : ℝ)

noncomputable def Good (P : Readers) (c r : List Bool) : Prop :=
  Function.Injective (fun x : BoundedFullCriticalSamples.Samples P c => value P (fun _ => r) c x.val)

theorem width_unary {P : Readers} (h : P.PolyTime) : UnaryFn (width P) :=
  ((UnaryFn.const 2).mul (BoundedFullCriticalSamples.labelWidth_unary h)).add (UnaryFn.const 1)

theorem recordLength_unary {P : Readers} (h : P.PolyTime) :
    UnaryFn (fun c => (P.dim c + 4) * width P c) :=
  (h.dim.add (UnaryFn.const 4)).mul (width_unary h)

theorem weight_binary {P : Readers} {record : List Bool → List Bool}
    (h : P.PolyTime) (hr : record ∈ FP) :
    BinaryFn (fun p => weight P record (pairFst p) (pairSnd p).length) := by
  have hw := (width_unary h).comp pairFst_mem_FP
  exact BinaryFn.fromBits (take_mem_FP (drop_mem_FP (mem_FP_comp pairFst_mem_FP hr)
    ((UnaryFn.length pairSnd_mem_FP).mul hw)) hw)

theorem exists_record (P : Readers) (c : List Bool) :
    ∃ r, r.length = (P.dim c + 4) * width P c ∧ Good P c r := by
  let : Finite (BoundedFullCriticalSamples.Samples P c) := (BoundedFullCriticalSamples.finite_samples P c).1
  let := Fintype.ofFinite (BoundedFullCriticalSamples.Samples P c)
  obtain ⟨v, hv, hinj⟩ := AffineGridAvoidance.exists_bounded_separating_direction
    (fun _ : Unit => fun x : BoundedFullCriticalSamples.Samples P c => x.val)
    (fun _ _ => (0 : ℝ)) (fun _ => Subtype.val_injective)
  have hcard : Fintype.card (BoundedFullCriticalSamples.Samples P c) ≤
      2 ^ BoundedFullCriticalSamples.labelWidth P c := by
    simpa only [Nat.card_eq_fintype_card] using (BoundedFullCriticalSamples.finite_samples P c).2
  have hfit (i : Fin (P.dim c + 4)) : v i < 2 ^ width P c := by
    have hi : v i ≤ Fintype.card (BoundedFullCriticalSamples.Samples P c) ^ 2 := by
      simpa only [Fintype.card_unit, one_mul] using hv i
    calc
      v i ≤ (2 ^ BoundedFullCriticalSamples.labelWidth P c) ^ 2 := hi.trans (Nat.pow_le_pow_left hcard 2)
      _ = 2 ^ (2 * BoundedFullCriticalSamples.labelWidth P c) := by rw [← pow_mul, Nat.mul_comm]
      _ < 2 ^ width P c := by unfold width; exact Nat.pow_lt_pow_right (by decide) (by omega)
  let e : ℕ → ℕ := fun i => if hi : i < P.dim c + 4 then v ⟨i, hi⟩ else 0
  let r := FixedWidthNatVector.encode (P.dim c + 4) (width P c) e
  have hw (i : Fin (P.dim c + 4)) : weight P (fun _ => r) c i.val = v i := by
    change Nat.fromBitsLE ((r.drop (i.val * width P c)).take (width P c)) = v i
    rw [FixedWidthNatVector.decode_block _ _ e i.val i.isLt]
    · simp only [e, dite_eq_left i.isLt]
    · simpa only [e, dite_eq_left i.isLt] using hfit i
  refine ⟨r, FixedWidthNatVector.length_encode _ _ _, ?_⟩
  simpa only [Good, value, hw, zero_add] using hinj ()

noncomputable def collision (P : Readers) (record : List Bool → List Bool) (c : List Bool) (i : ℕ) : Prop :=
  ∃ x : ℕ → ℝ,
    BoundedCriticalSampleQuery.Condition P (BoundedFullDirectionChoice.record P) c (x ∘ even) ∧
    BoundedCriticalSampleQuery.Condition P (BoundedFullDirectionChoice.record P) c (x ∘ odd) ∧
    (ProjectionCollision.formula (P.dim c + 4) (weight P record c) i).Holds x

private theorem projection_eq (P : Readers) (record : List Bool → List Bool) (c : List Bool)
    (x : ℕ → ℝ) (a : Fin (P.dim c + 4) → ℝ) (hx : ∀ i, x i.val = a i) :
    ProjectionCollision.projection (P.dim c + 4) (weight P record c) x = value P record c a := by
  rw [ProjectionCollision.projection, ← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [hx i, mul_comm]

private def extend {n : ℕ} (a : Fin n → ℝ) (i : ℕ) : ℝ := if hi : i < n then a ⟨i, hi⟩ else 0

private theorem extend_at {n : ℕ} (a : Fin n → ℝ) (i : Fin n) : extend a i.val = a i := by
  simp only [extend, dite_eq_left i.isLt]

theorem collision_iff (P : Readers) (record : List Bool → List Bool) (c : List Bool)
    (i : Fin (P.dim c + 4)) :
    collision P record c i.val ↔ ∃ a b : BoundedFullCriticalSamples.Samples P c,
      value P record c a.val = value P record c b.val ∧ a.val i ≠ b.val i := by
  rw [collision, BoundedCriticalPairQuery.selected_iff_samples]
  constructor
  · rintro ⟨a, b, x, ha, hb, hx⟩
    rw [ProjectionCollision.formula_holds,
      projection_eq P record c (x ∘ even) a.val ha,
      projection_eq P record c (x ∘ odd) b.val hb] at hx
    exact ⟨a, b, hx.1, by simpa only [ha i, hb i] using hx.2⟩
  · rintro ⟨a, b, he, hn⟩
    let x := RealQuery.Paired.merge (extend a.val) (extend b.val)
    have ha (j : Fin (P.dim c + 4)) : x (even j.val) = a.val j := by
      simp only [x, RealQuery.Paired.merge_even, extend_at]
    have hb (j : Fin (P.dim c + 4)) : x (odd j.val) = b.val j := by
      simp only [x, RealQuery.Paired.merge_odd, extend_at]
    refine ⟨a, b, x, ha, hb, ?_⟩
    rw [ProjectionCollision.formula_holds,
      projection_eq P record c (x ∘ even) a.val ha,
      projection_eq P record c (x ∘ odd) b.val hb, ha i, hb i]
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
    exact hn (congrArg (fun z : BoundedFullCriticalSamples.Samples P c => z.val ⟨i, hi⟩) (h he))

noncomputable def collisionFlag (P : Readers) (record : List Bool → List Bool) (p : List Bool) : List Bool :=
  [decide (collision P record (pairFst p) (pairSnd p).length)]

theorem collision_evaluator {P : Readers} {record : List Bool → List Bool}
    (h : P.PolyTime) (hr : record ∈ FP)
    (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (collisionFlag P record) := by
  have hP := h.comp pairFst_mem_FP
  have hw := weight_binary hP (mem_FP_comp pairFst_mem_FP hr)
  have hp := ProjectionCollision.formula_mem_FP (hP.dim.add (UnaryFn.const 4))
    (UnaryFn.length pairSnd_mem_FP) hw
  have he := BoundedCriticalPairQuery.selected_evaluator hP hp (fun p => ht (pairFst p))
  apply he.congr
  funext p
  apply congrArg List.singleton
  apply decide_eq_decide.mpr
  simp only [collision, BoundedCriticalSampleQuery.Condition]
  simp only [BoundedFullDirectionChoice.record_comp]
  rfl

theorem check_evaluator {P : Readers} {record : List Bool → List Bool}
    (h : P.PolyTime) (hr : record ∈ FP)
    (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (check P record) := by
  have hn := (collision_evaluator h hr ht).postcompose _
    (stringEq_fppred id_mem_FP (constFn_mem_FP [true])).not.flag_mem_FP
  have hs := hn.forall_unary (h.dim.add (UnaryFn.const 4))
  apply hs.congr
  funext c
  simp only [check, collisionFlag, Function.comp_apply, id_eq, pairFst_pair, pairSnd_pair,
    List.length_replicate, List.cons.injEq, and_true, decide_eq_true_eq]

theorem check_comp (P : Readers) (record f : List Bool → List Bool) (c : List Bool) :
    check (P.comp f) (record ∘ f) c = check P record (f c) := by
  simp only [check, collision, BoundedCriticalSampleQuery.Condition]
  simp only [BoundedFullDirectionChoice.record_comp]
  rfl

noncomputable def test (P : Readers) (p : List Bool × List Bool) : Bool :=
  decide (check (P.comp pairFst) pairSnd (pair p.1 p.2) = [true])

noncomputable def record (P : Readers) : List Bool → List Bool :=
  ImplicitGraph.findWord (test P) (fun c => (P.dim c + 4) * width P c)

theorem test_computable {P : Readers} (h : P.PolyTime)
    (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    Turing.MultiTapeTM.ComputableInPolySpace (test P)
      (Turing.MultiTapeTM.encPair Turing.MultiTapeTM.encBits Turing.MultiTapeTM.encBits)
      Turing.MultiTapeTM.encBool := by
  have hc := check_evaluator (h.comp pairFst_mem_FP) pairSnd_mem_FP (fun p => ht (pairFst p))
  have hp := pair_computable (ComputableTidilyInPolyTime.fst encBits encBits)
    (ComputableTidilyInPolyTime.snd encBits encBits)
  have heq := (stringEq_fppred id_mem_FP (constFn_mem_FP [true])).computable
  have he := (ComputableInPolySpace.of_tidyPolyTime heq).comp (hc.computable.comp (.of_tidyPolyTime hp))
  apply he.congr
  intro p
  apply Bool.eq_iff_iff.mpr
  simp only [test, decide_eq_true_eq, id_eq]

theorem evaluator {P : Readers} (h : P.PolyTime)
    (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (record P) :=
  ⟨ImplicitGraph.findWord_computable (test_computable h ht) (recordLength_unary h)⟩

theorem record_length (P : Readers) (c : List Bool) :
    (record P c).length = (P.dim c + 4) * width P c :=
  ImplicitGraph.findWord_length _ _ _

theorem test_correct (P : Readers) (c r : List Bool) : test P (c, r) = true ↔ Good P c r := by
  have hw : weight (P.comp pairFst) pairSnd (pair c r) = weight P (fun _ => r) c := by
    funext i
    simp only [weight, FixedWidthQuery.coordinate, width_comp, pairFst_pair, pairSnd_pair]
  have he : check (P.comp pairFst) pairSnd (pair c r) = check P (fun _ => r) c := by
    apply congrArg List.singleton
    apply decide_eq_decide.mpr
    simp only [collision, BoundedCriticalSampleQuery.Condition]
    simp only [BoundedFullDirectionChoice.record_comp]
    rw [hw]
    simp only [Readers.comp, Function.comp_apply, pairFst_pair]
  simp only [test, decide_eq_true_eq, he, check_correct]

theorem test_comp (P : Readers) (f : List Bool → List Bool) (c r : List Bool) :
    test (P.comp f) (c, r) = test P (f c, r) := by
  have hw : weight ((P.comp f).comp pairFst) pairSnd (pair c r) =
      weight (P.comp pairFst) pairSnd (pair (f c) r) := by
    funext i
    simp only [weight, FixedWidthQuery.coordinate, width_comp, pairFst_pair, pairSnd_pair]
  apply Bool.eq_iff_iff.mpr
  simp only [test, decide_eq_true_eq, check, List.cons.injEq, and_true,
    collision, BoundedCriticalSampleQuery.Condition]
  simp only [BoundedFullDirectionChoice.record_comp]
  rw [hw]
  simp only [Readers.comp, Function.comp_apply, pairFst_pair]

@[simp] theorem record_comp (P : Readers) (f : List Bool → List Bool) (c : List Bool) :
    record (P.comp f) c = record P (f c) := by
  unfold record
  apply ImplicitGraph.findWord_congr (c := c) (c' := f c)
    (width := fun z => ((P.comp f).dim z + 4) * width (P.comp f) z)
    (width' := fun z => (P.dim z + 4) * width P z) rfl
  exact test_comp P f c

theorem record_good (P : Readers) (c : List Bool) : Good P c (record P c) := by
  apply (test_correct P c _).mp
  apply ImplicitGraph.findWord_correct
  obtain ⟨r, hr, hg⟩ := exists_record P c
  exact ⟨r, hr, (test_correct P c r).mpr hg⟩

/-- Equality of the selected projection recovers the entire critical sample. -/
theorem value_injective (P : Readers) (c : List Bool) :
    Function.Injective (fun x : BoundedFullCriticalSamples.Samples P c => value P (record P) c x.val) :=
  record_good P c

/-- A formula writer receives the selected weights as a binary packet. Both
direction selection and separator selection are charged before the pair query. -/
theorem selected_pair_evaluator {P : Readers} {p : List Bool → Formula}
    (h : P.PolyTime) (hp : (fun c => (p c).encode) ∈ FP)
    (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun c => [decide (∃ x : ℕ → ℝ,
      BoundedCriticalSampleQuery.Condition P (BoundedFullDirectionChoice.record P) c (x ∘ even) ∧
      BoundedCriticalSampleQuery.Condition P (BoundedFullDirectionChoice.record P) c (x ∘ odd) ∧
      (p (pair c (record P c))).Holds x)]) := by
  have hc := BoundedCriticalPairQuery.selected_evaluator (h.comp pairFst_mem_FP) hp
    (fun z => ht (pairFst z))
  have he : SpaceFunction _ := ⟨hc.computable.comp (evaluator h ht).withInput.computable⟩
  apply he.congr
  funext c
  apply congrArg List.singleton
  apply decide_eq_decide.mpr
  simp only [BoundedCriticalSampleQuery.Condition]
  simp only [BoundedFullDirectionChoice.record_comp]
  simp only [Readers.comp, Function.comp_apply, pairFst_pair]

end LeanCanny.Encoding.BoundedCriticalSeparator
