/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleQuery
public import LeanCanny.ETR.ComplexPairedQuery

/-! # Native queries relating two independent critical samples

The two complete sample circuits occupy separate parity wire families.
The constraint formula sees alternating spatial coordinates and may introduce
further independent real witnesses. The actual direction selector is charged
once before the native pair query is run.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalPairQuery
open LeanCanny.ETR LeanCanny.ETR.ComplexCircuit LeanCanny.Computation
open BoundedFullWriter RealQuery.Interleaved
open scoped Classical

noncomputable def query (P : Readers) (record : List Bool → List Bool) (c : List Bool) : List Gate :=
  RealQuery.Paired.gates (BoundedCriticalSampleQuery.query P record c) (BoundedCriticalSampleQuery.query P record c)

theorem correct (P : Readers) (record : List Bool → List Bool) (c : List Bool) (p : Formula)
    (ht : (TermView.term (P.source c)).arity ≤ P.dim c) :
    InputSatisfiable (2 * (P.dim c + 4)) (2 * BoundedCriticalSampleQuery.frame P c) (query P record c) p ↔
      ∃ x : ℕ → ℝ, BoundedCriticalSampleQuery.Condition P record c (x ∘ even) ∧
        BoundedCriticalSampleQuery.Condition P record c (x ∘ odd) ∧ p.Holds x := by
  rw [query, RealQuery.Paired.satisfiable_iff]
  apply exists_congr
  intro x
  rw [BoundedCriticalSampleQuery.realizes_correct P record c (x ∘ even) ht,
    BoundedCriticalSampleQuery.realizes_correct P record c (x ∘ odd) ht]
  exact and_assoc

theorem evaluator {P : Readers} {record : List Bool → List Bool} {p : List Bool → Formula}
    (h : P.PolyTime) (hr : record ∈ FP) (hp : (fun c => (p c).encode) ∈ FP)
    (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun c => [decide (∃ x : ℕ → ℝ,
      BoundedCriticalSampleQuery.Condition P record c (x ∘ even) ∧
      BoundedCriticalSampleQuery.Condition P record c (x ∘ odd) ∧ (p c).Holds x)]) := by
  have hframe := BoundedCriticalSampleQuery.frame_unary h
  have hfresh := hframe.add (BoundedCriticalSampleQuery.length_unary (record := record) h)
  have hq := BoundedCriticalSampleQuery.query_encode_mem_FP h hr
  have hencode : (fun c => encode (query P record c)) ∈ FP := RealQuery.Paired.encode_mem_FP hq hq
  have ha (c) : ∀ g ∈ BoundedCriticalSampleQuery.query P record c,
      g.arity ≤ BoundedCriticalSampleQuery.frame P c + (BoundedCriticalSampleQuery.program P record c).length := by
    intro g hg
    rw [BoundedCriticalSampleQuery.query_eq_models] at hg
    exact zeroGates_arity _ _ _ (BoundedCriticalSampleQuery.wellFormed P record c)
      (BoundedCriticalSampleQuery.models_bound P record c) g hg
  have he := RealQuery.Interleaved.evaluator
    ((UnaryFn.const 2).mul (h.dim.add (UnaryFn.const 4))) ((UnaryFn.const 2).mul hframe)
    ((UnaryFn.const 2).mul hfresh) hencode hp
    (fun c => by unfold BoundedCriticalSampleQuery.frame CriticalKernel.zeroWire; omega)
    (fun c => by omega) (fun c => RealQuery.Paired.arity _ _ _ (ha c) (ha c))
  apply he.congr
  funext c
  rw [correct P record c (p c) (ht c)]

theorem selected_evaluator {P : Readers} {p : List Bool → Formula} (h : P.PolyTime)
    (hp : (fun c => (p c).encode) ∈ FP) (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun c => [decide (∃ x : ℕ → ℝ,
      BoundedCriticalSampleQuery.Condition P (BoundedFullDirectionChoice.record P) c (x ∘ even) ∧
      BoundedCriticalSampleQuery.Condition P (BoundedFullDirectionChoice.record P) c (x ∘ odd) ∧ (p c).Holds x)]) := by
  have hc := evaluator (h.comp pairFst_mem_FP) pairSnd_mem_FP (mem_FP_comp pairFst_mem_FP hp)
    (fun z => ht (pairFst z))
  have he : SpaceFunction _ := ⟨hc.computable.comp (BoundedFullDirectionChoice.evaluator h ht).withInput.computable⟩
  apply he.congr
  funext c
  apply congrArg List.singleton
  apply decide_eq_decide.mpr
  simp only [BoundedCriticalSampleQuery.Condition, Readers.comp, Function.comp_apply, pairFst_pair, pairSnd_pair]

def Matches (P : Readers) (c : List Bool) (p : Formula)
    (a b : BoundedFullCriticalSamples.Samples P c) : Prop :=
  ∃ x : ℕ → ℝ, (∀ i : Fin (P.dim c + 4), x (even i.val) = a.val i) ∧
    (∀ i : Fin (P.dim c + 4), x (odd i.val) = b.val i) ∧ p.Holds x

theorem selected_iff_samples (P : Readers) (c : List Bool) (p : Formula) :
    (∃ x : ℕ → ℝ, BoundedCriticalSampleQuery.Condition P (BoundedFullDirectionChoice.record P) c (x ∘ even) ∧
      BoundedCriticalSampleQuery.Condition P (BoundedFullDirectionChoice.record P) c (x ∘ odd) ∧ p.Holds x) ↔
      ∃ a b : BoundedFullCriticalSamples.Samples P c, Matches P c p a b := by
  constructor
  · rintro ⟨x, ha, hb, hp⟩
    refine ⟨⟨fun i => x (even i.val), (BoundedCriticalSampleQuery.selected_condition P c (x ∘ even)).mp ha⟩,
      ⟨fun i => x (odd i.val), (BoundedCriticalSampleQuery.selected_condition P c (x ∘ odd)).mp hb⟩,
      x, fun _ => rfl, fun _ => rfl, hp⟩
  · rintro ⟨a, b, x, ha, hb, hp⟩
    refine ⟨x, (BoundedCriticalSampleQuery.selected_condition P c (x ∘ even)).mpr ?_,
      (BoundedCriticalSampleQuery.selected_condition P c (x ∘ odd)).mpr ?_, hp⟩
    · change ∀ j, (BoundedFullCriticalSamples.equations P c j).eval₂ (Int.castRingHom ℝ)
        (fun i => x (even i.val)) = 0
      rw [funext ha]
      exact a.property
    · change ∀ j, (BoundedFullCriticalSamples.equations P c j).eval₂ (Int.castRingHom ℝ)
        (fun i => x (odd i.val)) = 0
      rw [funext hb]
      exact b.property

theorem samples_evaluator {P : Readers} {p : List Bool → Formula} (h : P.PolyTime)
    (hp : (fun c => (p c).encode) ∈ FP) (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun c => [decide (∃ a b : BoundedFullCriticalSamples.Samples P c, Matches P c (p c) a b)]) := by
  apply (selected_evaluator h hp ht).congr
  funext c
  rw [selected_iff_samples]

end LeanCanny.Encoding.BoundedCriticalPairQuery
