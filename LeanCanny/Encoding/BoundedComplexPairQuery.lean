/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedComplexSampleQuery
public import LeanCanny.ETR.ComplexPairedQuery

/-! # Native constraints on two independent complex critical samples

Parity copies retain the complete complex values of both samples. Formula
variables read the real and imaginary parts of their alternating input wires.
Both copies use the actual source and selected critical direction.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedComplexSampleQuery
open LeanCanny.ETR LeanCanny.ETR.ComplexCircuit LeanCanny.Computation MvPolynomial BoundedFullWriter

theorem holds_condition (P : Readers) (record : List Bool → List Bool) (c : List Bool)
    (ht : (TermView.term (P.source c)).arity ≤ P.dim c) (env : ℕ → ℂ)
    (hg : ∀ g ∈ BoundedCriticalSampleQuery.query P record c, g.Holds env) : Condition P record c env := by
  rw [BoundedCriticalSampleQuery.query_eq_models] at hg
  let frame := BoundedCriticalSampleQuery.frame P c
  let ops := BoundedCriticalSampleQuery.program P record c
  have hw := BoundedCriticalSampleQuery.wellFormed P record c
  have ho := BoundedCriticalSampleQuery.models_bound P record c
  have hm := BoundedCriticalSampleQuery.models_identity P record c ht
  have hg' : ∀ g ∈ StraightLine.gates frame ops, g.Holds env := fun g h => hg g (List.mem_append_left _ h)
  apply (condition_iff P record c env).mpr
  intro j
  let z := (CriticalSamples.output (start P c) (P.dim c + 4) (BoundedFullWriter.program P c) j.val,
    BoundedCriticalSampleQuery.equations P record c j)
  have hz : z ∈ BoundedCriticalSampleQuery.models P record c := List.mem_ofFn.mpr ⟨j, rfl⟩
  have he := StraightLine.symbolic_value env frame ops hw hg' env (fun _ _ => rfl) z.1 (ho z hz)
  rw [hm z hz, eval₂_rename] at he
  exact he.symm.trans (hg (.zero z.1) (List.mem_append_right _ (List.mem_map.mpr ⟨z, hz, rfl⟩)))

theorem completion (P : Readers) (record : List Bool → List Bool) (c : List Bool)
    (ht : (TermView.term (P.source c)).arity ≤ P.dim c) (x : ℕ → ℂ) (hx : Condition P record c x) :
    ∃ env : ℕ → ℂ, (∀ g ∈ BoundedCriticalSampleQuery.query P record c, g.Holds env) ∧
      ∀ i, i < P.dim c + 4 → env i = x i := by
  let frame := BoundedCriticalSampleQuery.frame P c
  let ops := BoundedCriticalSampleQuery.program P record c
  let env := StraightLine.run x frame ops
  have hw := BoundedCriticalSampleQuery.wellFormed P record c
  have ho := BoundedCriticalSampleQuery.models_bound P record c
  have hm := BoundedCriticalSampleQuery.models_identity P record c ht
  have hg : ∀ g ∈ StraightLine.gates frame ops, g.Holds env := StraightLine.run_satisfies x frame ops hw
  have hi : ∀ i < frame, env i = x i := fun i h => StraightLine.run_preserves_before x frame ops i h
  refine ⟨env, ?_, fun i h => hi i ?_⟩
  · rw [BoundedCriticalSampleQuery.query_eq_models]
    intro g hgmem
    rcases List.mem_append.mp hgmem with hgmem | hgmem
    · exact hg g hgmem
    · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hgmem
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hz
      change env (CriticalSamples.output _ _ _ j.val) = 0
      rw [StraightLine.symbolic_value env frame ops hw hg x hi _ (ho _ (List.mem_ofFn.mpr ⟨j, rfl⟩)),
        hm _ (List.mem_ofFn.mpr ⟨j, rfl⟩), eval₂_rename]
      exact (condition_iff P record c x).mp hx j
  · dsimp [frame, BoundedCriticalSampleQuery.frame, CriticalKernel.zeroWire]
    omega

end LeanCanny.Encoding.BoundedComplexSampleQuery

namespace LeanCanny.Encoding.BoundedComplexPairQuery
open LeanCanny.ETR LeanCanny.ETR.ComplexCircuit LeanCanny.Computation BoundedFullWriter
open RealQuery.Interleaved
open scoped Classical

noncomputable def query (P : Readers) (record : List Bool → List Bool) (c : List Bool) : List Gate :=
  RealQuery.Paired.gates (BoundedCriticalSampleQuery.query P record c) (BoundedCriticalSampleQuery.query P record c)

theorem paired_holds (left right : List Gate) (env : ℕ → ℂ) :
    (∀ g ∈ RealQuery.Paired.gates left right, g.Holds env) ↔
      (∀ g ∈ left, g.Holds (env ∘ even)) ∧ ∀ g ∈ right, g.Holds (env ∘ odd) := by
  simp only [RealQuery.Paired.gates, List.forall_mem_append, List.forall_mem_map, Gate.reindex_holds, Function.comp_def]

theorem correct (P : Readers) (record : List Bool → List Bool) (c : List Bool) (p : Formula)
    (ht : (TermView.term (P.source c)).arity ≤ P.dim c) (hp : p.arity ≤ 4 * (P.dim c + 4)) :
    RealifiedQuery.WithConstraints (query P record c) p ↔ ∃ x : ℕ → ℂ,
      BoundedComplexSampleQuery.Condition P record c (x ∘ even) ∧
        BoundedComplexSampleQuery.Condition P record c (x ∘ odd) ∧ p.Holds (realEnv x) := by
  constructor
  · rintro ⟨env, hg, hpred⟩
    obtain ⟨ha, hb⟩ := (paired_holds _ _ env).mp hg
    exact ⟨env, BoundedComplexSampleQuery.holds_condition P record c ht _ ha,
      BoundedComplexSampleQuery.holds_condition P record c ht _ hb, hpred⟩
  · rintro ⟨x, ha, hb, hpred⟩
    obtain ⟨a, hga, hia⟩ := BoundedComplexSampleQuery.completion P record c ht (x ∘ even) ha
    obtain ⟨b, hgb, hib⟩ := BoundedComplexSampleQuery.completion P record c ht (x ∘ odd) hb
    let env := RealQuery.Paired.merge a b
    refine ⟨env, (paired_holds _ _ env).mpr ⟨?_, ?_⟩, (p.holds_congr (realEnv x) (realEnv env) ?_).mp hpred⟩
    · simpa only [env, Function.comp_def, RealQuery.Paired.merge_even] using hga
    · simpa only [env, Function.comp_def, RealQuery.Paired.merge_odd] using hgb
    · intro i hi
      apply BoundedComplexSampleQuery.realEnv_congr_prefix (n := 2 * (P.dim c + 4)) x env ?_ i (by omega)
      intro j hj
      have hq : j / 2 < P.dim c + 4 := by omega
      by_cases hm : j % 2 = 0
      · have he : even (j / 2) = j := by unfold even; omega
        simp only [env, RealQuery.Paired.merge, hm, ite_true, hia _ hq, Function.comp_apply, he]
      · have he : odd (j / 2) = j := by unfold odd; omega
        simp only [env, RealQuery.Paired.merge, hm, ite_false, hib _ hq, Function.comp_apply, he]

theorem evaluator {P : Readers} {record : List Bool → List Bool} {p : List Bool → Formula}
    (h : P.PolyTime) (hr : record ∈ FP) (hp : (fun c => (p c).encode) ∈ FP)
    (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (hs : ∀ c, (p c).arity ≤ 4 * (P.dim c + 4)) :
    SpaceFunction (fun c => [decide (∃ x : ℕ → ℂ,
      BoundedComplexSampleQuery.Condition P record c (x ∘ even) ∧
        BoundedComplexSampleQuery.Condition P record c (x ∘ odd) ∧ (p c).Holds (realEnv x))]) := by
  have hq := BoundedCriticalSampleQuery.query_encode_mem_FP h hr
  have E := RealifiedQuery.evaluator (RealQuery.Paired.encode_mem_FP hq hq) hp
  apply E.congr
  funext c
  apply congrArg List.singleton
  exact decide_eq_decide.mpr (correct P record c (p c) (ht c) (hs c))

theorem selected_evaluator {P : Readers} {p : List Bool → Formula} (h : P.PolyTime)
    (hp : (fun c => (p c).encode) ∈ FP) (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c)
    (hs : ∀ c, (p c).arity ≤ 4 * (P.dim c + 4)) :
    SpaceFunction (fun c => [decide (∃ x : ℕ → ℂ,
      BoundedComplexSampleQuery.Condition P (BoundedFullDirectionChoice.record P) c (x ∘ even) ∧
        BoundedComplexSampleQuery.Condition P (BoundedFullDirectionChoice.record P) c (x ∘ odd) ∧ (p c).Holds (realEnv x))]) := by
  have E := evaluator (h.comp pairFst_mem_FP) pairSnd_mem_FP (mem_FP_comp pairFst_mem_FP hp)
    (fun z => ht (pairFst z)) (fun z => hs (pairFst z))
  have H : SpaceFunction _ := ⟨E.computable.comp (BoundedFullDirectionChoice.evaluator h ht).withInput.computable⟩
  apply H.congr
  funext c
  apply congrArg List.singleton
  apply decide_eq_decide.mpr
  simp only [BoundedComplexSampleQuery.Condition, Readers.comp, Function.comp_apply, pairFst_pair, pairSnd_pair]

def Matches (P : Readers) (c : List Bool) (p : Formula) (a b : BoundedFullComplexSamples.Samples P c) : Prop :=
  ∃ x : ℕ → ℂ, (∀ i : Fin (P.dim c + 4), x (even i.val) = a.val i) ∧
    (∀ i : Fin (P.dim c + 4), x (odd i.val) = b.val i) ∧ p.Holds (realEnv x)

theorem selected_iff_samples (P : Readers) (c : List Bool) (p : Formula) :
    (∃ x : ℕ → ℂ, BoundedComplexSampleQuery.Condition P (BoundedFullDirectionChoice.record P) c (x ∘ even) ∧
      BoundedComplexSampleQuery.Condition P (BoundedFullDirectionChoice.record P) c (x ∘ odd) ∧ p.Holds (realEnv x)) ↔
        ∃ a b : BoundedFullComplexSamples.Samples P c, Matches P c p a b := by
  constructor
  · rintro ⟨x, ha, hb, hp⟩
    exact ⟨⟨fun i => x (even i.val), (BoundedComplexSampleQuery.selected_condition P c _).mp ha⟩,
      ⟨fun i => x (odd i.val), (BoundedComplexSampleQuery.selected_condition P c _).mp hb⟩,
      x, fun _ => rfl, fun _ => rfl, hp⟩
  · rintro ⟨a, b, x, ha, hb, hp⟩
    refine ⟨x, (BoundedComplexSampleQuery.selected_condition P c _).mpr ?_,
      (BoundedComplexSampleQuery.selected_condition P c _).mpr ?_, hp⟩
    · simpa only [Function.comp_apply, ha] using a.property
    · simpa only [Function.comp_apply, hb] using b.property

end LeanCanny.Encoding.BoundedComplexPairQuery
