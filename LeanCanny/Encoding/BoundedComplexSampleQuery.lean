/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalSampleQuery
public import LeanCanny.Encoding.BoundedFullComplexSamples
public import LeanCanny.ETR.ComplexRealifiedQuery

/-! # Native Boolean queries on the complete complex critical sample set

The same shared derivative circuit is used without a real-input restriction.
Formula coordinates expose both parts of the spatial inputs. Completing the
acyclic circuit preserves those coordinates. The selected direction is charged
as a polynomial-space computation, rather than assumed to have an FP reader.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedComplexSampleQuery
open LeanCanny.ETR LeanCanny.ETR.ComplexCircuit LeanCanny.Computation MvPolynomial
open BoundedFullWriter
open scoped Classical

noncomputable def conditionData (source : List Bool) (dim radius : ℕ) (r : List Bool) (x : ℕ → ℂ) : Prop :=
  let P : Readers := ⟨fun _ => source, fun _ => dim, fun _ => radius⟩
  ∀ j, (BoundedCriticalSampleQuery.equations P (fun _ => r) [] j).eval₂ (Int.castRingHom ℂ) (fun i => x i.val) = 0

noncomputable def Condition (P : Readers) (record : List Bool → List Bool) (c : List Bool) (x : ℕ → ℂ) : Prop :=
  conditionData (P.source c) (P.dim c) (P.radius c) (record c) x

theorem condition_iff (P : Readers) (record : List Bool → List Bool) (c : List Bool) (x : ℕ → ℂ) :
    Condition P record c x ↔ ∀ j, (BoundedCriticalSampleQuery.equations P record c j).eval₂
      (Int.castRingHom ℂ) (fun i => x i.val) = 0 := Iff.rfl

theorem correct (P : Readers) (record : List Bool → List Bool) (c : List Bool) (p : Formula)
    (ht : (TermView.term (P.source c)).arity ≤ P.dim c) (hp : p.arity ≤ 2 * (P.dim c + 4)) :
    RealifiedQuery.WithConstraints (BoundedCriticalSampleQuery.query P record c) p ↔
      ∃ x : ℕ → ℂ, Condition P record c x ∧ p.Holds (realEnv x) := by
  rw [BoundedCriticalSampleQuery.query_eq_models]
  let start := BoundedCriticalSampleQuery.frame P c
  let ops := BoundedCriticalSampleQuery.program P record c
  have hw := BoundedCriticalSampleQuery.wellFormed P record c
  have ho := BoundedCriticalSampleQuery.models_bound P record c
  have hm := BoundedCriticalSampleQuery.models_identity P record c ht
  constructor
  · rintro ⟨env, hg, hpred⟩
    have hg' : ∀ g ∈ StraightLine.gates start ops, g.Holds env := fun g h => hg g (List.mem_append_left _ h)
    refine ⟨env, (condition_iff P record c env).mpr ?_, hpred⟩
    intro j
    let z := (CriticalSamples.output (BoundedFullWriter.start P c) (P.dim c + 4) (BoundedFullWriter.program P c) j.val,
      BoundedCriticalSampleQuery.equations P record c j)
    have hz : z ∈ BoundedCriticalSampleQuery.models P record c := List.mem_ofFn.mpr ⟨j, rfl⟩
    have he := StraightLine.symbolic_value env start ops hw hg' env (fun _ _ => rfl) z.1 (ho z hz)
    rw [hm z hz, eval₂_rename] at he
    exact he.symm.trans (hg (.zero z.1) (List.mem_append_right _ (List.mem_map.mpr ⟨z, hz, rfl⟩)))
  · rintro ⟨x, hx, hpred⟩
    let env := StraightLine.run x start ops
    have hg : ∀ g ∈ StraightLine.gates start ops, g.Holds env := StraightLine.run_satisfies x start ops hw
    have hi : ∀ i < start, env i = x i := fun i h => StraightLine.run_preserves_before x start ops i h
    refine ⟨env, ?_, (p.holds_congr (realEnv x) (realEnv env) ?_).mp hpred⟩
    · intro g hgmem
      rcases List.mem_append.mp hgmem with hgmem | hgmem
      · exact hg g hgmem
      · obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hgmem
        obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hz
        change env (CriticalSamples.output _ _ _ j.val) = 0
        rw [StraightLine.symbolic_value env start ops hw hg x hi _ (ho _ (List.mem_ofFn.mpr ⟨j, rfl⟩)),
          hm _ (List.mem_ofFn.mpr ⟨j, rfl⟩), eval₂_rename]
        exact (condition_iff P record c x).mp hx j
    · intro i hip
      have hframe : P.dim c + 4 ≤ start := by
        dsimp [start, BoundedCriticalSampleQuery.frame, CriticalKernel.zeroWire]
        omega
      have he := hi (i / 2) (by omega)
      simp only [realEnv, he]

theorem evaluator {P : Readers} {record : List Bool → List Bool} {p : List Bool → Formula}
    (h : P.PolyTime) (hr : record ∈ FP) (hp : (fun c => (p c).encode) ∈ FP)
    (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) (hscope : ∀ c, (p c).arity ≤ 2 * (P.dim c + 4)) :
    SpaceFunction (fun c => [decide (∃ x : ℕ → ℂ, Condition P record c x ∧ (p c).Holds (realEnv x))]) := by
  have E := RealifiedQuery.evaluator (BoundedCriticalSampleQuery.query_encode_mem_FP h hr) hp
  apply E.congr
  funext c
  rw [correct P record c (p c) (ht c) (hscope c)]

theorem selected_evaluator {P : Readers} {p : List Bool → Formula} (h : P.PolyTime)
    (hp : (fun c => (p c).encode) ∈ FP) (ht : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c)
    (hscope : ∀ c, (p c).arity ≤ 2 * (P.dim c + 4)) :
    SpaceFunction (fun c => [decide (∃ x : ℕ → ℂ,
      Condition P (BoundedFullDirectionChoice.record P) c x ∧ (p c).Holds (realEnv x))]) := by
  have E := evaluator (h.comp pairFst_mem_FP) pairSnd_mem_FP (mem_FP_comp pairFst_mem_FP hp)
    (fun z => ht (pairFst z)) (fun z => hscope (pairFst z))
  have H : SpaceFunction _ := ⟨E.computable.comp (BoundedFullDirectionChoice.evaluator h ht).withInput.computable⟩
  apply H.congr
  funext c
  apply congrArg List.singleton
  apply decide_eq_decide.mpr
  simp only [Condition, Readers.comp, Function.comp_apply, pairFst_pair, pairSnd_pair]

theorem selected_condition (P : Readers) (c : List Bool) (x : ℕ → ℂ) :
    Condition P (BoundedFullDirectionChoice.record P) c x ↔
      ∀ j, (BoundedFullCriticalSamples.equations P c j).eval₂ (Int.castRingHom ℂ) (fun i => x i.val) = 0 := Iff.rfl

def extend {n : ℕ} (x : Fin n → ℂ) (i : ℕ) : ℂ := if hi : i < n then x ⟨i, hi⟩ else 0

theorem extend_at {n : ℕ} (x : Fin n → ℂ) (i : Fin n) : extend x i.val = x i := by
  simp only [extend, i.isLt, dite_true, Fin.eta]

theorem realEnv_congr_prefix {n : ℕ} (x y : ℕ → ℂ) (h : ∀ i, i < n → x i = y i)
    (i : ℕ) (hi : i < 2 * n) : realEnv x i = realEnv y i := by
  have he := h (i / 2) (by omega)
  simp only [realEnv, he]

theorem selected_iff_samples (P : Readers) (c : List Bool) (p : Formula) (hp : p.arity ≤ 2 * (P.dim c + 4)) :
    (∃ x : ℕ → ℂ, Condition P (BoundedFullDirectionChoice.record P) c x ∧ p.Holds (realEnv x)) ↔
      ∃ x : BoundedFullComplexSamples.Samples P c, p.Holds (realEnv (extend x.val)) := by
  constructor
  · rintro ⟨x, hx, hpred⟩
    let a : BoundedFullComplexSamples.Samples P c := ⟨fun i => x i.val, (selected_condition P c x).mp hx⟩
    refine ⟨a, (p.holds_congr (realEnv x) (realEnv (extend a.val)) ?_).mp hpred⟩
    intro i hi
    apply realEnv_congr_prefix x (extend a.val) ?_ i (hi.trans_le hp)
    intro j hj
    simp only [extend, hj, dite_true, a]
  · rintro ⟨x, hpred⟩
    refine ⟨extend x.val, (selected_condition P c _).mpr ?_, hpred⟩
    simpa only [extend_at] using x.property

end LeanCanny.Encoding.BoundedComplexSampleQuery
