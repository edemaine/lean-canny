/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexInterleavedQuery

/-! # Two independent real circuit queries

Parity copies separate every wire of the two circuits. An outer interleaved
query leaves further formula witnesses independent of both copies. The finite
input tuple alternates the left and right spatial coordinates.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.RealQuery.Paired
open Interleaved LeanCanny.Computation LeanCanny.Encoding.Brackets
open scoped Classical

def merge {α : Type*} (a b : ℕ → α) (i : ℕ) : α := if i % 2 = 0 then a (i / 2) else b (i / 2)

theorem merge_even {α : Type*} (a b : ℕ → α) (i : ℕ) : merge a b (even i) = a i := by
  simp [merge, even, Nat.mul_comm]

theorem merge_odd {α : Type*} (a b : ℕ → α) (i : ℕ) : merge a b (odd i) = b i := by
  have hm : (2 * i + 1) % 2 = 1 := by omega
  have hd : (2 * i + 1) / 2 = i := by omega
  simp only [merge, odd, hm, one_ne_zero, ite_false, hd]

def gates (left right : List Gate) : List Gate :=
  left.map (Gate.reindex even) ++ right.map (Gate.reindex odd)

theorem realizes_iff (n start : ℕ) (left right : List Gate) (x : ℕ → ℝ) :
    PortRealizes (2 * n) (2 * start) id (gates left right) x ↔
      PortRealizes n start id left (x ∘ even) ∧ PortRealizes n start id right (x ∘ odd) := by
  constructor
  · rintro ⟨env, hg, hr, hi⟩
    refine ⟨⟨fun i => env (even i), ?_, ?_, ?_⟩, ⟨fun i => env (odd i), ?_, ?_, ?_⟩⟩
    · intro g h
      exact (Gate.reindex_holds even g env).mp
        (hg _ (List.mem_append_left _ (List.mem_map.mpr ⟨g, h, rfl⟩)))
    · intro i h
      exact hr (even i) (by unfold even; omega)
    · intro i h
      exact hi (even i) (by unfold even; omega)
    · intro g h
      exact (Gate.reindex_holds odd g env).mp
        (hg _ (List.mem_append_right _ (List.mem_map.mpr ⟨g, h, rfl⟩)))
    · intro i h
      exact hr (odd i) (by unfold odd; omega)
    · intro i h
      exact hi (odd i) (by unfold odd; omega)
  · rintro ⟨⟨a, ha, hra, hia⟩, ⟨b, hb, hrb, hib⟩⟩
    simp only [id_eq, Function.comp_apply] at hia hib
    refine ⟨merge a b, ?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · obtain ⟨base, hbase, rfl⟩ := List.mem_map.mp hg
        apply (Gate.reindex_holds even base (merge a b)).mpr
        simpa only [merge_even] using ha base hbase
      · obtain ⟨base, hbase, rfl⟩ := List.mem_map.mp hg
        apply (Gate.reindex_holds odd base (merge a b)).mpr
        simpa only [merge_odd] using hb base hbase
    · intro i hi
      have hq : i / 2 < start := by omega
      unfold merge
      split_ifs
      · exact hra _ hq
      · exact hrb _ hq
    · intro i hi
      have hq : i / 2 < n := by omega
      change merge a b i = (x i : ℂ)
      by_cases hm : i % 2 = 0
      · have he : even (i / 2) = i := by unfold even; omega
        rw [← he, merge_even, hia _ hq]
      · have he : odd (i / 2) = i := by unfold odd; omega
        rw [← he, merge_odd, hib _ hq]

theorem satisfiable_iff (n start : ℕ) (left right : List Gate) (p : Formula) :
    InputSatisfiable (2 * n) (2 * start) (gates left right) p ↔
      ∃ x : ℕ → ℝ, (PortRealizes n start id left (x ∘ even) ∧
        PortRealizes n start id right (x ∘ odd)) ∧ p.Holds x := by
  rw [InputSatisfiable, portSatisfiable_iff]
  apply exists_congr
  intro x
  exact and_congr (realizes_iff n start left right x) Iff.rfl

theorem encode_mem_FP {left right : List Bool → List Gate}
    (hl : (fun c => encode (left c)) ∈ FP) (hr : (fun c => encode (right c)) ∈ FP) :
    (fun c => encode (gates (left c) (right c))) ∈ FP := by
  have hi := (UnaryFn.const 2).mul (UnaryFn.length pairSnd_mem_FP)
  have he := Reindex.encode_mem_FP (index := fun _ => even) hi (constFn_mem_FP []) hl
  have ho := Reindex.encode_mem_FP (index := fun _ => odd) (hi.add (UnaryFn.const 1)) (constFn_mem_FP []) hr
  have h := mem_FP_comp (appendFn_mem_FP (mem_FP_comp he contents_mem_FP)
    (mem_FP_comp ho contents_mem_FP)) wrap_mem_FP
  apply mem_FP_of_eq h
  intro c
  simp only [Function.comp_apply, contents_encode]
  simp only [gates, encode_eq_wrap, forest_append]

theorem arity (left right : List Gate) (fresh : ℕ)
    (hl : ∀ g ∈ left, g.arity ≤ fresh) (hr : ∀ g ∈ right, g.arity ≤ fresh) :
    ∀ g ∈ gates left right, g.arity ≤ 2 * fresh := by
  intro g hg
  rcases List.mem_append.mp hg with hg | hg
  · obtain ⟨base, hbase, rfl⟩ := List.mem_map.mp hg
    have h := hl base hbase
    cases base <;> simp only [Gate.reindex, Gate.arity, even] at * <;> omega
  · obtain ⟨base, hbase, rfl⟩ := List.mem_map.mp hg
    have h := hr base hbase
    cases base <;> simp only [Gate.reindex, Gate.arity, odd] at * <;> omega

end LeanCanny.ETR.ComplexCircuit.RealQuery.Paired
