/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexInfinityCircuit
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Exact semantics of shared infinity-chart networks -/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.Infinity
open scoped Classical BigOperators

theorem power_sound (m : ℕ) (bits : List Bool) (v : ℕ → ℤ) (k : ℕ) (env : ℕ → ℂ)
    (h : ∀ g ∈ prefixGates m bits v k, g.Holds env) (j : ℕ) (hj : j < k) :
    env (powerWire m bits j) = env j ^ Nat.fromBitsLE bits := by
  apply Power.sound j (start m bits j) bits env
  intro g hg
  apply h g
  apply block_mem_prefix m bits v k j hj g
  exact List.mem_append_left _ hg

theorem block_sum_sound (m : ℕ) (bits : List Bool) (v : ℕ → ℤ) (j : ℕ) (env : ℕ → ℂ)
    (h : ∀ g ∈ blockGates m bits v j, g.Holds env) :
    env (sumWire m bits (j + 1)) = env (sumWire m bits j) + env j ^ (Nat.fromBitsLE bits + 1) := by
  have hp : env (powerWire m bits j) = env j ^ Nat.fromBitsLE bits := by
    apply Power.sound j (start m bits j) bits env
    intro g hg
    exact h g (List.mem_append_left _ hg)
  have hm := h (.mul (powerWire m bits j + 1) (powerWire m bits j) j) (by simp [blockGates])
  have ha := h (.add (sumWire m bits (j + 1)) (sumWire m bits j) (powerWire m bits j + 1)) (by simp [blockGates])
  simp only [Gate.Holds] at hm ha
  rw [ha, hm, hp, pow_succ]

theorem sum_sound (m : ℕ) (bits : List Bool) (v : ℕ → ℤ) (k : ℕ) (env : ℕ → ℂ)
    (h : ∀ g ∈ prefixGates m bits v k, g.Holds env) :
    env (sumWire m bits k) = ∑ j ∈ Finset.range k, env j ^ (Nat.fromBitsLE bits + 1) := by
  induction k with
  | zero =>
    have hc := h (.constant m 0) (by simp [prefixGates_zero])
    simpa only [Gate.Holds, Int.cast_zero, sumWire, Finset.sum_range_zero] using hc
  | succ k ih =>
    have hp : ∀ g ∈ prefixGates m bits v k, g.Holds env := by
      intro g hg
      exact h g (by rw [prefixGates_succ]; exact List.mem_append_left _ hg)
    have hb : ∀ g ∈ blockGates m bits v k, g.Holds env := by
      intro g hg
      exact h g (by rw [prefixGates_succ]; exact List.mem_append_right _ hg)
    rw [block_sum_sound m bits v k env hb, ih hp, Finset.sum_range_succ]

theorem difference_sound (m : ℕ) (bits : List Bool) (v : ℕ → ℤ) (k : ℕ) (env : ℕ → ℂ)
    (h : ∀ g ∈ prefixGates m bits v k, g.Holds env) (hk : 0 < k) (j : ℕ) (hj : j < k) :
    env (differenceWire m bits j) = env j ^ Nat.fromBitsLE bits - (v j : ℂ) * env 0 ^ Nat.fromBitsLE bits := by
  have hb : ∀ g ∈ blockGates m bits v j, g.Holds env :=
    fun g hg => h g (block_mem_prefix m bits v k j hj g hg)
  have hc := hb (.constant (powerWire m bits j + 3) (-v j)) (by simp [blockGates])
  have hm := hb (.mul (powerWire m bits j + 4) (powerWire m bits j + 3) (powerWire m bits 0)) (by simp [blockGates])
  have ha := hb (.add (differenceWire m bits j) (powerWire m bits j) (powerWire m bits j + 4)) (by simp [blockGates])
  simp only [Gate.Holds, Int.cast_neg] at hc hm ha
  rw [ha, hm, hc, power_sound m bits v k env h j hj, power_sound m bits v k env h 0 hk]
  ring

def query (m : ℕ) (bits : List Bool) (v : ℕ → ℤ) (i : ℕ) : List Gate :=
  [.constant i 1] ++ prefixGates m bits v m ++ [.zero (sumWire m bits m)] ++
    (List.range (m - 1)).map (fun j => .zero (differenceWire m bits (j + 1)))

theorem prefix_mem_query (m : ℕ) (bits : List Bool) (v : ℕ → ℤ) (i : ℕ) (g : Gate)
    (hg : g ∈ prefixGates m bits v m) : g ∈ query m bits v i :=
  List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hg))

theorem difference_mem_query (m : ℕ) (bits : List Bool) (v : ℕ → ℤ) (i j : ℕ)
    (hj0 : 0 < j) (hjm : j < m) : .zero (differenceWire m bits j) ∈ query m bits v i := by
  apply List.mem_append_right
  apply List.mem_map.mpr
  refine ⟨j - 1, List.mem_range.mpr (by omega), ?_⟩
  rw [Nat.sub_add_cancel (by omega : 1 ≤ j)]

theorem query_satisfiable (m : ℕ) (hm : 0 < m) (bits : List Bool) (v : ℕ → ℤ)
    (i : ℕ) (hi : i < m) : Satisfiable (query m bits v i) ↔
    ∃ x : ℕ → ℂ, x i = 1 ∧ (∑ j ∈ Finset.range m, x j ^ (Nat.fromBitsLE bits + 1)) = 0 ∧
      ∀ j, 0 < j → j < m → x j ^ Nat.fromBitsLE bits - (v j : ℂ) * x 0 ^ Nat.fromBitsLE bits = 0 := by
  constructor
  · rintro ⟨env, h⟩
    have hp : ∀ g ∈ prefixGates m bits v m, g.Holds env :=
      fun g hg => h g (prefix_mem_query m bits v i g hg)
    have hn := h (.constant i 1) (by simp [query])
    have hz := h (.zero (sumWire m bits m)) (by simp [query])
    refine ⟨env, ?_, (sum_sound m bits v m env hp).symm.trans hz, ?_⟩
    · simpa only [Gate.Holds, Int.cast_one] using hn
    · intro j hj0 hjm
      have hj := h (.zero (differenceWire m bits j)) (difference_mem_query m bits v i j hj0 hjm)
      exact (difference_sound m bits v m env hp hm j hjm).symm.trans hj
  · rintro ⟨x, hx, hs, hd⟩
    obtain ⟨env, hp, hg⟩ := StraightLine.exists_completion x m (prefixProgram m bits v m)
      (wellFormed m bits v m le_rfl)
    have hsum : env (sumWire m bits m) = 0 := by
      rw [sum_sound m bits v m env hg]
      have he : (∑ j ∈ Finset.range m, env j ^ (Nat.fromBitsLE bits + 1)) =
          ∑ j ∈ Finset.range m, x j ^ (Nat.fromBitsLE bits + 1) :=
        Finset.sum_congr rfl (fun j hj => congrArg (· ^ (Nat.fromBitsLE bits + 1)) (hp j (Finset.mem_range.mp hj)))
      exact he.trans hs
    have hdiff (j : ℕ) (hj0 : 0 < j) (hjm : j < m) : env (differenceWire m bits j) = 0 := by
      rw [difference_sound m bits v m env hg hm j hjm, hp j hjm, hp 0 hm]
      exact hd j hj0 hjm
    refine ⟨env, ?_⟩
    intro g hmem
    simp only [query, List.mem_append, List.mem_singleton] at hmem
    rcases hmem with ((rfl | ha) | rfl) | hdiffmem
    · simpa only [Gate.Holds, Int.cast_one] using (hp i hi).trans hx
    · exact hg g ha
    · exact hsum
    · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hdiffmem
      have hjm : j + 1 < m := by have := List.mem_range.mp hj; omega
      exact hdiff (j + 1) (by omega) hjm

end LeanCanny.ETR.ComplexCircuit.Infinity
