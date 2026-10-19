/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.SubroutineIteration

/-!
# Intermediate states and workspace of suspended iteration

Every physical iterate is either an abstract parent state at its expanded
clock or a child state during one requested call. The saved parent and live
child give the explicit bit bound `2*S + U + 3`. The wrapper's halting test
accepts only parent states, so child computations cannot signal parent
completion prematurely.
-/

@[expose] public section

namespace LeanCanny.Computation.SubroutineIteration
open Complexity

theorem iterate_requested (P : Program) (T : List Bool → ℕ) (p : List Bool)
    (hr : P.request p = true) (hT : TerminatesAt P p (T p)) (t : ℕ) (ht : t ≤ T p) :
    (step P)^[t + 1] (parent p) = child p (P.advance^[t] (P.start p)) := by
  rw [Function.iterate_succ_apply, step_parent, hr]
  simpa using iterate_child P p (T p) hT t ht

theorem iterate_operation_inside (P : Program) (T : List Bool → ℕ) (p : List Bool)
    (hT : P.request p = true → TerminatesAt P p (T p)) (t : ℕ) (ht : t < cost P T p) :
    (t = 0 ∧ (step P)^[t] (parent p) = parent p) ∨
      ∃ j, j ≤ T p ∧ P.request p = true ∧ t = j + 1 ∧
        (step P)^[t] (parent p) = child p (P.advance^[j] (P.start p)) := by
  by_cases hz : t = 0
  · exact Or.inl ⟨hz, by simp [hz]⟩
  · right
    by_cases hr : P.request p = true
    · have hj : t - 1 ≤ T p := by simp only [cost, hr, ↓reduceIte] at ht; omega
      refine ⟨t - 1, hj, hr, by omega, ?_⟩
      rw [show t = (t - 1) + 1 by omega]
      exact iterate_requested P T p hr (hT hr) _ hj
    · simp only [cost, hr, Bool.false_eq_true, ↓reduceIte] at ht
      omega

theorem iterate_prefix (P : Program) (T : List Bool → ℕ) (p : List Bool) (N t : ℕ)
    (hT : ∀ k, k < N → P.request ((abstractStep P T)^[k] p) = true →
      TerminatesAt P ((abstractStep P T)^[k] p) (T ((abstractStep P T)^[k] p)))
    (ht : t ≤ clock P T p N) :
    (∃ k, k ≤ N ∧ t = clock P T p k ∧
      (step P)^[t] (parent p) = parent ((abstractStep P T)^[k] p)) ∨
    ∃ k, k < N ∧ ∃ j, j ≤ T ((abstractStep P T)^[k] p) ∧
      P.request ((abstractStep P T)^[k] p) = true ∧
      t = j + 1 + clock P T p k ∧
      (step P)^[t] (parent p) = child ((abstractStep P T)^[k] p)
        (P.advance^[j] (P.start ((abstractStep P T)^[k] p))) := by
  induction N generalizing t with
  | zero =>
      have hz : t = 0 := by simp only [clock] at ht; omega
      exact Or.inl ⟨0, le_rfl, hz, by simp [hz]⟩
  | succ N ih =>
      by_cases htN : t ≤ clock P T p N
      · rcases ih t (by intro k hk; exact hT k (by omega)) htN with hp | hc
        · obtain ⟨k, hk, he, hs⟩ := hp
          exact Or.inl ⟨k, by omega, he, hs⟩
        · obtain ⟨k, hk, j, hj, hr, he, hs⟩ := hc
          exact Or.inr ⟨k, by omega, j, hj, hr, he, hs⟩
      · by_cases he : t = clock P T p (N + 1)
        · exact Or.inl ⟨N + 1, le_rfl, he, he ▸ iterate_clock P T p (N + 1) hT⟩
        · have hlocal : t - clock P T p N < cost P T ((abstractStep P T)^[N] p) := by
            rw [clock] at ht he
            omega
          have hs : (step P)^[t] (parent p) =
              (step P)^[t - clock P T p N] (parent ((abstractStep P T)^[N] p)) := by
            calc
              _ = (step P)^[(t - clock P T p N) + clock P T p N] (parent p) :=
                congrArg (fun j => (step P)^[j] (parent p)) (by omega)
              _ = _ := by
                rw [Function.iterate_add_apply,
                  iterate_clock P T p N (by intro k hk; exact hT k (by omega))]
          rcases iterate_operation_inside P T ((abstractStep P T)^[N] p)
            (hT N (by omega)) _ hlocal with hz | hc
          · have := hz.1
            omega
          · obtain ⟨j, hj, hr, hjtime, hjstate⟩ := hc
            exact Or.inr ⟨N, by omega, j, hj, hr, by omega, hs.trans hjstate⟩

theorem iterate_length_le (P : Program) (T : List Bool → ℕ) (p : List Bool) (N S U : ℕ)
    (hT : ∀ k, k < N → P.request ((abstractStep P T)^[k] p) = true →
      TerminatesAt P ((abstractStep P T)^[k] p) (T ((abstractStep P T)^[k] p)))
    (hp : ∀ k, k ≤ N → ((abstractStep P T)^[k] p).length ≤ S)
    (hu : ∀ k, k < N → P.request ((abstractStep P T)^[k] p) = true →
      ∀ j, j ≤ T ((abstractStep P T)^[k] p) →
        (P.advance^[j] (P.start ((abstractStep P T)^[k] p))).length ≤ U)
    (t : ℕ) (ht : t ≤ clock P T p N) :
    ((step P)^[t] (parent p)).length ≤ 2 * S + U + 3 := by
  rcases iterate_prefix P T p N t hT ht with hparent | hchild
  · obtain ⟨k, hk, _, hs⟩ := hparent
    rw [hs]
    have h := hp k hk
    simp only [parent, List.length_cons]
    omega
  · obtain ⟨k, hk, j, hj, hr, _, hs⟩ := hchild
    rw [hs]
    have hparent := hp k (by omega)
    have hchild := hu k hk hr j hj
    simp only [child, List.length_cons, pair_length]
    omega

def halted (H : List Bool → Bool) (bits : List Bool) : Bool :=
  if bits[0]?.getD false = true then false else H (bits.drop 1)

theorem halted_mem_FP {H : List Bool → Bool} (hH : (fun p => [H p]) ∈ FP) :
    (fun bits => [halted H bits]) ∈ FP := by
  have hbody := mem_FP_comp (drop_mem_FP id_mem_FP (UnaryFn.const 1)) hH
  have h := (FPPred.getBit id_mem_FP (UnaryFn.const 0)).ite_mem_FP (constFn_mem_FP [false]) hbody
  exact mem_FP_of_eq h (fun bits => by
    simp only [halted, id_eq, Function.comp_apply]
    split_ifs <;> rfl)

@[simp] theorem halted_parent (H : List Bool → Bool) (p : List Bool) :
    halted H (parent p) = H p := by simp [halted, parent]

@[simp] theorem halted_child (H : List Bool → Bool) (p u : List Bool) :
    halted H (child p u) = false := by simp [halted, child]

theorem halted_before (P : Program) (T : List Bool → ℕ) (p : List Bool) (N : ℕ)
    (hT : ∀ k, k < N → P.request ((abstractStep P T)^[k] p) = true →
      TerminatesAt P ((abstractStep P T)^[k] p) (T ((abstractStep P T)^[k] p)))
    (H : List Bool → Bool) (hH : ∀ k, k < N → H ((abstractStep P T)^[k] p) = false)
    (t : ℕ) (ht : t < clock P T p N) : halted H ((step P)^[t] (parent p)) = false := by
  rcases iterate_prefix P T p N t hT ht.le with hp | hc
  · obtain ⟨k, hk, he, hs⟩ := hp
    have hklt : k < N := by
      by_contra hn
      have : k = N := by omega
      subst k
      omega
    rw [hs, halted_parent, hH k hklt]
  · obtain ⟨k, _, j, _, _, _, hs⟩ := hc
    rw [hs, halted_child]

end LeanCanny.Computation.SubroutineIteration
