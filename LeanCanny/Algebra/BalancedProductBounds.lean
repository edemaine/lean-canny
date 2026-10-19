/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BalancedProductMachine
public import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Linarith

/-!
# Live-query and stack bounds for balanced product bits

Every child decreases the tree height. Node addresses stay within the root
tree, and every requested bit stays below the root index. Thus the stack has
at most the root height many frames, with short binary query/counter fields.
-/

@[expose] public section

namespace LeanCanny.Algebra.BalancedProduct

def Frame.parent : Frame → Query
  | .left q _ _ | .right q _ _ _ => q

def Frame.time : Frame → ℕ
  | .left _ t _ | .right _ t _ _ => t

def Frame.accumulator : Frame → ℕ
  | .left _ _ acc | .right _ _ acc _ => acc

def QueryFits (H K : ℕ) (q : Query) : Prop :=
  q.height ≤ H ∧ q.index ≤ K ∧ q.node < 2 ^ (H - q.height)

theorem query_left_fits (H K : ℕ) (q : Query) (t : ℕ) (hq : QueryFits H K q) (ht : Active q t) :
    QueryFits H K (q.left t) := by
  obtain ⟨hh, hk, hn⟩ := hq
  obtain ⟨hhp, htime, hpos⟩ := ht
  have he : H - (q.height - 1) = H - q.height + 1 := by omega
  refine ⟨(Nat.sub_le _ _).trans hh, ?_, ?_⟩
  · change position q.index t ≤ K
    unfold count at hpos
    omega
  · change 2 * q.node < 2 ^ (H - (q.height - 1))
    rw [he, pow_succ]
    omega

theorem query_right_fits (H K : ℕ) (q : Query) (t : ℕ) (hq : QueryFits H K q) (ht : Active q t) :
    QueryFits H K (q.right t) := by
  obtain ⟨hh, hk, hn⟩ := hq
  obtain ⟨hhp, htime, hpos⟩ := ht
  have he : H - (q.height - 1) = H - q.height + 1 := by omega
  refine ⟨(Nat.sub_le _ _).trans hh, ?_, ?_⟩
  · change column q.index t - position q.index t ≤ K
    exact (Nat.sub_le _ _).trans ((column_le q.index t htime.le).trans hk)
  · change 2 * q.node + 1 < 2 ^ (H - (q.height - 1))
    rw [he, pow_succ]
    omega

inductive StackFits (H K : ℕ) : ℕ → List Frame → Prop where
  | nil {h : ℕ} (bound : h ≤ H) : StackFits H K h []
  | cons {h : ℕ} {f : Frame} {stack : List Frame}
      (height : h < f.parent.height) (query : QueryFits H K f.parent) (active : Active f.parent f.time)
      (tail : StackFits H K f.parent.height stack) : StackFits H K h (f :: stack)

theorem StackFits.mono {H K h l : ℕ} {stack : List Frame}
    (hs : StackFits H K h stack) (hl : l ≤ h) : StackFits H K l stack := by
  cases hs with
  | nil hb => exact .nil (hl.trans hb)
  | cons hh hq ht hs => exact .cons (hl.trans_lt hh) hq ht hs

theorem StackFits.length_le {H K h : ℕ} {stack : List Frame}
    (hs : StackFits H K h stack) : h + stack.length ≤ H := by
  induction hs with
  | nil hb => simpa only [List.length_nil, Nat.add_zero] using hb
  | cons hh _ _ _ ih => simp only [List.length_cons]; omega

theorem StackFits.parents {H K h : ℕ} {stack : List Frame} (hs : StackFits H K h stack) :
    ∀ f ∈ stack, QueryFits H K f.parent ∧ Active f.parent f.time := by
  induction hs with
  | nil _ => simp
  | cons hh hq ht hs ih =>
    intro f hf
    rcases List.mem_cons.mp hf with rfl | hf
    · exact ⟨hq, ht⟩
    · exact ih f hf

def Fits (H K : ℕ) : State → Prop
  | .eval q stack => QueryFits H K q ∧ StackFits H K q.height stack
  | .scan q t _ stack => QueryFits H K q ∧ 0 < q.height ∧ t ≤ limit q.index ∧ StackFits H K q.height stack
  | .ret _ stack => StackFits H K 0 stack
  | .done _ => True

theorem step_fits (a : ℕ → ℕ) (H K : ℕ) (s : State) (hs : Fits H K s) : Fits H K (step a s) := by
  cases s with
  | eval q stack =>
    obtain ⟨hq, hs⟩ := hs
    by_cases hh : q.height = 0
    · simpa only [step, hh, ↓reduceIte, Fits] using hs.mono (Nat.zero_le _)
    · simpa only [step, hh, ↓reduceIte, Fits] using And.intro hq ⟨by omega, Nat.zero_le _, hs⟩
  | scan q t acc stack =>
    obtain ⟨hq, hh, ht, hs⟩ := hs
    by_cases hend : limit q.index ≤ t
    · simpa only [step, hend, ↓reduceIte, Fits] using hs.mono (Nat.zero_le _)
    · by_cases hi : position q.index t < count q.index
      · have hactive : Active q t := ⟨hh, by omega, hi⟩
        simp only [step, hend, hi, ↓reduceIte, Fits]
        exact ⟨query_left_fits H K q t hq hactive,
          .cons (by simp only [Query.left, Frame.parent]; omega) hq hactive hs⟩
      · simp only [step, hend, hi, ↓reduceIte, Fits]
        exact ⟨hq, hh, by omega, hs⟩
  | ret x stack =>
    cases stack with
    | nil => trivial
    | cons f stack =>
      cases hs with
      | cons hh hq ht hs =>
        cases f with
        | left q t acc =>
          simp only [Frame.parent, Frame.time] at hq ht hs
          simp only [step, Fits]
          exact ⟨query_right_fits H K q t hq ht,
            .cons (by simp only [Query.right, Frame.parent]; have := ht.1; omega) hq ht hs⟩
        | right q t acc lhs =>
          simp only [Frame.parent, Frame.time] at hq ht hs
          simp only [step, Fits]
          exact ⟨hq, ht.1, by have := ht.2.1; omega, hs⟩
  | done _ => trivial

theorem iterate_fits (a : ℕ → ℕ) (H K : ℕ) (s : State) (hs : Fits H K s) (t : ℕ) :
    Fits H K ((step a)^[t] s) := by
  induction t with
  | zero => exact hs
  | succ t ih => rw [Function.iterate_succ_apply']; exact step_fits a H K _ ih

def start (H K : ℕ) : State := .eval ⟨H, 0, K⟩ []

theorem start_fits (H K : ℕ) : Fits H K (start H K) := by
  exact ⟨⟨le_rfl, le_rfl, by simp⟩, .nil le_rfl⟩

theorem start_correct (a : ℕ → ℕ) (H K : ℕ) : Correct a ((tree a H 0).testBit K) (start H K) := rfl

theorem limit_mono {k K : ℕ} (hk : k ≤ K) : limit k ≤ limit K := by
  have he := Nat.mul_le_mul hk (Nat.add_le_add_right hk 2)
  unfold limit width count
  omega

theorem query_node_size {H K : ℕ} {q : Query} (hq : QueryFits H K q) : q.node.size ≤ H :=
  Nat.size_le.mpr (hq.2.2.trans_le (Nat.pow_le_pow_right (by decide) (Nat.sub_le H q.height)))

theorem query_index_size {H K : ℕ} {q : Query} (hq : QueryFits H K q) : q.index.size ≤ K.size :=
  Nat.size_le_size hq.2.1

end LeanCanny.Algebra.BalancedProduct
