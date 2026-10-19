/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MatrixPowerWork

/-!
# Bounds on the live matrix-power continuation stack

Parent heights strictly increase from the top frame to the bottom frame.
Every reachable state therefore has at most the initial height many frames.
All exponents stay below the initial exponent; all indices belong to `Fin n`.
Scalar representation and arithmetic costs are separate from these invariants.
-/

@[expose] public section

namespace LeanCanny.Algebra.MatrixPower

variable {R : Type*} {n : ℕ}

def Frame.parent : Frame R n → Query n
  | .left q _ _ => q
  | .right q _ _ _ => q

inductive StackFits (H : ℕ) : ℕ → List (Frame R n) → Prop where
  | nil {h : ℕ} (bound : h ≤ H) : StackFits H h []
  | cons {h : ℕ} {f : Frame R n} {stack : List (Frame R n)}
      (height : h < f.parent.height) (tail : StackFits H f.parent.height stack) :
      StackFits H h (f :: stack)

theorem StackFits.mono {H h l : ℕ} {stack : List (Frame R n)}
    (hs : StackFits H h stack) (hl : l ≤ h) : StackFits H l stack := by
  cases hs with
  | nil hb => exact .nil (hl.trans hb)
  | cons hh ht => exact .cons (hl.trans_lt hh) ht

theorem StackFits.length_le {H h : ℕ} {stack : List (Frame R n)}
    (hs : StackFits H h stack) : h + stack.length ≤ H := by
  induction hs with
  | nil hb => simpa only [List.length_nil, Nat.add_zero] using hb
  | cons hh ht ih => simp only [List.length_cons]; omega

theorem StackFits.parents_le {H h : ℕ} {stack : List (Frame R n)}
    (hs : StackFits H h stack) : ∀ f ∈ stack, f.parent.height ≤ H := by
  induction hs with
  | nil _ => simp
  | @cons h f stack hh ht ih =>
      intro g hg
      rcases List.mem_cons.mp hg with rfl | hg
      · have := ht.length_le; omega
      · exact ih g hg

def Fits (H E : ℕ) : State R n → Prop
  | .eval q stack => q.exponent ≤ E ∧ StackFits H q.height stack ∧
      ∀ f ∈ stack, f.parent.exponent ≤ E
  | .ret _ stack => StackFits H 0 stack ∧ ∀ f ∈ stack, f.parent.exponent ≤ E
  | .done _ => True

theorem step_fits [Semiring R] (A : Matrix (Fin n) (Fin n) R) (H E : ℕ)
    (s : State R n) (hs : Fits H E s) : Fits H E (step A s) := by
  cases s with
  | eval q stack =>
      obtain ⟨he, hstack, hparents⟩ := hs
      by_cases he0 : q.exponent = 0
      · simpa only [step, he0, ↓reduceIte, Fits] using
          And.intro (hstack.mono (Nat.zero_le _)) hparents
      by_cases he1 : q.exponent = 1
      · simpa only [step, he0, he1, Nat.one_ne_zero, ↓reduceIte, Fits] using
          And.intro (hstack.mono (Nat.zero_le _)) hparents
      by_cases hh : q.height = 0
      · simpa only [step, he0, he1, hh, ↓reduceIte, Fits] using
          And.intro (hstack.mono (Nat.zero_le _)) hparents
      · simp only [step, he0, he1, hh, ↓reduceIte, Fits]
        refine ⟨(Nat.div_le_self _ _).trans he, ?_, ?_⟩
        · exact .cons (by simp only [Query.left, Frame.parent]; omega) hstack
        · intro f hf
          rcases List.mem_cons.mp hf with rfl | hf
          · exact he
          · exact hparents f hf
  | ret x stack =>
      cases stack with
      | nil => trivial
      | cons f stack =>
          obtain ⟨hstack, hparents⟩ := hs
          have htail : ∀ g ∈ stack, g.parent.exponent ≤ E :=
            fun g hg => hparents g (List.mem_cons_of_mem _ hg)
          have he := hparents f List.mem_cons_self
          cases hstack with
          | cons hh ht =>
              cases f with
              | left q k acc =>
                  simp only [step, Fits]
                  refine ⟨(Nat.sub_le _ _).trans he, ?_, ?_⟩
                  · exact .cons (by simp only [Query.right, Frame.parent] at *; omega) ht
                  · intro g hg
                    rcases List.mem_cons.mp hg with rfl | hg
                    · exact he
                    · exact htail g hg
              | right q k acc lhs =>
                  by_cases hk : k.val = 0
                  · simpa only [step, hk, ↓reduceIte, Fits] using
                      And.intro (ht.mono (Nat.zero_le _)) htail
                  · simp only [step, hk, ↓reduceIte, Fits]
                    refine ⟨(Nat.div_le_self _ _).trans he, ?_, ?_⟩
                    · exact .cons (by simp only [Query.left, Frame.parent] at *; omega) ht
                    · intro g hg
                      rcases List.mem_cons.mp hg with rfl | hg
                      · exact he
                      · exact htail g hg
  | done x => trivial

theorem iterate_fits [Semiring R] (A : Matrix (Fin n) (Fin n) R) (H E t : ℕ)
    (s : State R n) (hs : Fits H E s) : Fits H E ((step A)^[t] s) := by
  induction t with
  | zero => exact hs
  | succ t ih => rw [Function.iterate_succ_apply']; exact step_fits A H E _ ih

def stackLength : State R n → ℕ
  | .eval _ stack | .ret _ stack => stack.length
  | .done _ => 0

theorem Fits.stackLength_le {H E : ℕ} {s : State R n} (hs : Fits H E s) :
    stackLength s ≤ H := by
  cases s with
  | eval q stack => have := hs.2.1.length_le; simp only [stackLength]; omega
  | ret x stack => simpa only [stackLength, Nat.zero_add] using hs.1.length_le
  | done x => exact Nat.zero_le _

/-- The bound holds throughout the run, including after termination. -/
theorem run_stackLength_le [Semiring R] (A : Matrix (Fin n) (Fin n) R)
    (e t : ℕ) (i j : Fin n) :
    stackLength ((step A)^[t] (.eval ⟨e.size, e, i, j⟩ [])) ≤ e.size := by
  apply Fits.stackLength_le
  apply iterate_fits A e.size e t
  exact ⟨le_rfl, .nil le_rfl, by simp⟩

end LeanCanny.Algebra.MatrixPower
