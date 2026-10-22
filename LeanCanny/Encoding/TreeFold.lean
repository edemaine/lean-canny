/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BracketsFP

/-!
# A stack pass implementing a bottom-up fold of serialized rose trees

The pass reads bracket bits from right to left. A closing bracket pushes an empty
frame; an opening bracket combines the completed child frame with its parent.
The correctness theorem is generic in the frame algebra. With finite frames,
this supports a uniform grammar checker at every input depth.
-/

@[expose] public section

namespace LeanCanny.Encoding.TreeFold


variable {σ : Type*}

def foldData (empty : σ) (combine : σ → σ → σ) : Data → σ
  | .l xs => (xs.map (foldData empty combine)).foldr combine empty

def step (empty : σ) (combine : σ → σ → σ) (b : Bool) :
    Option (List σ) → Option (List σ)
  | none => none
  | some stack =>
      if b then some (empty :: stack)
      else match stack with
        | child :: parent :: rest => some (combine child parent :: rest)
        | _ => none

/-- One entire serialized tree updates the parent frame with its bottom-up value. -/
theorem foldr_toBits (empty : σ) (combine : σ → σ → σ) (d : Data)
    (parent : σ) (rest : List σ) :
    d.toBits.foldr (step empty combine) (some (parent :: rest)) =
      some (combine (foldData empty combine d) parent :: rest) := by
  have key : ∀ (n : ℕ) (d : Data) (parent : σ) (rest : List σ), d.size ≤ n →
      d.toBits.foldr (step empty combine) (some (parent :: rest)) =
        some (combine (foldData empty combine d) parent :: rest) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
        rintro ⟨xs⟩ parent rest hsize
        have children : ∀ (ys : List Data) (current : σ) (tail : List σ),
            (∀ c ∈ ys, c.size < n) →
            (ys.map Data.toBits).flatten.foldr (step empty combine) (some (current :: tail)) =
              some ((ys.map (foldData empty combine)).foldr combine current :: tail) := by
          intro ys
          induction ys with
          | nil => intro current tail _; rfl
          | cons c cs ihcs =>
              intro current tail hlt
              have hc : c.size < n := hlt c (List.mem_cons_self ..)
              simp only [List.map_cons, List.flatten_cons, List.foldr_append]
              rw [ihcs current tail (fun c' hc' => hlt c' (List.mem_cons_of_mem c hc')),
                ih c.size hc c _ tail le_rfl]
              rfl
        rw [Data.toBits_l]
        simp only [List.foldr_cons, List.foldr_append, List.foldr_nil, step,
          Bool.false_eq_true, ite_true, ite_false]
        rw [children xs empty (parent :: rest)
          (fun c hc => (Data.size_lt_of_mem hc).trans_le hsize)]
        rw [foldData]
  exact key d.size d parent rest le_rfl

def run (empty : σ) (combine : σ → σ → σ) (bits : List Bool) : Option (List σ) :=
  bits.foldr (step empty combine) (some [empty])

@[simp] theorem run_nil (empty : σ) (combine : σ → σ → σ) :
    run empty combine [] = some [empty] := rfl

@[simp] theorem run_cons (empty : σ) (combine : σ → σ → σ) (b : Bool) (bits : List Bool) :
    run empty combine (b :: bits) = step empty combine b (run empty combine bits) := rfl

@[simp] theorem run_toBits (empty : σ) (combine : σ → σ → σ) (d : Data) :
    run empty combine d.toBits = some [combine (foldData empty combine d) empty] :=
  foldr_toBits empty combine d empty []

def frameCount : Option (List σ) → ℕ
  | none => 0
  | some stack => stack.length

theorem step_frameCount_le (empty : σ) (combine : σ → σ → σ) (b : Bool)
    (s : Option (List σ)) :
    frameCount (step empty combine b s) ≤ frameCount s + 1 := by
  cases s with
  | none => simp [step, frameCount]
  | some stack =>
      cases b
      · cases stack with
        | nil => simp [step, frameCount]
        | cons child tail => cases tail <;> simp [step, frameCount]
      · simp [step, frameCount]

theorem run_frameCount_le (empty : σ) (combine : σ → σ → σ) (bits : List Bool) :
    frameCount (run empty combine bits) ≤ bits.length + 1 := by
  induction bits with
  | nil => simp [frameCount]
  | cons b bits ih =>
      rw [run_cons]
      have hs := step_frameCount_le empty combine b (run empty combine bits)
      simp only [List.length_cons]
      omega

end LeanCanny.Encoding.TreeFold
