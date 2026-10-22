/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.PolyTimeFunctions
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Transducer

/-! # Native polynomial-time certificates for the existing pair codec

The transducers preserve the total decoders' behavior on malformed words as well
as their behavior on encoded pairs.
-/

@[expose] public section

namespace LeanCanny

open Turing.MultiTapeTM

private def delimitT : Transducer Bool Unit where
  q₀ := ()
  step _ b := ((), [b, b])
  final _ := [false, true]
  length_step_le _ _ := by simp
  length_final_le _ := by simp

private theorem delimitT_run (w : List Bool) : delimitT.run () w = delimit w := by
  induction w with
  | nil => rfl
  | cons b w ih => rw [Transducer.run_cons, ih, delimit_cons]; rfl

theorem delimit_mem_FP : delimit ∈ FP := by
  refine ComputableTidilyInPolyTime.of_linear ⟨8, ?_⟩
  exact (delimitT.computableTidilyInTimeAndSpace fun w => (delimitT_run w).symm).mono
    (fun w => by simp only [encBits_apply]; omega) (fun _ => Nat.zero_le _)

@[fun_prop]
theorem pair_computable {α : Type} {enc : α ↪ List Bool} {f g : α → List Bool}
    (hf : ComputableTidilyInPolyTime f enc encBits)
    (hg : ComputableTidilyInPolyTime g enc encBits) :
    ComputableTidilyInPolyTime (fun z => pair (f z) (g z)) enc encBits :=
  (ComputableTidilyInPolyTime.comp delimit_mem_FP hf).append hg fun _ => rfl

theorem mem_FP_pair {f g : List Bool → List Bool} (hf : f ∈ FP) (hg : g ∈ FP) :
    (fun z => pair (f z) (g z)) ∈ FP :=
  pair_computable hf hg

private def pairT (first : Bool) : Transducer Bool (Bool ⊕ Option Bool) where
  q₀ := .inr none
  step q c := match q with
    | .inl copy => (.inl copy, if copy && !first then [c] else [])
    | .inr none => (.inr (some c), [])
    | .inr (some b) =>
      if b = c then (.inr none, if first then [b] else [])
      else (.inl (!b && c), [])
  final _ := []
  length_step_le q c := by
    rcases q with copy | (_ | b)
    · cases copy <;> cases first <;> simp
    · simp
    · cases b <;> cases c <;> cases first <;> decide
  length_final_le _ := by simp

private theorem pairT_stopped (first copy : Bool) (w : List Bool) :
    (pairT first).run (.inl copy) w = if copy && !first then w else [] := by
  induction w with
  | nil => cases first <;> cases copy <;> rfl
  | cons b w ih =>
    change (if copy && !first then [b] else []) ++ (pairT first).run (.inl copy) w =
      if copy && !first then b :: w else []
    rw [ih]
    cases first <;> cases copy <;> rfl

private theorem pairSnd_double (b : Bool) (w : List Bool) :
    pairSnd (b :: b :: w) = pairSnd w := by
  cases b <;> cases h : unpair? w <;> simp [pairSnd, unpair?, h]

private theorem pairT_run (first : Bool) (w : List Bool) :
    (pairT first).run (.inr none) w = if first then pairFst w else pairSnd w := by
  induction w using pairFst.induct with
  | case1 w ih =>
    change (if first then [false] else []) ++ (pairT first).run (.inr none) w =
      if first then false :: pairFst w else pairSnd (false :: false :: w)
    rw [ih, pairSnd_double]
    cases first <;> rfl
  | case2 w ih =>
    change (if first then [true] else []) ++ (pairT first).run (.inr none) w =
      if first then true :: pairFst w else pairSnd (true :: true :: w)
    rw [ih, pairSnd_double]
    cases first <;> rfl
  | case3 w hfalse htrue =>
    cases w with
    | nil => simp [Transducer.run, pairT, pairFst, pairSnd, unpair?]
    | cons b w =>
      cases w with
      | nil => cases b <;> cases first <;>
          simp [Transducer.run, pairT, pairFst, pairSnd, unpair?]
      | cons c w =>
        cases b <;> cases c
        · exact False.elim (hfalse w rfl)
        · change (pairT first).run (.inl true) w = if first then [] else w
          rw [pairT_stopped]
          cases first <;> rfl
        · change (pairT first).run (.inl false) w = if first then [] else []
          rw [pairT_stopped]
          cases first <;> rfl
        · exact False.elim (htrue w rfl)

theorem pairFst_mem_FP : pairFst ∈ FP := by
  refine ComputableTidilyInPolyTime.of_linear ⟨8, ?_⟩
  exact ((pairT true).computableTidilyInTimeAndSpace fun w => by
    change pairFst w = (pairT true).run (.inr none) w
    exact (pairT_run true w).symm).mono
    (fun w => by simp only [encBits_apply]; omega) (fun _ => Nat.zero_le _)

theorem pairSnd_mem_FP : pairSnd ∈ FP := by
  refine ComputableTidilyInPolyTime.of_linear ⟨8, ?_⟩
  exact ((pairT false).computableTidilyInTimeAndSpace fun w => by
    change pairSnd w = (pairT false).run (.inr none) w
    exact (pairT_run false w).symm).mono
    (fun w => by simp only [encBits_apply]; omega) (fun _ => Nat.zero_le _)

theorem mem_FP_pairWithInput {f : List Bool → List Bool} (hf : f ∈ FP) :
    (fun z => pair (f z) z) ∈ FP := mem_FP_pair hf id_mem_FP

theorem UnaryFn.lift {f : List Bool → ℕ} (hf : UnaryFn f) :
    UnaryFn (fun z => f (pairFst z)) := hf.comp pairFst_mem_FP

theorem UnaryFn.index : UnaryFn (fun z => (pairSnd z).length) :=
  UnaryFn.length pairSnd_mem_FP

theorem FPPred.lift {p : List Bool → Prop} (hp : FPPred p) :
    FPPred (fun z => p (pairFst z)) := hp.comp pairFst_mem_FP

end LeanCanny
