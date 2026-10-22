/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.InSpaceLib
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolySpace

/-!
# A streamed modular sum with a space-bounded child

This independent experiment uses Complexitylib2's binary encodings and space
calculus. The summand is assumed computable in linear space, with no time
hypothesis. The concrete child runs a binary-counted repeated-subtraction loop.
-/

@[expose] public section

namespace LeanCanny.SpacePrototype

open Turing.MultiTapeTM
open ComputableTidilyInSpace
open scoped BigOperators

abbrev encInput : ℕ × ℕ ↪ List Bool := encPair encNat encNat
abbrev State := ℕ × ℕ × ℕ
abbrev encState : State ↪ List Bool := encPair encNat (encPair encNat encNat)

/-- The context is `m`, the index is `i`, and the accumulator is reduced modulo `m+1`. -/
def step (child : ℕ × ℕ → ℕ) (s : State) : State :=
  (s.1, s.2.1 + 1, (s.2.2 + child (s.1, s.2.1)) % (s.1 + 1))

def value (child : ℕ × ℕ → ℕ) (m : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => (value child m k + child (m, k)) % (m + 1)

def scan (child : ℕ × ℕ → ℕ) (p : ℕ × ℕ) : ℕ :=
  ((step child)^[p.2] (p.1, 0, 0)).2.2

theorem iterate_step (child : ℕ × ℕ → ℕ) (m k : ℕ) :
    (step child)^[k] (m, 0, 0) = (m, k, value child m k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih]; rfl

theorem value_le (child : ℕ × ℕ → ℕ) (m k : ℕ) : value child m k ≤ m := by
  cases k with
  | zero => exact Nat.zero_le _
  | succ k => exact Nat.le_of_lt_succ (Nat.mod_lt _ (Nat.succ_pos _))

theorem scan_eq_sum (child : ℕ × ℕ → ℕ) (p : ℕ × ℕ) :
    scan child p = (∑ i ∈ Finset.range p.2, child (p.1, i)) % (p.1 + 1) := by
  suffices h : ∀ k, value child p.1 k =
      (∑ i ∈ Finset.range k, child (p.1, i)) % (p.1 + 1) by
    rw [scan, iterate_step, h]
  intro k
  induction k with
  | zero => simp [value]
  | succ k ih =>
    rw [value, ih, Finset.sum_range_succ, Nat.mod_add_mod]

/-- Composing the child needs neither a clock nor a bound on its execution time. -/
theorem step_inSpace {child : ℕ × ℕ → ℕ}
    (hc : ComputableTidilyInSpace child encInput encNat fun p => (encInput p).length) :
    ComputableTidilyInSpace (step child) encState encState fun s => (encState s).length := by
  have hm := fst encNat (encPair encNat encNat)
  have hi := fst' (snd encNat (encPair encNat encNat))
  have ha := snd' (snd encNat (encPair encNat encNat))
  have hv := budget_comp_linear hc (budget_prod hm hi)
  exact budget_prod hm (budget_prod (budget_natSucc hi)
    (budget_natMod (budget_natAdd ha hv) (budget_natSucc hm)))

theorem state_length_le (child : ℕ × ℕ → ℕ) (p : ℕ × ℕ) (k : ℕ) (hk : k ≤ p.2) :
    (encState ((step child)^[k] (p.1, 0, 0))).length ≤ 4 * ((encInput p).length + 1) := by
  rw [iterate_step]
  have hi := ComputableTidilyInO.length_encNat_mono hk
  have ha := ComputableTidilyInO.length_encNat_mono (value_le child p.1 k)
  simp only [encState, encInput, length_encPair] at hi ha ⊢
  omega

/-- Binary-counted folding stays within a linear budget, even for a slow child. -/
theorem scan_inSpace {child : ℕ × ℕ → ℕ}
    (hc : ComputableTidilyInSpace child encInput encNat fun p => (encInput p).length) :
    ComputableTidilyInSpace (scan child) encInput encNat fun p => (encInput p).length := by
  have hinit : ComputableTidilyInSpace (fun p : ℕ × ℕ => (p.1, 0, 0)) encInput encState
      (fun p => (encInput p).length) :=
    budget_prod (fst _ _) (budget_prod (budget_const 0 (.refl _)) (budget_const 0 (.refl _)))
  exact snd' (snd' (budget_iterate (snd _ _) hinit (step_inSpace hc)
    (state_length_le child) (linear_mul 4)))

/-- The same fold accepts arbitrary polynomial-space children, not just linear ones. -/
theorem polySpace_of_linear {α β : Type} {eA : α ↪ List Bool} {eB : β ↪ List Bool}
    {f : α → β} (h : ComputableTidilyInSpace f eA eB fun a => (eA a).length) :
    ComputableTidilyInPolySpace f eA eB := by
  obtain ⟨T, h⟩ := h
  exact ⟨T, _, PolyBounded.self, h⟩

theorem scan_inPolySpace {child : ℕ × ℕ → ℕ}
    (hc : ComputableTidilyInPolySpace child encInput encNat) :
    ComputableTidilyInPolySpace (scan child) encInput encNat := by
  have hm := polySpace_of_linear (fst encNat (encPair encNat encNat))
  have hr := polySpace_of_linear (snd encNat (encPair encNat encNat))
  have hi := (polySpace_of_linear (fst encNat encNat)).comp hr
  have ha := (polySpace_of_linear (snd encNat encNat)).comp hr
  have hsucc := polySpace_of_linear (natSucc.weaken linear_succ)
  have hadd := polySpace_of_linear (natAdd.weaken linear_succ)
  have hmod := polySpace_of_linear (natMod.weaken (linear_mul 16))
  have hstep : ComputableTidilyInPolySpace (step child) encState encState :=
    hm.prod ((hsucc.comp hi).prod (hmod.comp
      ((hadd.comp (ha.prod (hc.comp (hm.prod hi)))).prod (hsucc.comp hm))))
  have hinit : ComputableTidilyInPolySpace (fun p : ℕ × ℕ => (p.1, 0, 0)) encInput encState :=
    polySpace_of_linear (budget_prod (fst _ _)
      (budget_prod (budget_const 0 (.refl _)) (budget_const 0 (.refl _))))
  have h := ComputableTidilyInPolySpace.iterate (ComputableTidilyInPolyTime.snd _ _)
    hinit hstep (PolyBounded.of_forall_le 4 1 (fun _ => by
      simp only [pow_one, encInput]
      exact le_rfl))
    (state_length_le child)
  exact (polySpace_of_linear (snd encNat encNat)).comp
    ((polySpace_of_linear (snd encNat (encPair encNat encNat))).comp h)

/-- The child explicitly performs `p.1` rounds of the library's subtraction loop. -/
def slowChild (p : ℕ × ℕ) : ℕ :=
  (divStep^[p.1] (p.2 + 1, 0, p.1)).2.2

theorem slowChild_eq (p : ℕ × ℕ) : slowChild p = p.1 % (p.2 + 1) := by
  rw [slowChild, iterate_divStep_self]

theorem slowChild_inSpace :
    ComputableTidilyInSpace slowChild encInput encNat fun p => (encInput p).length := by
  have hinit : ComputableTidilyInSpace (fun p : ℕ × ℕ => (p.2 + 1, 0, p.1))
      encInput encState (fun p => (encInput p).length) :=
    budget_prod (budget_natSucc (snd _ _))
      (budget_prod (budget_const 0 (.refl _)) (fst _ _))
  have hstate (p : ℕ × ℕ) (k : ℕ) (_ : k ≤ p.1) :
      (encState (divStep^[k] (p.2 + 1, 0, p.1))).length ≤ 8 * ((encInput p).length + 1) := by
    rw [iterate_divStep]
    have hq := ComputableTidilyInO.length_encNat_mono
      ((Nat.min_le_right k (p.1 / (p.2 + 1))).trans (Nat.div_le_self _ _))
    have hr := ComputableTidilyInO.length_encNat_mono
      (Nat.sub_le p.1 ((p.2 + 1) * min k (p.1 / (p.2 + 1))))
    have hd := length_encNat_add_le_add p.2 1
    simp only [encState, encInput, length_encPair, length_encNat_eq_size, Nat.size_one] at hq hr hd ⊢
    omega
  exact snd' (snd' (budget_iterate (fst _ _) hinit
    (divStep_inSpace.weaken linear_succ) hstate (linear_mul 8)))

/-- On these inputs all `2^w` prescribed child rounds increment the quotient. -/
theorem slowChild_rounds (w k : ℕ) (hk : k ≤ 2 ^ w) :
    divStep^[k] (1, 0, 2 ^ w) = (1, k, 2 ^ w - k) := by
  rw [iterate_divStep]
  simp only [Nat.div_one, Nat.min_eq_left hk, one_mul]

theorem slowChild_input_length (w : ℕ) :
    (encInput (2 ^ w, 0)).length = 2 * w + 3 := by
  simp only [encInput, length_encPair, length_encNat_eq_size, Nat.size_pow, Nat.size_zero]
  omega

theorem slowScan_inSpace :
    ComputableTidilyInSpace (scan slowChild) encInput encNat fun p => (encInput p).length :=
  scan_inSpace slowChild_inSpace

theorem slowScan_correct (p : ℕ × ℕ) :
    scan slowChild p = (∑ i ∈ Finset.range p.2, p.1 % (i + 1)) % (p.1 + 1) := by
  simp only [scan_eq_sum, slowChild_eq]

end LeanCanny.SpacePrototype
