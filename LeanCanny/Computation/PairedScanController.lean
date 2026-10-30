/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.ControllerRequests
public import LeanCanny.Computation.PSPACEBoolean

/-! # A resumable binary scan with two recursive requests per entry

For each counter value, the controller requests two child answers and keeps
only their conjunction and the running disjunction. This is the streamed
midpoint scan needed by recursive graph reachability. It never stores a table
of child answers or an unrolled computation tree.
-/

@[expose] public section
namespace LeanCanny.Computation.PairedScan
open Turing.MultiTapeTM
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

abbrev State := List Bool × ℕ × Bool × Bool × Bool
abbrev encState : State ↪ List Bool :=
  encPair encBits (encPair encNat (encPair encBool (encPair encBool encBool)))

structure Program where
  count : List Bool → ℕ
  left : List Bool → List Bool
  right : List Bool → List Bool

namespace Program
variable (P : Program)

def reply (v : List Bool) : Bool := decide (v = [true])
def initial (q : List Bool) : State := (q, 0, false, false, false)
def entry (q : List Bool) (k : ℕ) : List Bool := pair q (BinaryNatCode.encode k)
def test (answer : List Bool → List Bool) (q : List Bool) (k : ℕ) : Bool :=
  reply (answer (P.left (entry q k))) && reply (answer (P.right (entry q k)))
def scan (P : Program) (answer : List Bool → List Bool) (q : List Bool) : ℕ → Bool
  | 0 => false
  | k + 1 => scan P answer q k || P.test answer q k

def controller : RecursiveController.Controller (List Bool) State where
  initial := initial
  halted s := decide (P.count s.1 ≤ s.2.1)
  output s := [s.2.2.2.2]
  needs _ := true
  query s := if s.2.2.1 then P.right (entry s.1 s.2.1) else P.left (entry s.1 s.2.1)
  advance := id
  resume p := if p.1.2.2.1 then
    (p.1.1, p.1.2.1 + 1, false, false, p.1.2.2.2.2 || (p.1.2.2.2.1 && reply p.2))
    else (p.1.1, p.1.2.1, true, reply p.2, p.1.2.2.2.2)

def value (answer : List Bool → List Bool) (q : List Bool) : List Bool := [P.scan answer q (P.count q)]

theorem scan_true_iff (answer : List Bool → List Bool) (q : List Bool) (n : ℕ) :
    P.scan answer q n = true ↔ ∃ k < n,
      answer (P.left (entry q k)) = [true] ∧ answer (P.right (entry q k)) = [true] := by
  induction n with
  | zero => simp only [scan, Bool.false_eq_true, Nat.not_lt_zero, false_and, exists_false]
  | succ n ih =>
    simp only [scan, Bool.or_eq_true, ih, test, Bool.and_eq_true, reply, decide_eq_true_eq]
    constructor
    · rintro (⟨k, hk, h⟩ | h)
      · exact ⟨k, by omega, h⟩
      · exact ⟨n, by omega, h⟩
    · rintro ⟨k, hk, h⟩
      by_cases he : k = n
      · exact Or.inr (he ▸ h)
      · exact Or.inl ⟨k, by omega, h⟩

theorem reference_left (answer : List Bool → List Bool) (q : List Bool) (k : ℕ) (a : Bool)
    (hk : k < P.count q) :
    P.controller.reference answer (q, k, false, false, a) =
      (q, k, true, reply (answer (P.left (entry q k))), a) := by
  simp only [RecursiveController.Controller.reference, controller, not_le.mpr hk, decide_false,
    Bool.false_eq_true, ite_false, ite_true]

theorem reference_right (answer : List Bool → List Bool) (q : List Bool) (k : ℕ) (l a : Bool)
    (hk : k < P.count q) :
    P.controller.reference answer (q, k, true, l, a) =
      (q, k + 1, false, false, a || (l && reply (answer (P.right (entry q k))))) := by
  simp only [RecursiveController.Controller.reference, controller, not_le.mpr hk, decide_false,
    Bool.false_eq_true, ite_false, ite_true]

theorem iterate_even (answer : List Bool → List Bool) (q : List Bool) (k : ℕ) (hk : k ≤ P.count q) :
    (P.controller.reference answer)^[2 * k] (initial q) = (q, k, false, false, P.scan answer q k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have HK : k < P.count q := by omega
    have HE : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
    rw [HE, Function.iterate_succ_apply', Function.iterate_succ_apply', ih (by omega),
      P.reference_left answer q k _ HK, P.reference_right answer q k _ _ HK]
    rfl

theorem iterate_odd (answer : List Bool → List Bool) (q : List Bool) (k : ℕ) (hk : k < P.count q) :
    (P.controller.reference answer)^[2 * k + 1] (initial q) =
      (q, k, true, reply (answer (P.left (entry q k))), P.scan answer q k) := by
  rw [Function.iterate_succ_apply', P.iterate_even answer q k hk.le, P.reference_left answer q k _ hk]

theorem halted_after (answer : List Bool → List Bool) (q : List Bool) :
    P.controller.halted ((P.controller.reference answer)^[2 * P.count q] (initial q)) = true := by
  rw [P.iterate_even answer q _ le_rfl]
  exact decide_eq_true le_rfl

theorem context_reference (answer : List Bool → List Bool) (s : State) :
    (P.controller.reference answer s).1 = s.1 := by
  dsimp only [RecursiveController.Controller.reference, controller]
  split_ifs <;> rfl

theorem context_iterate (answer : List Bool → List Bool) (q : List Bool) (t : ℕ) :
    ((P.controller.reference answer)^[t] (initial q)).1 = q := by
  induction t with
  | zero => rfl
  | succ t ih => rw [Function.iterate_succ_apply', P.context_reference, ih]

theorem output_when_halted (answer : List Bool → List Bool) (q : List Bool) (t : ℕ)
    (ht : t ≤ 2 * P.count q)
    (hh : P.controller.halted ((P.controller.reference answer)^[t] (initial q)) = true) :
    P.controller.output ((P.controller.reference answer)^[t] (initial q)) = P.value answer q := by
  have HM := Nat.mod_lt t (by decide : 0 < 2)
  have HD := Nat.mod_add_div t 2
  by_cases he : t % 2 = 0
  · have HE : t = 2 * (t / 2) := by omega
    have HK : t / 2 ≤ P.count q := by omega
    rw [HE, P.iterate_even answer q _ HK] at hh ⊢
    have HL : P.count q ≤ t / 2 := of_decide_eq_true hh
    have HN : t / 2 = P.count q := by omega
    rw [HN]
    rfl
  · have HE : t = 2 * (t / 2) + 1 := by omega
    have HK : t / 2 < P.count q := by omega
    rw [HE, P.iterate_odd answer q _ HK] at hh
    have HL : P.count q ≤ t / 2 := of_decide_eq_true hh
    omega

theorem requests_iff (answer : List Bool → List Bool) (q child : List Bool) :
    P.controller.Requests answer (fun q => 2 * P.count q) q child ↔
      ∃ k < P.count q, child = P.left (entry q k) ∨ child = P.right (entry q k) := by
  change (∃ t, t ≤ 2 * P.count q ∧
    P.controller.halted ((P.controller.reference answer)^[t] (initial q)) = false ∧
    P.controller.needs ((P.controller.reference answer)^[t] (initial q)) = true ∧
    child = P.controller.query ((P.controller.reference answer)^[t] (initial q))) ↔ _
  constructor
  · rintro ⟨t, ht, hh, _, he⟩
    have HM := Nat.mod_lt t (by decide : 0 < 2)
    have HD := Nat.mod_add_div t 2
    by_cases hp : t % 2 = 0
    · have HE : t = 2 * (t / 2) := by omega
      have HK : t / 2 ≤ P.count q := by omega
      rw [HE, P.iterate_even answer q _ HK] at hh he
      have HL : t / 2 < P.count q := by
        have HH : ¬P.count q ≤ t / 2 := of_decide_eq_false hh
        omega
      exact ⟨t / 2, HL, Or.inl he⟩
    · have HE : t = 2 * (t / 2) + 1 := by omega
      have HK : t / 2 < P.count q := by omega
      rw [HE, P.iterate_odd answer q _ HK] at he
      exact ⟨t / 2, HK, Or.inr he⟩
  · rintro ⟨k, hk, he | he⟩
    · refine ⟨2 * k, by omega, ?_, rfl, ?_⟩
      · rw [P.iterate_even answer q k hk.le]
        exact decide_eq_false (not_le.mpr hk)
      · rw [P.iterate_even answer q k hk.le]
        exact he
    · refine ⟨2 * k + 1, by omega, ?_, rfl, ?_⟩
      · rw [P.iterate_odd answer q k hk]
        exact decide_eq_false (not_le.mpr hk)
      · rw [P.iterate_odd answer q k hk]
        exact he

end Program
end LeanCanny.Computation.PairedScan
