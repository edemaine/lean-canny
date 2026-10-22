/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanCanny.Encoding.Delimit
public import Mathlib.Data.Nat.Init
public import Aesop.BuiltinRules
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Tactic.Basic
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Widget.Calc
public import Std.Tactic.BVDecide.Normalize.Prop

/-!
Adapted from Complexitylib at add0aca8ee0d71e68969f2cb45cf91554a50f787.
The definitions preserve the existing wire format and use no machine model.

# Pairing binary strings

This file defines the low-level self-delimiting pairing codec used by machine
inputs throughout this project. It deliberately has no dependency on the
machine or complexity-class layers, so parsers and encoders can reuse it
without introducing an import cycle.
-/


@[expose] public section

namespace LeanCanny

/-- Encode a pair of binary strings as a single binary string.
    Each bit of `x` is doubled (`false ↦ [false, false]`, `true ↦ [true, true]`),
    followed by the separator `[false, true]`, followed by `y` verbatim.
    The output has length `2|x| + 2 + |y|` (`pair_length`) and the encoding is
    injective (`pair_inj`). Machine-level cost is recorded elsewhere: `pair` of
    two `FP` functions is in `FP` (`mem_FP_pair`), and `x ↦ pair (f x) x` has
    an explicit bound (`TM.pairWithInputTM_computesInTime`); no linear-time
    bound for `pair` itself is stated. -/
def pair (x y : List Bool) : List Bool :=
  delimit x ++ y

/-- One step of the doubling encoder: `pair` on `b :: x` prepends the
    doubled bit `b, b`. -/
theorem pair_cons_eq (b : Bool) (x y : List Bool) :
    pair (b :: x) y = b :: b :: pair x y := by
  simp [pair]

/-- `|pair x y| = 2·|x| + 2 + |y|`. The `2·|x|` comes from doubling every
    bit of `x`; the `+2` is the separator `[false, true]`. -/
@[simp] theorem pair_length (x y : List Bool) :
    (pair x y).length = 2 * x.length + 2 + y.length := by
  simp only [pair, List.length_append, delimit_length]

/-- `pair` is injective: if `pair x₁ y₁ = pair x₂ y₂` then `x₁ = x₂` and
`y₁ = y₂`. -/
theorem pair_inj {x₁ x₂ : List Bool} {y₁ y₂ : List Bool}
    (h : pair x₁ y₁ = pair x₂ y₂) : x₁ = x₂ ∧ y₁ = y₂ := by
  simpa only [pair, unpair?_delimit_append, Option.some.injEq, Prod.mk.injEq]
    using congrArg unpair? h

/-- `unpair?` is a left inverse of `pair`: decoding an encoded pair
    recovers exactly its two components. -/
@[simp] theorem unpair?_pair (x y : List Bool) :
    unpair? (pair x y) = some (x, y) :=
  unpair?_delimit_append x y

/-- Soundness of the decoder: if `unpair?` succeeds on `z`, producing `(x, y)`,
    then `z` was exactly the encoding `pair x y`. -/
theorem eq_pair_of_unpair?_eq_some {z x y : List Bool} (h : unpair? z = some (x, y)) :
    z = pair x y :=
  eq_delimit_append_of_unpair?_eq_some h

/-- `unpair? z` returns `some (x, y)` if and only if `z = pair x y`,
    characterizing exactly which strings are valid pair encodings. -/
theorem unpair?_eq_some_iff {z x y : List Bool} :
    unpair? z = some (x, y) ↔ z = pair x y := by
  constructor
  · exact eq_pair_of_unpair?_eq_some
  · intro hz
    subst hz
    exact unpair?_pair x y

/-- In `pair x y`, the first duplicated copy of `x[i]` sits at position `2*i`. -/
theorem pair_getElem_left_first (x y : List Bool) (i : ℕ) (hi : i < x.length) :
    (pair x y)[2 * i]'(by rw [pair_length]; omega) = x[i]'hi := by
  induction x generalizing i with
  | nil => cases hi
  | cons b xs ih =>
    cases i with
    | zero => simp [pair_cons_eq]
    | succ i =>
      simpa only [pair_cons_eq, show 2 * (i + 1) = (2 * i + 1) + 1 by omega,
        List.getElem_cons_succ] using ih i (by simpa using hi)

/-- In `pair x y`, the second duplicated copy of `x[i]` sits at position `2*i+1`. -/
theorem pair_getElem_left_second (x y : List Bool) (i : ℕ) (hi : i < x.length) :
    (pair x y)[2 * i + 1]'(by rw [pair_length]; omega) = x[i]'hi := by
  induction x generalizing i with
  | nil => cases hi
  | cons b xs ih =>
    cases i with
    | zero => simp [pair_cons_eq]
    | succ i =>
      simpa only [pair_cons_eq, show 2 * (i + 1) + 1 = ((2 * i + 1) + 1) + 1 by omega,
        List.getElem_cons_succ] using ih i (by simpa using hi)

/-- The first separator bit in `pair x y` is `false`. -/
theorem pair_getElem_sep_zero (x y : List Bool) :
    (pair x y)[2 * x.length]'(by rw [pair_length]; omega) = false := by
  induction x with
  | nil => simp [pair]
  | cons b xs ih =>
    simpa only [List.length_cons, pair_cons_eq,
      show 2 * (xs.length + 1) = (2 * xs.length + 1) + 1 by omega,
      List.getElem_cons_succ] using ih

/-- The second separator bit in `pair x y` is `true`. -/
theorem pair_getElem_sep_one (x y : List Bool) :
    (pair x y)[2 * x.length + 1]'(by rw [pair_length]; omega) = true := by
  induction x with
  | nil => simp [pair]
  | cons b xs ih =>
    simpa only [List.length_cons, pair_cons_eq,
      show 2 * (xs.length + 1) + 1 = ((2 * xs.length + 1) + 1) + 1 by omega,
      List.getElem_cons_succ] using ih

/-- In `pair x y`, the suffix after the separator is exactly `y`. -/
theorem pair_getElem_right (x y : List Bool) (j : ℕ) (hj : j < y.length) :
    (pair x y)[2 * x.length + 2 + j]'(by rw [pair_length]; omega) = y[j]'hj := by
  simpa only [pair, delimit_length, Nat.add_sub_cancel_left] using
    (List.getElem_append_right (as := delimit x) (bs := y)
      (i := (delimit x).length + j) (h₂ := by simp only [List.length_append]; omega)
      (by omega))

/-! ## The projections

Total decoders for the two components. `pairFst` is defined by scanning rather
than through `unpair?` so that a single-pass machine can compute it; only the
behaviour of either projection on canonical pairs is ever used. -/

/-- The first component of a canonical pair: read doubled bits until the
`[false, true]` separator. On `pair x y` this returns `x` (see `pairFst_pair`);
on malformed input it returns the bits decoded so far. -/
def pairFst : List Bool → List Bool
  | false :: false :: z => false :: pairFst z
  | true :: true :: z => true :: pairFst z
  | _ => []

/-- The second component of a canonical pair: the suffix after the leading
self-delimiting block, or `[]` if the input is not a valid pair. -/
def pairSnd (z : List Bool) : List Bool :=
  match unpair? z with
  | some (_, s) => s
  | none => []

@[simp] theorem pairFst_pair (x y : List Bool) : pairFst (pair x y) = x := by
  induction x with
  | nil => rfl
  | cons b x ih => cases b <;> (rw [pair_cons_eq]; simp [pairFst, ih])

@[simp] theorem pairSnd_pair (x y : List Bool) : pairSnd (pair x y) = y := by
  simp [pairSnd]

/-- `pairSnd` agrees with the partial decoder `unpair?`, defaulting to `[]`. -/
theorem pairSnd_eq_unpair? (z : List Bool) :
    pairSnd z = ((unpair? z).map Prod.snd).getD [] := by
  unfold pairSnd
  cases unpair? z <;> rfl

/-- The first component of a pair is no longer than the pair. -/
theorem pairFst_length_le (z : List Bool) : (pairFst z).length ≤ z.length := by
  induction z using pairFst.induct <;> simp [pairFst] <;> omega

/-- The second component of a pair is no longer than the pair. -/
theorem pairSnd_length_le (z : List Bool) : (pairSnd z).length ≤ z.length := by
  rcases hu : unpair? z with _ | ⟨p, q⟩
  · rw [show pairSnd z = [] from by rw [pairSnd, hu]]
    simp
  · have hz : z = pair p q := unpair?_eq_some_iff.mp hu
    rw [show pairSnd z = q from by rw [pairSnd, hu], hz, pair_length]
    omega

end LeanCanny
