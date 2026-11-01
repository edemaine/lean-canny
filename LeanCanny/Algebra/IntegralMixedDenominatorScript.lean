/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedDenominatorInstruction
/-! # Chronological scalar denominator programs for tagged mixed scripts -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedDenominatorScriptBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralMixedHistory IntegralMixedHistoryScript IntegralMixedDenominatorBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Family where
  ambient : List Bool → ℕ
  width : List Bool → ℕ
  spatial : ∀ c, SpatialSource (ambient c)
  rules : ∀ c, List (Command (ambient c) (width c))
  modulus : List Bool → ℕ
  modulus_ne_zero : ∀ c, modulus c ≠ 0

def count (F : Family) (c : List Bool) : ℕ := (F.rules c).length

def commandAt (F : Family) (c : List Bool) (i : ℕ) : Option (Command (F.ambient c) (F.width c)) := (F.rules c).reverse[i]?

noncomputable def descriptorAt (F : Family) (c : List Bool) (i : ℕ) : Instruction :=
  match commandAt F c i with
  | some cmd => instruction (F.spatial c) cmd (min i (count F c))
  | none => ⟨0, 0, 1, 1, fun _ => 0⟩

noncomputable def program (F : Family) : IntegralDenominatorPass.Family where
  count := count F
  modulus := F.modulus
  modulus_ne_zero := F.modulus_ne_zero
  leading c i := (descriptorAt F c i).leading
  arity c i := (descriptorAt F c i).arity
  degree c i := (descriptorAt F c i).degree
  exponent c i := (descriptorAt F c i).exponent
  index c i j := (descriptorAt F c i).index j

theorem next_descriptor (F : Family) (c : List Bool) (i : ℕ) (v : List ℤ) :
    IntegralDenominatorPass.integerNext (program F) c i v = (descriptorAt F c i).value v := rfl

theorem next_valid (F : Family) (c : List Bool) (i : ℕ) (hi : i < count F c) (v : List ℤ) (hv : v.length = i) :
    IntegralDenominatorPass.integerNext (program F) c i v = scalarLeading (F.spatial c)
      ((F.rules c).reverse[i]'(by simpa only [count, List.length_reverse] using hi)) v := by
  rw [next_descriptor]
  unfold descriptorAt commandAt
  rw [List.getElem?_eq_getElem (by simpa only [count, List.length_reverse] using hi), min_eq_left hi.le]
  exact instruction_value _ _ i v hv

theorem integers_prefix (F : Family) (c : List Bool) (i : ℕ) (hi : i ≤ count F c) :
    IntegralDenominatorPass.integers (program F) c i =
      ((F.rules c).reverse.take i).foldl (fun v cmd => scalarLeading (F.spatial c) cmd v :: v) [] := by
  induction i with
  | zero => rfl
  | succ i ih =>
    have H : i < count F c := by omega
    rw [IntegralDenominatorPass.integers, List.take_succ_eq_append_getElem (by simpa only [count, List.length_reverse] using H), List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [next_valid F c i H _ (IntegralDenominatorPass.integers_length _ _ _), ih H.le]

theorem denominators_fold {n B : ℕ} (P : SpatialSource n) (initial : List ℤ) (cs : List (Command n B)) :
    denominators P initial cs = cs.reverse.foldl (fun v cmd => scalarLeading P cmd v :: v) initial := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [denominators, List.reverse_cons, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, ← ih]

theorem integers_full (F : Family) (c : List Bool) :
    IntegralDenominatorPass.integers (program F) c (count F c) = denominators (F.spatial c) [] (F.rules c) := by
  have H := integers_prefix F c (count F c) le_rfl
  have HT : (F.rules c).reverse.take (count F c) = (F.rules c).reverse := by
    simpa only [count, List.length_reverse] using (List.take_length (l := (F.rules c).reverse))
  rw [HT] at H
  exact H.trans (denominators_fold _ _ _).symm

theorem denominators_append {n B : ℕ} (P : SpatialSource n) (initial : List ℤ) (cs ds : List (Command n B)) :
    denominators P initial (cs ++ ds) = denominators P (denominators P initial ds) cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp only [List.cons_append, denominators, ih]

theorem actual_continue {S m : ℕ} (F : Family) (c : List Bool) {ι : Type} [Fintype ι]
    (initial : State (F.spatial c) S (F.width c) m ι) (cs ds : List (Command (F.ambient c) (F.width c)))
    (h : m + cs.length ≤ S + 1) (hrules : F.rules c = cs ++ ds)
    (hinitial : bankList initial = denominators (F.spatial c) [] ds) :
    bankList (continueRun initial cs h) = IntegralDenominatorPass.integers (program F) c (count F c) := by
  rw [bankList_continueRun, integers_full, hrules, denominators_append, hinitial]
end LeanCanny.Algebra.IntegralMixedDenominatorScriptBits
