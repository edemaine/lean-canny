/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MatrixPowerBounds
public import Complexitylib.Encoding.BinaryNat
public import Complexitylib.Encoding.Pairing
public import Mathlib.Data.ZMod.Basic

/-!
# Binary representations of streamed matrix-power states

Natural fields use canonical binary codes and Complexitylib's self-delimiting
pairing. The state representation is injective whenever the scalar representation
is injective. Its length is bounded throughout the run when scalar codes have a
uniform bit bound; residues modulo a nonzero runtime modulus supply such codes.

Exact decoding is developed in `MatrixPowerDecoding`, and certified binary query
writers in `MatrixPowerQueryFP`. `MatrixPowerArithmeticFP` supplies certified
modular scalar operations. `MatrixPowerController` assembles an FP transition
with explicit FP callbacks; its correctness and context-inclusive size bounds
are proved in `MatrixPowerControllerCorrect`.
-/

@[expose] public section

namespace LeanCanny.Algebra.MatrixPower
open Complexity

variable {R : Type*} {n : ℕ}

def queryBits (q : Query n) : List Bool :=
  pair (BinaryNatCode.encode q.height) (pair (BinaryNatCode.encode q.exponent)
    (pair (BinaryNatCode.encode q.row.val) (BinaryNatCode.encode q.col.val)))

theorem queryBits_injective : Function.Injective (queryBits (n := n)) := by
  intro q r h
  obtain ⟨hh, h⟩ := pair_inj h
  obtain ⟨he, h⟩ := pair_inj h
  obtain ⟨hi, hj⟩ := pair_inj h
  have hh := BinaryNatCode.encode_injective hh
  have he := BinaryNatCode.encode_injective he
  have hi := Fin.ext (BinaryNatCode.encode_injective hi)
  have hj := Fin.ext (BinaryNatCode.encode_injective hj)
  cases q
  cases r
  cases hh
  cases he
  cases hi
  cases hj
  rfl

def frameBits (enc : R → List Bool) : Frame R n → List Bool
  | .left q k acc => false :: pair (queryBits q) (pair (BinaryNatCode.encode k.val) (enc acc))
  | .right q k acc lhs =>
      true :: pair (queryBits q) (pair (BinaryNatCode.encode k.val) (pair (enc acc) (enc lhs)))

theorem frameBits_injective (enc : R → List Bool) (henc : Function.Injective enc) :
    Function.Injective (frameBits (n := n) enc) := by
  intro f g h
  cases f <;> cases g <;>
    simp only [frameBits, List.cons.injEq, Bool.false_eq_true, Bool.true_eq_false,
      true_and, false_and] at h
  · obtain ⟨hq, h⟩ := pair_inj h
    obtain ⟨hk, ha⟩ := pair_inj h
    cases queryBits_injective hq
    cases Fin.ext (BinaryNatCode.encode_injective hk)
    cases henc ha
    rfl
  · obtain ⟨hq, h⟩ := pair_inj h
    obtain ⟨hk, h⟩ := pair_inj h
    obtain ⟨ha, hl⟩ := pair_inj h
    cases queryBits_injective hq
    cases Fin.ext (BinaryNatCode.encode_injective hk)
    cases henc ha
    cases henc hl
    rfl

def stackBits (enc : R → List Bool) : List (Frame R n) → List Bool
  | [] => []
  | f :: stack => true :: pair (frameBits enc f) (stackBits enc stack)

theorem stackBits_injective (enc : R → List Bool) (henc : Function.Injective enc) :
    Function.Injective (stackBits (n := n) enc) := by
  intro stack other h
  induction stack generalizing other with
  | nil => cases other <;> simp_all [stackBits]
  | cons f stack ih =>
      cases other with
      | nil => simp [stackBits] at h
      | cons g other =>
          obtain ⟨hf, ht⟩ := pair_inj (List.cons.inj h).2
          cases frameBits_injective enc henc hf
          cases ih ht
          rfl

def stateBits (enc : R → List Bool) : State R n → List Bool
  | .eval q stack => false :: false :: pair (queryBits q) (stackBits enc stack)
  | .ret x stack => false :: true :: pair (enc x) (stackBits enc stack)
  | .done x => true :: enc x

theorem stateBits_injective (enc : R → List Bool) (henc : Function.Injective enc) :
    Function.Injective (stateBits (n := n) enc) := by
  intro s t h
  cases s <;> cases t <;>
    simp only [stateBits, List.cons.injEq, Bool.false_eq_true, Bool.true_eq_false,
      true_and, false_and] at h
  · obtain ⟨hq, hs⟩ := pair_inj h
    cases queryBits_injective hq
    cases stackBits_injective enc henc hs
    rfl
  · obtain ⟨hx, hs⟩ := pair_inj h
    cases henc hx
    cases stackBits_injective enc henc hs
    rfl
  · cases henc h
    rfl

def queryBitBound (n H E : ℕ) : ℕ := 2 * H.size + 2 * E.size + 3 * n.size + 6

def frameBitBound (n H E b : ℕ) : ℕ := 2 * queryBitBound n H E + 2 * n.size + 3 * b + 7

def stateBitBound (n H E b : ℕ) : ℕ :=
  2 * queryBitBound n H E + 2 * b + 4 + H * (2 * frameBitBound n H E b + 3)

/-- With initial height `e.size`, the full state allowance is quadratic in the
binary lengths of the dimension and exponent and the scalar bit allowance. -/
theorem stateBitBound_size_le (n e b : ℕ) :
    stateBitBound n e.size e b ≤ 64 * (n.size + e.size + b + 1) ^ 2 := by
  have hh : e.size.size ≤ e.size := Nat.size_le.mpr Nat.lt_two_pow_self
  let S := n.size + e.size + b + 1
  have hS : 1 ≤ S := by dsimp [S]; omega
  have he : e.size ≤ S := by dsimp [S]; omega
  have hb : b ≤ S := by dsimp [S]; omega
  have hq : queryBitBound n e.size e ≤ 6 * S := by
    unfold queryBitBound
    dsimp [S]
    omega
  have hf : frameBitBound n e.size e b ≤ 19 * S := by
    unfold frameBitBound queryBitBound
    dsimp [S]
    omega
  have hm := Nat.mul_le_mul he (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hf) 3)
  change stateBitBound n e.size e b ≤ 64 * S ^ 2
  unfold stateBitBound
  nlinarith

theorem queryBits_length_le (q : Query n) (H E : ℕ)
    (hh : q.height ≤ H) (he : q.exponent ≤ E) :
    (queryBits q).length ≤ queryBitBound n H E := by
  have hh := Nat.size_le_size hh
  have he := Nat.size_le_size he
  have hi := Nat.size_le_size q.row.isLt.le
  have hj := Nat.size_le_size q.col.isLt.le
  simp only [queryBits, pair_length, BinaryNatCode.length_encode, queryBitBound]
  omega

theorem frameBits_length_le (enc : R → List Bool) (H E b : ℕ)
    (hb : ∀ x, (enc x).length ≤ b) (f : Frame R n)
    (hh : f.parent.height ≤ H) (he : f.parent.exponent ≤ E) :
    (frameBits enc f).length ≤ frameBitBound n H E b := by
  cases f with
  | left q k acc =>
      have hq := queryBits_length_le q H E hh he
      have hk := Nat.size_le_size k.isLt.le
      have ha := hb acc
      simp only [frameBits, List.length_cons, pair_length, BinaryNatCode.length_encode, frameBitBound]
      omega
  | right q k acc lhs =>
      have hq := queryBits_length_le q H E hh he
      have hk := Nat.size_le_size k.isLt.le
      have ha := hb acc
      have hl := hb lhs
      simp only [frameBits, List.length_cons, pair_length, BinaryNatCode.length_encode, frameBitBound]
      omega

theorem stackBits_length_le (enc : R → List Bool) (F : ℕ) (stack : List (Frame R n))
    (hF : ∀ f ∈ stack, (frameBits enc f).length ≤ F) :
    (stackBits enc stack).length ≤ stack.length * (2 * F + 3) := by
  induction stack with
  | nil => simp [stackBits]
  | cons f stack ih =>
      have hf := hF f List.mem_cons_self
      have ht := ih (fun g hg => hF g (List.mem_cons_of_mem _ hg))
      simp only [stackBits, List.length_cons, pair_length]
      nlinarith

theorem stateBits_length_le (enc : R → List Bool) (H E b : ℕ)
    (hb : ∀ x, (enc x).length ≤ b) (s : State R n) (hs : Fits H E s) :
    (stateBits enc s).length ≤ stateBitBound n H E b := by
  have hstack : ∀ (stack : List (Frame R n)), stack.length ≤ H →
      (∀ f ∈ stack, f.parent.height ≤ H) → (∀ f ∈ stack, f.parent.exponent ≤ E) →
      (stackBits enc stack).length ≤ H * (2 * frameBitBound n H E b + 3) := by
    intro stack hl hh he
    exact (stackBits_length_le enc _ stack
      (fun f hf => frameBits_length_le enc H E b hb f (hh f hf) (he f hf))).trans
        (Nat.mul_le_mul_right _ hl)
  cases s with
  | eval q stack =>
      obtain ⟨he, hf, hp⟩ := hs
      have hlen := hf.length_le
      have hq := queryBits_length_le q H E (by omega) he
      have ht := hstack stack (by omega) hf.parents_le hp
      simp only [stateBits, List.length_cons, pair_length, stateBitBound]
      omega
  | ret x stack =>
      obtain ⟨hf, hp⟩ := hs
      have ht := hstack stack (by simpa using hf.length_le) hf.parents_le hp
      have hx := hb x
      simp only [stateBits, List.length_cons, pair_length, stateBitBound]
      omega
  | done x =>
      have hx := hb x
      simp only [stateBits, List.length_cons, stateBitBound]
      omega

theorem run_stateBits_length_le [Semiring R] (A : Matrix (Fin n) (Fin n) R)
    (enc : R → List Bool) (b : ℕ) (hb : ∀ x, (enc x).length ≤ b)
    (e t : ℕ) (i j : Fin n) :
    (stateBits enc ((step A)^[t] (.eval ⟨e.size, e, i, j⟩ []))).length ≤
      stateBitBound n e.size e b := by
  apply stateBits_length_le enc e.size e b hb
  apply iterate_fits A e.size e t
  exact ⟨le_rfl, .nil le_rfl, by simp⟩

def residueBits {m : ℕ} (x : ZMod m) : List Bool := BinaryNatCode.encode x.val

theorem residueBits_injective (m : ℕ) [NeZero m] :
    Function.Injective (residueBits (m := m)) := by
  intro x y h
  exact ZMod.val_injective m (BinaryNatCode.encode_injective h)

theorem residueBits_length_le (m : ℕ) [NeZero m] (x : ZMod m) :
    (residueBits x).length ≤ m.size := by
  simpa only [residueBits, BinaryNatCode.length_encode] using
    Nat.size_le_size (ZMod.val_lt x).le

/-- The dimension, exponent and modulus may all vary. Only their binary lengths
enter the representation-size bound; no full matrix is part of a state. -/
theorem run_residueBits_length_le (m : ℕ) [NeZero m]
    (A : Matrix (Fin n) (Fin n) (ZMod m)) (e t : ℕ) (i j : Fin n) :
    (stateBits residueBits ((step A)^[t] (.eval ⟨e.size, e, i, j⟩ []))).length ≤
      stateBitBound n e.size e m.size :=
  run_stateBits_length_le A residueBits m.size (residueBits_length_le m) e t i j

theorem run_residueBits_quadratic (m : ℕ) [NeZero m]
    (A : Matrix (Fin n) (Fin n) (ZMod m)) (e t : ℕ) (i j : Fin n) :
    (stateBits residueBits ((step A)^[t] (.eval ⟨e.size, e, i, j⟩ []))).length ≤
      64 * (n.size + e.size + m.size + 1) ^ 2 :=
  (run_residueBits_length_le m A e t i j).trans (stateBitBound_size_le n e m.size)

end LeanCanny.Algebra.MatrixPower
