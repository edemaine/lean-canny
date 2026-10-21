/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.BoundedFoldSpace
public import LeanCanny.Computation.SpaceFunctionBranch
public import LeanCanny.Encoding.BinaryModFP
public import Mathlib.Data.Nat.Prime.Defs

/-!
# A certified binary primality predicate by trial division

The loop scans divisors below the input value and retains one Boolean flag.
Binary modular reduction and comparisons make each update FP. The exponential
iteration count is allowed by the bounded-fold certificate; every stored word
still has polynomial length. This supplies the prime guard for CRT moduli.
-/

@[expose] public section

namespace LeanCanny.Algebra.PrimalityBits
open Complexity
open LeanCanny.Encoding
open LeanCanny.Computation

def seed (c : List Bool) : List Bool := [decide (2 ≤ Nat.fromBitsLE c)]

def good (p : List Bool) : Prop :=
  Nat.fromBitsLE (BoundedFold.counter p) < 2 ∨
    Nat.fromBitsLE (pairFst p) % Nat.fromBitsLE (BoundedFold.counter p) ≠ 0

instance (p : List Bool) : Decidable (good p) := inferInstanceAs (Decidable (_ ∨ _))

def update (p : List Bool) : List Bool :=
  [((BoundedFold.accumulator p)[0]?.getD false) && decide (good p)]

theorem seed_mem_FP : seed ∈ FP :=
  (BinaryNat.le_fppred (constFn_mem_FP [false, true]) id_mem_FP).flag_mem_FP

theorem good_fppred : FPPred good := by
  have hl := BinaryNat.lt_fppred BoundedFold.counter_mem_FP (constFn_mem_FP [false, true])
  have hm := mem_FP_comp (mem_FP_pair pairFst_mem_FP BoundedFold.counter_mem_FP) BinaryNat.mod_mem_FP
  have hn := BinaryNat.lt_fppred (constFn_mem_FP []) hm
  refine (hl.or hn).of_iff ?_
  intro p
  simp only [good, Function.comp_apply, BinaryNat.mod_eq_bits, pairFst_pair, pairSnd_pair,
    Nat.fromBitsLE_bits, show Nat.fromBitsLE [false, true] = 2 from rfl, show Nat.fromBitsLE [] = 0 from rfl]
  omega

theorem update_mem_FP : update ∈ FP := by
  have hv := FPPred.getBit BoundedFold.accumulator_mem_FP (UnaryFn.const 0)
  have h := (hv.and good_fppred).flag_mem_FP
  refine mem_FP_of_eq (g := update) h ?_
  intro p
  cases hv : (BoundedFold.accumulator p)[0]?.getD false <;> simp [update, hv]

def survives (n : ℕ) : ℕ → Bool
  | 0 => decide (2 ≤ n)
  | d + 1 => survives n d && decide (d < 2 ∨ n % d ≠ 0)

theorem survives_true (n d : ℕ) : survives n d = true ↔
    2 ≤ n ∧ ∀ j < d, 2 ≤ j → ¬ j ∣ n := by
  induction d with
  | zero => simp [survives]
  | succ d ih =>
    rw [survives, Bool.and_eq_true, ih, decide_eq_true_eq]
    have hd : (d < 2 ∨ n % d ≠ 0) ↔ (2 ≤ d → ¬ d ∣ n) := by rw [Nat.dvd_iff_mod_eq_zero]; omega
    rw [hd]
    constructor
    · rintro ⟨⟨hn, hj⟩, hlast⟩
      refine ⟨hn, ?_⟩
      intro j hjd hj2
      by_cases he : j = d
      · exact he ▸ hlast (he ▸ hj2)
      · exact hj j (by omega) hj2
    · rintro ⟨hn, hj⟩
      exact ⟨⟨hn, fun j hlt => hj j (by omega)⟩, hj d (by omega)⟩

theorem survives_self (n : ℕ) : survives n n = decide n.Prime := by
  apply Bool.eq_iff_iff.mpr
  rw [survives_true, decide_eq_true_eq, Nat.prime_def_lt']
  constructor
  · rintro ⟨hn, h⟩
    exact ⟨hn, fun m hm hmn => h m hmn hm⟩
  · rintro ⟨hn, h⟩
    exact ⟨hn, fun m hmn hm => h m hm hmn⟩

theorem fold_eq (c : List Bool) (d : ℕ) :
    BoundedFold.fold update seed c d = [survives (Nat.fromBitsLE c) d] := by
  induction d with
  | zero => rfl
  | succ d ih =>
    rw [BoundedFold.fold, ih]
    simp only [update, good, BoundedFold.context_packet, BoundedFold.counter_packet,
      BoundedFold.accumulator_packet, BinaryNatCode.encode, Nat.fromBitsLE_bits,
      List.getElem?_cons_zero, Option.getD_some, survives]

theorem evaluator : SpaceFunction (fun c => [decide (Nat.fromBitsLE c).Prime]) := by
  let E := BoundedFold.evaluator (SpaceFunction.ofFP update update_mem_FP) id seed id_mem_FP seed_mem_FP 1
    (by intro c i _; rw [fold_eq]; simp only [List.length_singleton, Polynomial.eval_one, le_refl])
  refine E.congr (funext fun c => ?_)
  simp only [id_eq, fold_eq, survives_self]

end LeanCanny.Algebra.PrimalityBits
