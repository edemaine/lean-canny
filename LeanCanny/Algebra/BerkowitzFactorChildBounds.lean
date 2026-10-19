/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BerkowitzFactorChildCorrect

/-!
# Termination and resource bounds for the factor-entry child

The child halts for the first time at its mathematical clock. Both its packet
length and the logarithm of its clock are bounded using only the original
dimension and modulus lengths, together with the retained request packet.
-/

@[expose] public section

namespace LeanCanny.Algebra.Berkowitz.FactorChild
open LeanCanny.Encoding
open Complexity
open MatrixPower

theorem moment_conditions (a : Access) (p : List Bool) (n s t d k : ℕ)
    (hd : a.dimension (pairFst p) = BinaryNatCode.encode n) (hq : DecodedAt a p s t d k)
    (hmode : QueryBits.selector a.dimension p = [true, true]) :
    s + 1 = t ∧ s < n ∧ d < k ∧ k ≤ n - s - 1 := by
  apply (QueryBits.select_moment_iff n s t d k).mp
  exact (selector_code a p n s t d k hd hq).symm.trans hmode

theorem first_halt (a : Access) (p : List Bool) (m n s t d k : ℕ) [NeZero m]
    (A : Matrix (Fin n) (Fin n) (ZMod m)) (hb : CorrectAt a (pairFst p) m A)
    (hq : DecodedAt a p s t d k) :
    (∀ u < time a p, halted ((advance a)^[u] (start a p)) = false) ∧
      halted ((advance a)^[time a p] (start a p)) = true := by
  by_cases hmode : QueryBits.selector a.dimension p = [true, true]
  · have hs := (moment_conditions a p n s t d k hb.dimension hq hmode).2.1
    have hd := remaining_code a p n s t d k hb.dimension hq
    have he := exponent_code a p s t d k hq
    have hc := EntryAccess.momentCallbacks_correctAt a.dimension a.entry a.modulus p m n s A hs
      hb.dimension hq.sourceLayer hb.modulus hb.entry
    rw [time_moment a p n s t d k hb.dimension hq hmode]
    simp only [start, hmode, ↓reduceIte, advance, callbacks, halted]
    exact ⟨fun u hu => MatrixMoment.EntryBits.halted_before _ _ _ p m (n - s - 1)
      (k - (d + 1)) _ _ _ hc hd he u hu,
      MatrixMoment.EntryBits.halted_after _ _ _ p m (n - s - 1)
        (k - (d + 1)) _ _ _ hc hd he⟩
  · rw [time_immediate a p hmode]
    constructor
    · intro u hu
      omega
    · simp only [Function.iterate_zero, id_eq, start, hmode, ↓reduceIte]
      exact immediate_halted a p

theorem run_length (a : Access) (p : List Bool) (m n s t d k : ℕ) [NeZero m]
    (A : Matrix (Fin n) (Fin n) (ZMod m)) (hb : CorrectAt a (pairFst p) m A)
    (hq : DecodedAt a p s t d k) (u : ℕ) (hu : u ≤ time a p) :
    ((advance a)^[u] (start a p)).length ≤
      2 * p.length + 2 + 64 * (2 * (n + 2).size + m.size + 1) ^ 2 := by
  by_cases hmode : QueryBits.selector a.dimension p = [true, true]
  · have hm := moment_conditions a p n s t d k hb.dimension hq hmode
    have hs := hm.2.1
    have hd := remaining_code a p n s t d k hb.dimension hq
    have he := exponent_code a p s t d k hq
    have hc := EntryAccess.momentCallbacks_correctAt a.dimension a.entry a.modulus p m n s A hs
      hb.dimension hq.sourceLayer hb.modulus hb.entry
    have hl := MatrixMoment.EntryBits.run_length (EntryAccess.momentAccess a.dimension a.entry)
      (EntryAccess.childModulus a.modulus) (QueryBits.momentExponent a.dimension) p m (n - s - 1)
      (k - (d + 1)) _ _ _ hc hd he u
    simp only [start, hmode, ↓reduceIte, advance, callbacks]
    have hdim : (n - s - 1 + 2).size ≤ (n + 2).size := Nat.size_le_size (by omega)
    have hexp : (k - (d + 1) + 2).size ≤ (n + 2).size := Nat.size_le_size (by omega)
    exact hl.trans (Nat.add_le_add_left (Nat.mul_le_mul_left 64
      (Nat.pow_le_pow_left (by omega) 2)) _)
  · have hu0 : u = 0 := by rw [time_immediate a p hmode] at hu; omega
    have hf := (run_immediate a p hmode).symm.trans (run_correct a p m n s t d k A hb hq)
    have hv := residueBits_length_le m (value A s t d k)
    rw [← hf] at hv
    simp only [hu0, Function.iterate_zero, id_eq, start, hmode, ↓reduceIte, immediate,
      pair_length, Controller.doneBits, List.length_cons]
    have hpos : 1 ≤ 2 * (n + 2).size + m.size + 1 := by omega
    have hsq := Nat.mul_le_mul_left (2 * (n + 2).size + m.size + 1) hpos
    simp only [Nat.mul_one, ← pow_two] at hsq
    omega

theorem time_le (a : Access) (p : List Bool) (m n s t d k : ℕ)
    (A : Matrix (Fin n) (Fin n) (ZMod m)) (hb : CorrectAt a (pairFst p) m A)
    (hq : DecodedAt a p s t d k) :
    time a p ≤ 2 ^ (((n + 2).size + 2) * (n + 2).size + 1) := by
  by_cases hmode : QueryBits.selector a.dimension p = [true, true]
  · have hm := moment_conditions a p n s t d k hb.dimension hq hmode
    rw [time_moment a p n s t d k hb.dimension hq hmode]
    have hdim : (n - s - 1 + 2).size ≤ (n + 2).size := Nat.size_le_size (by omega)
    have hexp : (k - (d + 1) + 2).size ≤ (n + 2).size := Nat.size_le_size (by omega)
    apply (MatrixPower.work_add_one_le_two_pow _ _ _).trans
    apply Nat.pow_le_pow_right (by decide)
    exact Nat.add_le_add_right (Nat.mul_le_mul (Nat.add_le_add_right hdim 2) hexp) 1
  · rw [time_immediate a p hmode]
    exact Nat.zero_le _

end LeanCanny.Algebra.Berkowitz.FactorChild
