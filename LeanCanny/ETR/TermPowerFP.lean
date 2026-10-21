/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TermView
public import LeanCanny.ETR.SumSquaresFP
public import LeanCanny.ETR.FinitePolynomial

/-! # Polynomial-time writing of polynomially bounded source powers

The writer retains the validated source once and appends one multiplication
per round. A unary FP exponent gives a polynomial-sized expression, without
expanding any monomials. Invalid source words retain the zero-term default.
-/

@[expose] public section

namespace LeanCanny.ETR.Term

def power (t : Term) : ℕ → Term
  | 0 => .const 1
  | n + 1 => .mul t (power t n)

theorem finitePolynomial_power (t : Term) (A n : ℕ) :
    finitePolynomial A (power t n) = finitePolynomial A t ^ n := by
  induction n with
  | zero => simp [power, finitePolynomial]
  | succ n ih => simp only [power, finitePolynomial, ih, pow_succ']

theorem arity_power (t : Term) (n : ℕ) (hn : 0 < n) : (power t n).arity = t.arity := by
  cases n with
  | zero => omega
  | succ n =>
    induction n with
    | zero => simp [power, arity]
    | succ n ih =>
      change max t.arity (t.power (n + 1)).arity = t.arity
      rw [ih (by omega), max_self]

end LeanCanny.ETR.Term

namespace LeanCanny.ETR.TermPower

open LeanCanny.Encoding

def step (p : List Bool) : List Bool :=
  pair (pairFst p) (Codec.taggedTwo 3 (pairFst p) (pairSnd p))

theorem step_mem_FP : step ∈ FP :=
  mem_FP_pair pairFst_mem_FP (Codec.taggedTwo_mem_FP 3 pairFst_mem_FP pairSnd_mem_FP)

theorem iterate_pair_exists (f a : List Bool) (n : ℕ) : ∃ b, step^[n] (pair f a) = pair f b := by
  induction n with
  | zero => exact ⟨a, rfl⟩
  | succ n ih =>
    obtain ⟨b, hb⟩ := ih
    exact ⟨Codec.taggedTwo 3 f b, by rw [Function.iterate_succ_apply', hb, step, pairFst_pair, pairSnd_pair]⟩

theorem iterate_pair_length (f a : List Bool) (n : ℕ) :
    (step^[n] (pair f a)).length = (pair f a).length + n * (f.length + 10) := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨b, hb⟩ := iterate_pair_exists f a n
    rw [hb] at ih
    rw [Function.iterate_succ_apply', hb, step, pairFst_pair, pairSnd_pair]
    simp only [pair_length, SumSquares.taggedTwo_length, Nat.add_mul, Nat.one_mul] at *
    omega

def write (source : List Bool → List Bool) (exponent : List Bool → ℕ) (c : List Bool) : List Bool :=
  pairSnd (step^[exponent c] (pair (TermView.normalize (source c)) (Term.const 1).toData.toBits))

theorem write_mem_FP {source : List Bool → List Bool} {exponent : List Bool → ℕ}
    (hs : source ∈ FP) (he : UnaryFn exponent) : write source exponent ∈ FP := by
  have hn := mem_FP_comp hs TermView.normalize_mem_FP
  have hi := mem_FP_pair hn (constFn_mem_FP (Term.const 1).toData.toBits)
  obtain ⟨p, hp⟩ := output_length_poly_of_mem_FP hi
  obtain ⟨q, hq⟩ := output_length_poly_of_mem_FP he
  obtain ⟨r, hr⟩ := output_length_poly_of_mem_FP hn
  have hb := (PolyBound.eval p).add ((PolyBound.eval q).mul ((PolyBound.eval r).add (PolyBound.const 10)))
  have hloop := iterate_mem_FP_of_polyBound step_mem_FP hi he hb (by
    intro c n hnc
    rw [iterate_pair_length]
    have hinit := hp c
    have hexp := hq c
    simp only [List.length_replicate] at hexp hnc
    exact Nat.add_le_add hinit (Nat.mul_le_mul (hnc.trans hexp) (Nat.add_le_add_right (hr c) 10)))
  have h := mem_FP_comp hloop pairSnd_mem_FP
  exact mem_FP_of_eq h (fun _ => by simp only [write, Function.comp_apply, List.length_replicate])

theorem iterate_term (t : Term) (n : ℕ) :
    step^[n] (pair t.toData.toBits (Term.const 1).toData.toBits) = pair t.toData.toBits (t.power n).toData.toBits := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, step, pairFst_pair, pairSnd_pair, Term.power, Term.mul_toBits]

theorem write_correct (source : List Bool → List Bool) (exponent : List Bool → ℕ) (c : List Bool) :
    write source exponent c = ((TermView.term (source c)).power (exponent c)).toData.toBits := by
  rw [write, TermView.normalize_eq_term, iterate_term, pairSnd_pair]

end LeanCanny.ETR.TermPower
