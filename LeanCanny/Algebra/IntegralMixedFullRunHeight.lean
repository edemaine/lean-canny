/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullScriptHeight
/-! # Literal full continuations, including padded integer-X births, obey the ceiling -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullScriptHeight
open LeanCanny.Encoding LeanCanny.Computation FixedWidthPolynomial UniformIntegralPrefix
open IntegralMixedHistory IntegralMixedFullHistoryScript
set_option backward.isDefEq.respectTransparency false

variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

theorem continueRun_bounds (initial : State P S B m ι) (W D L C : ℕ)
    (HC : ∀ e, (P.low.coeff e).natAbs ≤ 2 ^ C) (HP : P.leading.natAbs.size ≤ C)
    (hW : P.degree.size ≤ W) (hD : P.degree ≤ D)
    (hB : IntegralMixedExceptionalBounds.auxiliaryCap (n + 1) P.degree ≤ 2 ^ B)
    (HI : initial.bank.Bounds (height n S B W D L C m)) (cs : List (Command P B)) :
    ∀ (hlen : m + cs.length ≤ S + 1) (_ : ∀ command ∈ cs, CommandBounds C L command),
      (continueRun initial cs hlen).bank.Bounds (height n S B W D L C (m + cs.length)) := by
  induction cs with
  | nil => intro _ _; simpa only [continueRun, List.length_nil, Nat.add_zero] using HI
  | cons c cs ih =>
    intro hlen hall
    have HT : m + cs.length ≤ S + 1 := by simp only [List.length_cons] at hlen; omega
    have HM : m + cs.length ≤ S := by simp only [List.length_cons] at hlen; omega
    have HB := ih HT (fun command hc => hall command (List.mem_cons_of_mem _ hc))
    have HS := step_bounds (continueRun initial cs HT) HM c (height n S B W D L C (m + cs.length)) C W D L
      HB HC HP hW hD hB (hall c List.mem_cons_self) (source_le_height _ _ _ _ _ _ _ _)
    simpa only [continueRun, List.length_cons, Nat.add_succ, height_step] using HS

theorem run_bounds (initial : State P S B 0 ι) (W D L C : ℕ)
    (HC : ∀ e, (P.low.coeff e).natAbs ≤ 2 ^ C) (HP : P.leading.natAbs.size ≤ C)
    (hW : P.degree.size ≤ W) (hD : P.degree ≤ D)
    (hB : IntegralMixedExceptionalBounds.auxiliaryCap (n + 1) P.degree ≤ 2 ^ B)
    (cs : List (Command P B)) : ∀ (hlen : cs.length ≤ S + 1) (_ : ∀ command ∈ cs, CommandBounds C L command),
      (run initial cs hlen).bank.Bounds (height n S B W D L C cs.length) := by
  induction cs with
  | nil =>
    intro _ _
    constructor
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
  | cons c cs ih =>
    intro hlen hall
    have HT : cs.length ≤ S + 1 := by simp only [List.length_cons] at hlen; omega
    have HM : cs.length ≤ S := by simp only [List.length_cons] at hlen; omega
    have HB := ih HT (fun command hc => hall command (List.mem_cons_of_mem _ hc))
    have HS := step_bounds (run initial cs HT) HM c (height n S B W D L C cs.length) C W D L
      HB HC HP hW hD hB (hall c List.mem_cons_self) (source_le_height _ _ _ _ _ _ _ _)
    simpa only [run, List.length_cons, height_step] using HS

theorem default_bounds (C L : ℕ) : CommandBounds (P := P) (B := B) C L defaultCommand := by
  change ∀ k, ((Polynomial.X : Polynomial ℤ).coeff k).natAbs ≤ 2 ^ C
  intro k
  rw [Polynomial.coeff_X]
  split_ifs
  · simpa only [Int.natAbs_one] using (Nat.one_le_two_pow : 1 ≤ 2 ^ C)
  · simp only [Int.natAbs_zero, Nat.zero_le]

theorem padded_command_bounds (cs : List (Command P B)) (birth C L : ℕ)
    (hall : ∀ command ∈ cs, CommandBounds C L command) : ∀ command ∈ paddedPast cs birth, CommandBounds C L command := by
  intro command hc
  rcases List.mem_append.mp hc with hr | hp
  · have HE := List.eq_of_mem_replicate hr
    subst command
    exact default_bounds C L
  · have HT := List.mem_of_mem_take (List.mem_reverse.mp hp)
    exact hall command (List.mem_reverse.mp HT)

theorem paddedRun_bounds (initial : State P S B 0 ι) (W D L C : ℕ)
    (HC : ∀ e, (P.low.coeff e).natAbs ≤ 2 ^ C) (HP : P.leading.natAbs.size ≤ C)
    (hW : P.degree.size ≤ W) (hD : P.degree ≤ D)
    (hB : IntegralMixedExceptionalBounds.auxiliaryCap (n + 1) P.degree ≤ 2 ^ B)
    (cs : List (Command P B)) (birth : ℕ) (hlen : birth ≤ S + 1) (hall : ∀ command ∈ cs, CommandBounds C L command) :
    (run initial (paddedPast cs birth) (by rw [paddedPast_length]; exact hlen)).bank.Bounds (height n S B W D L C birth) := by
  have HB := run_bounds initial W D L C HC HP hW hD hB (paddedPast cs birth)
    (by rw [paddedPast_length]; exact hlen) (padded_command_bounds cs birth C L hall)
  exact HB.mono (congrArg (fun j => height n S B W D L C j) (paddedPast_length cs birth)).le

theorem height_mono (n S B W D L C : ℕ) {i j : ℕ} (h : i ≤ j) : height n S B W D L C i ≤ height n S B W D L C j :=
  Nat.mul_le_mul_right (C + 1) (Nat.pow_le_pow_right (growth_pos n S B W D L) h)
end LeanCanny.Algebra.IntegralMixedFullScriptHeight
