/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedGlobalHeightControls
public import LeanCanny.Algebra.IntegralMixedHistoryContinuation
/-! # Actual tagged mixed continuations obey one original-spatial ceiling

One scalar width, birth cap, spatial degree and source coefficient bound
are fixed before interpretation. Every integer or physical critical birth
updates the retained bank under the same multiplicative height factor.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedScriptHeightBounds
open LeanCanny.Encoding LeanCanny.Computation FixedWidthPolynomial UniformIntegralPrefix
open IntegralMixedHistory IntegralMixedHistoryScript IntegralMixedGlobalHeightBounds
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def CommandBounds {n B : ℕ} (C L : ℕ) : Command n B → Prop
  | .integer p _ _ => ∀ k, (p.coeff k).natAbs ≤ 2 ^ C
  | .critical r => (∀ i, (r.heights i).nodes ≤ L) ∧
      (∀ i, (r.heights i).CoefficientsBound C) ∧ (∀ i, (r.scales i).natAbs.size ≤ C)

def scriptHeight (n S B W D L C j : ℕ) : ℕ :=
  height n (count (S + 1) B) W D (2 ^ B) S L C j

theorem scriptHeight_step (n S B W D L C j : ℕ) :
    scriptHeight n S B W D L C (j + 1) =
      growth n (count (S + 1) B) W D (2 ^ B) S L * scriptHeight n S B W D L C j :=
  height_step _ _ _ _ _ _ _ _ _

theorem source_le_scriptHeight (n S B W D L C j : ℕ) : C + 1 ≤ scriptHeight n S B W D L C j :=
  source_le_height _ _ _ _ _ _ _ _ _

theorem step_bounds {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (x : State P S B m ι) (hm : m ≤ S) (command : Command n B) (G C M W D L : ℕ)
    (HG : x.bank.Bounds G) (HC : ∀ e, (P.low.coeff e).natAbs ≤ 2 ^ C)
    (HP : P.leading.natAbs.size ≤ C) (hM : count m B ≤ M) (hW : P.degree.size ≤ W) (hD : P.degree ≤ D)
    (hcommand : CommandBounds C L command) (hG : C + 1 ≤ G) :
    (step x hm command).bank.Bounds (growth n M W D (2 ^ B) S L * G) := by
  cases command with
  | integer p hp hcap => exact integerStep_scaled_bounds x hm p hp hcap G C M W D L HG hcommand hM hG
  | critical r =>
    exact criticalStep_scaled_bounds x hm r G C M W D L HG HC HP hM hW hD
      hcommand.1 hcommand.2.1 hcommand.2.2 hG

theorem continueRun_bounds {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State P S B m ι) (W D L C : ℕ)
    (HC : ∀ e, (P.low.coeff e).natAbs ≤ 2 ^ C) (HP : P.leading.natAbs.size ≤ C)
    (hW : P.degree.size ≤ W) (hD : P.degree ≤ D)
    (HI : initial.bank.Bounds (scriptHeight n S B W D L C m)) (cs : List (Command n B)) :
    ∀ (hlen : m + cs.length ≤ S + 1) (_ : ∀ command ∈ cs, CommandBounds C L command),
      (continueRun initial cs hlen).bank.Bounds (scriptHeight n S B W D L C (m + cs.length)) := by
  induction cs with
  | nil => intro _ _; simpa only [continueRun, List.length_nil, Nat.add_zero] using HI
  | cons command cs ih =>
    intro hlen hall
    have HT : m + cs.length ≤ S + 1 := by simp only [List.length_cons] at hlen; omega
    have HM : m + cs.length ≤ S := by simp only [List.length_cons] at hlen; omega
    have HB := ih HT (fun c hc => hall c (List.mem_cons_of_mem _ hc))
    have HR : count (m + cs.length) B ≤ count (S + 1) B := Nat.pow_le_pow_right (Nat.two_pow_pos _) HT
    have HS := step_bounds (continueRun initial cs HT) HM command
      (scriptHeight n S B W D L C (m + cs.length)) C (count (S + 1) B) W D L HB HC HP HR hW hD
      (hall command List.mem_cons_self) (source_le_scriptHeight _ _ _ _ _ _ _ _)
    simpa only [continueRun, List.length_cons, Nat.add_succ, scriptHeight_step] using HS

theorem continueRun_from_empty_bounds {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State P S B 0 ι) (W D L C : ℕ)
    (HC : ∀ e, (P.low.coeff e).natAbs ≤ 2 ^ C) (HP : P.leading.natAbs.size ≤ C)
    (hW : P.degree.size ≤ W) (hD : P.degree ≤ D) (cs : List (Command n B))
    (hlen : cs.length ≤ S + 1) (hall : ∀ command ∈ cs, CommandBounds C L command) :
    (continueRun initial cs (by simpa only [Nat.zero_add] using hlen)).bank.Bounds
      (scriptHeight n S B W D L C cs.length) := by
  have HI : initial.bank.Bounds (scriptHeight n S B W D L C 0) := by
    constructor
    · intro i; exact Fin.elim0 i
    · intro i; exact Fin.elim0 i
  simpa only [Nat.zero_add] using continueRun_bounds initial W D L C HC HP hW hD HI cs
    (by simpa only [Nat.zero_add] using hlen) hall

theorem scriptHeight_binary {n S B W D L C j : List Bool → ℕ} (hn : UnaryFn n) (hS : UnaryFn S)
    (hB : UnaryFn B) (hW : UnaryFn W) (hD : BinaryFn D) (hL : BinaryFn L) (hC : BinaryFn C) (hj : UnaryFn j) :
    BinaryFn (fun c => scriptHeight (n c) (S c) (B c) (W c) (D c) (L c) (C c) (j c)) :=
  height_binary hn (((BinaryFn.const 2).powUnary hB).powUnary (hS.add (UnaryFn.const 1)))
    hW hD ((BinaryFn.const 2).powUnary hB) (BinaryFn.ofUnary hS) hL hC hj

theorem scriptHeight_bits (n S B W D L C j : ℕ) :
    (scriptHeight n S B W D L C j).size ≤
      (growth n (count (S + 1) B) W D (2 ^ B) S L).size * j + (C + 1).size + 1 :=
  height_bits _ _ _ _ _ _ _ _ _

end LeanCanny.Algebra.IntegralMixedScriptHeightBounds
