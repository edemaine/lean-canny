/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import LeanCanny.Computation.PolyTimeArithmetic
public import LeanCanny.Computation.PolyTimeIteration
public import LeanCanny.Computation.PolyTimeRange
public import LeanCanny.Tactic.PolyTime.Init
public import Complexity.Tactic.PolyTime
public import Mathlib.Data.Finset.Card

/-! # Polynomial-time automation through Complexitylib

`polytime` normalizes the project's `FP`, `UnaryFn`, and `FPPred` interfaces,
then uses Complexitylib's `fun_prop` and `PolyTime` certificate search. Local
predicate certificates expose their Boolean verdicts. The project contributes
only rules for its raw packet/range conventions and convenient unary bounds;
composition, named routine lookup, and search belong to the upstream tools.

Use `polytime [program]` to unfold selected definitions. Register native named
certificates with `@[program_certificate]`; they also become `fun_prop` rules.
-/

public section
namespace LeanCanny.Tactic.PolyTime
open Turing.MultiTapeTM

/-- Normalize unary certificates before matching local hypotheses. -/
theorem unary_rule {f : List Bool → ℕ} :
    (fun x => List.replicate (f x) true) ∈ FP ↔ UnaryFn f := unaryFn_iff.symm

/-- Present a predicate goal as its ordinary Boolean decision program. -/
theorem native_predicate_rule {p : List Bool → Prop} [DecidablePred p]
    (h : ComputableTidilyInPolyTime (fun z => decide (p z))
      encBits encBool) : FPPred p :=
  FPPred.of_computable h (fun _ => decide_eq_true_iff.symm)

/-- A Boolean verdict is unchanged by deciding that it is true. -/
theorem native_decide_bool (b : Bool) [Decidable (b = true)] :
    decide (b = true) = b := by cases b <;> simp

open Lean Meta Elab Tactic in
/-- Expose local predicate routines as ordinary Boolean programs for composition. -/
elab "canny_native_certificates" : tactic => do
  let declarations ← withMainContext do
    return (← getLCtx).getFVarIds
  let mut rewrites : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := #[]
  for fvar in declarations do
    let predicate? ← withMainContext do
      let decl ← fvar.getDecl
      if decl.isImplementationDetail || !decl.type.consumeMData.isAppOf ``FPPred then
        return none
      let duplicate ← mkFreshUserName `predicateCertificate
      let goal ← getMainGoal
      let (_, goal) ← (← goal.assert duplicate decl.type decl.toExpr).intro1P
      replaceMainGoal [goal]
      return some (mkIdent duplicate)
    if let some duplicate := predicate? then
      let verdict ← mkIdent <$> mkFreshUserName `verdict
      let bits ← mkIdent <$> mkFreshUserName `verdictBits
      let equivalence ← mkIdent <$> mkFreshUserName `verdict_eq
      let native ← mkIdent <$> mkFreshUserName `nativeVerdict
      evalTactic (← `(tactic| obtain ⟨$verdict, $bits, $equivalence⟩ := $duplicate))
      evalTactic (← `(tactic|
        have $native : ComputableTidilyInPolyTime $verdict encBits encBool :=
          flag_computable $bits))
      rewrites := rewrites.push (← `(Lean.Parser.Tactic.simpLemma| $equivalence:ident))
  withMainContext do
    if (← getMainTarget).consumeMData.isAppOf ``FPPred then
      liftMetaTactic fun goal => goal.applyConst ``native_predicate_rule
  if !rewrites.isEmpty then
    evalTactic (← `(tactic| simp only [$[$rewrites],*, native_decide_bool] at *))

/-- Bounded scans expose the input and unary index directly to native composition. -/
@[fun_prop]
theorem native_forall_lt {n : List Bool → ℕ} {p : List Bool → ℕ → Prop}
    [∀ z i, Decidable (p z i)] [∀ z, Decidable (∀ i < n z, p z i)]
    (hn : ComputableTidilyInPolyTime n encBits encUnary)
    (hp : ComputableTidilyInPolyTime (fun q : List Bool × ℕ => decide (p q.1 q.2))
      (encPair encBits encUnary) encBool) :
    ComputableTidilyInPolyTime (fun z => decide (∀ i < n z, p z i)) encBits encBool := by
  have h := ComputableTidilyInPolyTime.allWithInput
    (test := fun z i => decide (p z i)) (ComputableTidilyInPolyTime.range.comp hn) hp
  have heq (z : List Bool) :
      (List.range (n z)).all (fun i => decide (p z i)) = decide (∀ i < n z, p z i) := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.all_eq_true, List.mem_range, decide_eq_true_eq]
  simpa only [Function.comp_apply, heq] using h

@[fun_prop]
theorem native_exists_lt {n : List Bool → ℕ} {p : List Bool → ℕ → Prop}
    [∀ z i, Decidable (p z i)] [∀ z, Decidable (∃ i < n z, p z i)]
    (hn : ComputableTidilyInPolyTime n encBits encUnary)
    (hp : ComputableTidilyInPolyTime (fun q : List Bool × ℕ => decide (p q.1 q.2))
      (encPair encBits encUnary) encBool) :
    ComputableTidilyInPolyTime (fun z => decide (∃ i < n z, p z i)) encBits encBool := by
  have h := ComputableTidilyInPolyTime.anyWithInput
    (test := fun z i => decide (p z i)) (ComputableTidilyInPolyTime.range.comp hn) hp
  have heq (z : List Bool) :
      (List.range (n z)).any (fun i => decide (p z i)) = decide (∃ i < n z, p z i) := by
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, List.mem_range, decide_eq_true_eq]
  simpa only [Function.comp_apply, heq] using h

/-- Counting uses the upstream typed traversal, including arbitrary decision instances. -/
@[program_certificate hn hp]
theorem native_count {n : List Bool → ℕ} {p : List Bool → ℕ → Prop}
    [∀ z i, Decidable (p z i)]
    (hn : ComputableTidilyInPolyTime n encBits encUnary)
    (hp : ComputableTidilyInPolyTime (fun q : List Bool × ℕ => decide (p q.1 q.2))
      (encPair encBits encUnary) encBool) :
    ComputableTidilyInPolyTime
      (fun z => ((Finset.range (n z)).filter (p z)).card) encBits encUnary := by
  have h := ComputableTidilyInPolyTime.countPWithInput
    (test := fun z i => decide (p z i)) (ComputableTidilyInPolyTime.range.comp hn) hp
  have heq (z : List Bool) : (List.range (n z)).countP (fun i => decide (p z i)) =
      ((Finset.range (n z)).filter (p z)).card := by
    simpa only [List.toFinset_range] using
      ((show (List.range (n z)).Nodup from List.nodup_range).card_eq_countP (P := p z)).symm
  simpa only [Function.comp_apply, heq] using h

-- Native forwarding certificates preserve the fluent `UnaryFn` API while
-- exposing both premises and conclusions to upstream recursive composition.
@[fun_prop]
theorem native_max {f g : List Bool → ℕ}
    (hf : ComputableTidilyInPolyTime f encBits encUnary)
    (hg : ComputableTidilyInPolyTime g encBits encUnary) :
    ComputableTidilyInPolyTime (fun z => max (f z) (g z)) encBits encUnary := UnaryFn.max hf hg

@[fun_prop]
theorem native_div {f g : List Bool → ℕ}
    (hf : ComputableTidilyInPolyTime f encBits encUnary)
    (hg : ComputableTidilyInPolyTime g encBits encUnary) :
    ComputableTidilyInPolyTime (fun z => f z / g z) encBits encUnary := UnaryFn.div hf hg

@[fun_prop]
theorem native_mod {f g : List Bool → ℕ}
    (hf : ComputableTidilyInPolyTime f encBits encUnary)
    (hg : ComputableTidilyInPolyTime g encBits encUnary) :
    ComputableTidilyInPolyTime (fun z => f z % g z) encBits encUnary := UnaryFn.mod hf hg

@[fun_prop]
theorem native_size {f : List Bool → ℕ}
    (hf : ComputableTidilyInPolyTime f encBits encUnary) :
    ComputableTidilyInPolyTime (fun z => (f z).size) encBits encUnary := UnaryFn.size hf

@[fun_prop]
theorem native_sum {n f : List Bool → ℕ}
    (hn : ComputableTidilyInPolyTime n encBits encUnary)
    (hf : ComputableTidilyInPolyTime f encBits encUnary) :
    ComputableTidilyInPolyTime (fun z => Finset.sum (Finset.range (n z))
      (fun i => f (pair z (List.replicate i true)))) encBits encUnary := UnaryFn.sum hn hf

@[fun_prop]
theorem native_bits {n : List Bool → ℕ}
    (hn : ComputableTidilyInPolyTime n encBits encUnary) :
    ComputableTidilyInPolyTime (fun z => (n z).bits) encBits encBits := bits_mem_FP hn

/-- Normalize project interfaces, then use Complexitylib's certificate search. -/
macro "native_polytime" : tactic => `(tactic|
  (classical
   canny_native_certificates
   try simp only [unary_rule] at *
   try dsimp only [FP, Set.mem_ofPred_eq, UnaryFn] at *
   solve
   | fun_prop (config := { maxSteps := 256 })
   | aesop (config := { assumptionTransparency := .reducible, maxRuleApplications := 1000, maxRuleApplicationDepth := 100 })
       (rule_sets := [PolyTime])))

/-- Polynomial-time certificates use the upstream automation after normalization. -/
macro "polytime" : tactic => `(tactic| native_polytime)

/-- Unfold selected programs before synthesizing their efficiency certificate. -/
macro "polytime" "[" names:ident,* "]" : tactic =>
  `(tactic| (unfold $names*; native_polytime))

end LeanCanny.Tactic.PolyTime
