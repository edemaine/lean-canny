/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public meta import Lean.Elab.Deriving.Util
public meta import Lean.Elab.Tactic.Basic
public import LeanCanny.AbstractEncodingBridge

/-! # Transfer from the independent mathematical abstract

Structural induction identifies the abstract syntax and solution sets with the
established arithmetic syntax. The encoding bridge supplies the native PSPACE
bounds for the flat library-encoded languages, including malformed inputs.
-/

@[expose] public section
namespace LeanCanny.AbstractBridge
open Encoding.FlatSyntax Turing.MultiTapeTM

theorem reduction_closure {L : Set (List Bool)}
    (h : L ∈ Cslib.Complexity.PSPACE Turing.MultiTapeTM.encBits) :
    {K | Cslib.Complexity.PolyTimeReducible Turing.MultiTapeTM.encBits
      Turing.MultiTapeTM.encBits K L} ⊆
        Cslib.Complexity.PSPACE Turing.MultiTapeTM.encBits := by
  intro K hK
  exact Computation.mem_PSPACE_of_reduction hK h

open Lean Lean.Meta Lean.Elab Lean.Elab.Tactic in
/-- Supply an inductive type's own recursor to a default proof argument.
The final quantified input reveals the type after the conclusion is matched. -/
elab "bridge_induction" : tactic => withMainContext do
  let name ← forallTelescopeReducing (← getMainTarget) fun args _ => do
    if args.isEmpty then throwError "Expected an induction principle"
    let ty ← whnf (← inferType args.back!)
    let .const name _ := ty.getAppFn
      | throwError "Cannot infer the inductive type from {ty}"
    discard <| getConstInfoInduct name
    return name.str "rec"
  evalTactic (← `(tactic| exact @$(mkCIdent name)))

/-! ## Dimension-indexed abstract syntax

All representation assembly stays in the bridge. The abstract supplies only
its induction principles and the defining equations for evaluation and coding.
-/
section Finite
variable {T F : ℕ → Type}
  {const : ∀ {n}, ℤ → T n} {var : ∀ {n}, Fin n → T n}
  {add mul : ∀ {n}, T n → T n → T n}
  {falsum : ∀ {n}, F n} {eqZero ltZero : ∀ {n}, T n → F n}
  {neg : ∀ {n}, F n → F n} {conj disj : ∀ {n}, F n → F n → F n}
  {eval : ∀ {n}, (Fin n → ℝ) → T n → ℝ}
  {solutions : ∀ {n}, F n → Set (Fin n → ℝ)}
  {termCode : ∀ {n}, T n → List Token} {formulaCode : ∀ {n}, F n → List Token}

local notation "holds" => (fun {n : ℕ} (x : Fin n → ℝ) (p : F n) => x ∈ solutions p)

structure FiniteLaws : Prop where
  holds_eqZero : ∀ n (x : Fin n → ℝ) t, holds x (eqZero t) ↔ eval x t = 0
  code_eqZero : ∀ n t, formulaCode (n := n) (eqZero t) = op 3 :: termCode t
  eval_const : ∀ n (x : Fin n → ℝ) z, eval x (const z) = z
  eval_var : ∀ n (x : Fin n → ℝ) i, eval x (var i) = x i
  eval_add : ∀ n (x : Fin n → ℝ) a b, eval x (add a b) = eval x a + eval x b
  eval_mul : ∀ n (x : Fin n → ℝ) a b, eval x (mul a b) = eval x a * eval x b
  holds_falsum : ∀ n (x : Fin n → ℝ), holds x falsum ↔ False
  holds_ltZero : ∀ n (x : Fin n → ℝ) t, holds x (ltZero t) ↔ eval x t < 0
  holds_not : ∀ n (x : Fin n → ℝ) p, holds x (neg p) ↔ ¬ holds x p
  holds_and : ∀ n (x : Fin n → ℝ) p q, holds x (conj p q) ↔ holds x p ∧ holds x q
  holds_or : ∀ n (x : Fin n → ℝ) p q, holds x (disj p q) ↔ holds x p ∨ holds x q
  code_const : ∀ n z, termCode (n := n) (const z) = [.inl z]
  code_var : ∀ n i, termCode (n := n) (var i) = [.inr (i.val + 8)]
  code_add : ∀ n a b, termCode (n := n) (add a b) = op 0 :: (termCode a ++ termCode b)
  code_mul : ∀ n a b, termCode (n := n) (mul a b) = op 1 :: (termCode a ++ termCode b)
  code_falsum : ∀ n, formulaCode (n := n) falsum = [op 2]
  code_ltZero : ∀ n t, formulaCode (n := n) (ltZero t) = op 4 :: termCode t
  code_not : ∀ n p, formulaCode (n := n) (neg p) = op 5 :: formulaCode p
  code_and : ∀ n p q, formulaCode (n := n) (conj p q) = op 6 :: (formulaCode p ++ formulaCode q)
  code_or : ∀ n p q, formulaCode (n := n) (disj p q) = op 7 :: (formulaCode p ++ formulaCode q)

variable
  (ti : ∀ {n} {P : T n → Prop}, (∀ z, P (const z)) → (∀ i, P (var i)) →
    (∀ a b, P a → P b → P (add a b)) →
    (∀ a b, P a → P b → P (mul a b)) → ∀ t, P t)
  (fi : ∀ {n} {P : F n → Prop}, P falsum → (∀ t, P (eqZero t)) →
    (∀ t, P (ltZero t)) → (∀ p, P p → P (neg p)) →
    (∀ p q, P p → P q → P (conj p q)) →
    (∀ p q, P p → P q → P (disj p q)) → ∀ p, P p)
  (h : FiniteLaws (const := const) (var := var) (add := add) (mul := mul)
    (falsum := falsum) (eqZero := eqZero) (ltZero := ltZero)
    (neg := neg) (conj := conj) (disj := disj)
    (eval := eval) (solutions := solutions) (termCode := termCode) (formulaCode := formulaCode))

private def TermRep {n} (t : T n) (a : ETR.Term) : Prop :=
  a.arity ≤ n ∧ termCode t = termTokens a ∧
    ∀ x : Fin n → ℝ, eval x t = a.eval (ETR.Formula.extend x)

private def FormulaRep {n} (p : F n) (a : ETR.Formula) : Prop :=
  a.arity ≤ n ∧ formulaCode p = formulaTokens a ∧
    ∀ x : Fin n → ℝ, holds x p ↔ a.Holds (ETR.Formula.extend x)

include h in
private theorem termRep_const (n : ℕ) (z : ℤ) :
    TermRep (eval := eval) (termCode := termCode) (const z : T n) (.const z) := by
  simp [TermRep, ETR.Term.arity, termTokens,
    h.code_const, ETR.Term.eval, h.eval_const]

include h in
private theorem termRep_var (n : ℕ) (i : Fin n) :
    TermRep (eval := eval) (termCode := termCode) (var i) (.var i.val) := by
  refine ⟨by simp [ETR.Term.arity], ?_, ?_⟩
  · simp [h.code_var, termTokens]
  · intro x
    simp [h.eval_var, ETR.Term.eval, ETR.Formula.extend, i.isLt]

include h in
private theorem termRep_add {n} {a b : T n} {ra rb : ETR.Term}
    (ha : TermRep (eval := eval) (termCode := termCode) a ra)
    (hb : TermRep (eval := eval) (termCode := termCode) b rb) :
    TermRep (eval := eval) (termCode := termCode) (add a b) (.add ra rb) := by
  refine ⟨max_le ha.1 hb.1, ?_, ?_⟩
  · simp [h.code_add, ha.2.1, hb.2.1, termTokens]
  · intro x; simp [h.eval_add, ha.2.2 x, hb.2.2 x, ETR.Term.eval]

include h in
private theorem termRep_mul {n} {a b : T n} {ra rb : ETR.Term}
    (ha : TermRep (eval := eval) (termCode := termCode) a ra)
    (hb : TermRep (eval := eval) (termCode := termCode) b rb) :
    TermRep (eval := eval) (termCode := termCode) (mul a b) (.mul ra rb) := by
  refine ⟨max_le ha.1 hb.1, ?_, ?_⟩
  · simp [h.code_mul, ha.2.1, hb.2.1, termTokens]
  · intro x; simp [h.eval_mul, ha.2.2 x, hb.2.2 x, ETR.Term.eval]

include ti h in
private theorem term_to_raw {n} (t : T n) :
    ∃ a, TermRep (eval := eval) (termCode := termCode) t a := by
  apply ti (P := fun t => ∃ a, TermRep (eval := eval) (termCode := termCode) t a)
  · intro z; exact ⟨.const z, termRep_const h n z⟩
  · intro i; exact ⟨.var i.val, termRep_var h n i⟩
  · rintro a b ⟨ra, ha⟩ ⟨rb, hb⟩; exact ⟨.add ra rb, termRep_add h ha hb⟩
  · rintro a b ⟨ra, ha⟩ ⟨rb, hb⟩; exact ⟨.mul ra rb, termRep_mul h ha hb⟩

include h in
private theorem term_from_raw {n} (a : ETR.Term) (ha : a.arity ≤ n) :
    ∃ t : T n, TermRep (eval := eval) (termCode := termCode) t a := by
  induction a with
  | const z => exact ⟨const z, termRep_const h n z⟩
  | var i => exact ⟨var ⟨i, ha⟩, termRep_var h n ⟨i, ha⟩⟩
  | add a b ia ib =>
    obtain ⟨ta, hta⟩ := ia (le_trans (Nat.le_max_left ..) ha)
    obtain ⟨tb, htb⟩ := ib (le_trans (Nat.le_max_right ..) ha)
    exact ⟨add ta tb, termRep_add h hta htb⟩
  | mul a b ia ib =>
    obtain ⟨ta, hta⟩ := ia (le_trans (Nat.le_max_left ..) ha)
    obtain ⟨tb, htb⟩ := ib (le_trans (Nat.le_max_right ..) ha)
    exact ⟨mul ta tb, termRep_mul h hta htb⟩

include ti fi h in
private theorem formula_to_raw {n} (p : F n) :
    ∃ a, FormulaRep (solutions := solutions) (formulaCode := formulaCode) p a := by
  apply fi (P := fun p => ∃ a, FormulaRep (solutions := solutions) (formulaCode := formulaCode) p a)
  · refine ⟨.falsum, Nat.zero_le _, ?_, ?_⟩
    · simp [h.code_falsum, formulaTokens]
    · intro x; exact h.holds_falsum n x
  · intro t; obtain ⟨a, ha⟩ := term_to_raw ti h t
    refine ⟨.eqZero a, ha.1, ?_, ?_⟩
    · simp [h.code_eqZero, ha.2.1, formulaTokens]
    · intro x; simp [h.holds_eqZero, ha.2.2 x, ETR.Formula.Holds]
  · intro t; obtain ⟨a, ha⟩ := term_to_raw ti h t
    refine ⟨.ltZero a, ha.1, ?_, ?_⟩
    · simp [h.code_ltZero, ha.2.1, formulaTokens]
    · intro x; simp [h.holds_ltZero, ha.2.2 x, ETR.Formula.Holds]
  · rintro p ⟨a, ha⟩
    refine ⟨.not a, ha.1, ?_, ?_⟩
    · simp [h.code_not, ha.2.1, formulaTokens]
    · intro x; simp [h.holds_not, ha.2.2 x, ETR.Formula.Holds]
  · rintro p q ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨.and a b, max_le ha.1 hb.1, ?_, ?_⟩
    · simp [h.code_and, ha.2.1, hb.2.1, formulaTokens]
    · intro x; simp [h.holds_and, ha.2.2 x, hb.2.2 x, ETR.Formula.Holds]
  · rintro p q ⟨a, ha⟩ ⟨b, hb⟩
    refine ⟨.or a b, max_le ha.1 hb.1, ?_, ?_⟩
    · simp [h.code_or, ha.2.1, hb.2.1, formulaTokens]
    · intro x; simp [h.holds_or, ha.2.2 x, hb.2.2 x, ETR.Formula.Holds]

include h in
private theorem formula_from_raw {n} (a : ETR.Formula) (ha : a.arity ≤ n) :
    ∃ p : F n, FormulaRep (solutions := solutions) (formulaCode := formulaCode) p a := by
  induction a with
  | falsum =>
    refine ⟨falsum, ha, ?_, ?_⟩
    · simp [h.code_falsum, formulaTokens]
    · intro x; exact h.holds_falsum n x
  | eqZero t =>
    obtain ⟨a, ht⟩ := term_from_raw h t ha
    refine ⟨eqZero a, ha, ?_, ?_⟩
    · simp [h.code_eqZero, ht.2.1, formulaTokens]
    · intro x; simp [h.holds_eqZero, ht.2.2 x, ETR.Formula.Holds]
  | ltZero t =>
    obtain ⟨a, ht⟩ := term_from_raw h t ha
    refine ⟨ltZero a, ha, ?_, ?_⟩
    · simp [h.code_ltZero, ht.2.1, formulaTokens]
    · intro x; simp [h.holds_ltZero, ht.2.2 x, ETR.Formula.Holds]
  | not p ip =>
    obtain ⟨a, ht⟩ := ip ha
    refine ⟨neg a, ha, ?_, ?_⟩
    · simp [h.code_not, ht.2.1, formulaTokens]
    · intro x; simp [h.holds_not, ht.2.2 x, ETR.Formula.Holds]
  | and p q ip iq =>
    obtain ⟨a, ht⟩ := ip (le_trans (Nat.le_max_left ..) ha)
    obtain ⟨b, hu⟩ := iq (le_trans (Nat.le_max_right ..) ha)
    refine ⟨conj a b, ha, ?_, ?_⟩
    · simp [h.code_and, ht.2.1, hu.2.1, formulaTokens]
    · intro x; simp [h.holds_and, ht.2.2 x, hu.2.2 x, ETR.Formula.Holds]
  | or p q ip iq =>
    obtain ⟨a, ht⟩ := ip (le_trans (Nat.le_max_left ..) ha)
    obtain ⟨b, hu⟩ := iq (le_trans (Nat.le_max_right ..) ha)
    refine ⟨disj a b, ha, ?_, ?_⟩
    · simp [h.code_or, ht.2.1, hu.2.1, formulaTokens]
    · intro x; simp [h.holds_or, ht.2.2 x, hu.2.2 x, ETR.Formula.Holds]

private theorem solution_eq {n} {p : F n} {a : ETR.Formula}
    (hp : FormulaRep (solutions := solutions) (formulaCode := formulaCode) p a) :
    {x | holds x p} = (Connectivity.Description.mk n a).realization := by
  ext x
  exact hp.2.2 x

private theorem whole_code {n} {p : F n} {a : ETR.Formula}
    (hp : FormulaRep (solutions := solutions) (formulaCode := formulaCode) p a) :
    encPair encUnary encoding (n, formulaCode p) =
      AbstractEncodingBridge.spaceCode n a := by
  simp only [AbstractEncodingBridge.spaceCode, hp.2.1]

private theorem point_code {n} {p l r : F n} {a b c : ETR.Formula}
    (hp : FormulaRep (solutions := solutions) (formulaCode := formulaCode) p a)
    (hl : FormulaRep (solutions := solutions) (formulaCode := formulaCode) l b)
    (hr : FormulaRep (solutions := solutions) (formulaCode := formulaCode) r c) :
    encPair encUnary (encList encoding) (n, [formulaCode p, formulaCode l, formulaCode r]) =
      AbstractEncodingBridge.pointCode n a b c := by
  simp only [AbstractEncodingBridge.pointCode, hp.2.1, hl.2.1, hr.2.1]

private theorem singleton_iff {n} {p : F n} {a : ETR.Formula}
    (hp : FormulaRep (solutions := solutions) (formulaCode := formulaCode) p a) (x : Fin n → ℝ) :
    {y | holds y p} = {x} ↔ Connectivity.Denotes n a x := by
  simp only [Set.ext_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff,
    Connectivity.Denotes, hp.1, true_and, hp.2.2]

include ti fi h in
/-- The independent syntax describes the flat encoded ETR language. -/
theorem finite_etr_upper_bound :
    (⋃ n, (fun p => encoding (@formulaCode n p)) '' {p | ∃ x, holds x p}) ∈
      Cslib.Complexity.PSPACE Turing.MultiTapeTM.encBits := by
  have HE : (⋃ n, (fun p => encoding (@formulaCode n p)) '' {p | ∃ x, holds x p}) = AbstractEncodingBridge.etrLanguage := by
    ext bits
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_ofPred_eq, AbstractEncodingBridge.etrLanguage]
    constructor
    · rintro ⟨n, p, ⟨x, hx⟩, hb⟩
      obtain ⟨a, ha⟩ := formula_to_raw ti fi h p
      exact ⟨a, hb.symm.trans (congrArg encoding ha.2.1), ETR.Formula.extend x, (ha.2.2 x).mp hx⟩
    · rintro ⟨a, hb, hx⟩
      obtain ⟨p, hp⟩ := formula_from_raw h a (le_refl a.arity)
      obtain ⟨x, hx⟩ := (ETR.Formula.satisfiable_iff_fin a).mp hx
      exact ⟨a.arity, p, ⟨x, (hp.2.2 x).mpr hx⟩, (congrArg encoding hp.2.1).trans hb.symm⟩
  rw [HE]
  exact AbstractEncodingBridge.etr_mem_PSPACE

include ti fi h in
theorem finite_connected_upper_bound :
    (⋃ n, (fun p : F n => encPair encUnary encoding (n, formulaCode p)) ''
      {p | IsPreconnected {x | holds x p}}) ∈
        Cslib.Complexity.PSPACE Turing.MultiTapeTM.encBits := by
  have HE : (⋃ n, (fun p : F n => encPair encUnary encoding (n, formulaCode p)) ''
      {p | IsPreconnected {x | holds x p}}) = AbstractEncodingBridge.connectedLanguage := by
    ext bits
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_ofPred_eq, AbstractEncodingBridge.connectedLanguage]
    constructor
    · rintro ⟨n, p, hc, hb⟩
      obtain ⟨a, ha⟩ := formula_to_raw ti fi h p
      exact ⟨⟨n, a⟩, hb.symm.trans (whole_code ha), ha.1, (solution_eq ha) ▸ hc⟩
    · rintro ⟨⟨n, a⟩, hb, ha, hc⟩
      obtain ⟨p, hp⟩ := formula_from_raw h a ha
      exact ⟨n, p, (solution_eq hp).symm ▸ hc, (whole_code hp).trans hb.symm⟩
  rw [HE]
  exact AbstractEncodingBridge.connected_mem_PSPACE

include ti fi h in
theorem finite_point_upper_bound :
    (⋃ n, ⋃ p : F n, (fun ab : F n × F n => encPair encUnary (encList encoding) (n, [formulaCode p, formulaCode ab.1, formulaCode ab.2])) ''
      {(a, b) | ∃ x y, {v | holds v a} = {x} ∧ {v | holds v b} = {y} ∧
        ∃ γ : _root_.Path x y, ∀ t, holds (γ t) p}) ∈
          Cslib.Complexity.PSPACE Turing.MultiTapeTM.encBits := by
  have HE : (⋃ n, ⋃ p : F n, (fun ab : F n × F n => encPair encUnary (encList encoding) (n, [formulaCode p, formulaCode ab.1, formulaCode ab.2])) ''
      {(a, b) | ∃ x y, {v | holds v a} = {x} ∧ {v | holds v b} = {y} ∧
        ∃ γ : _root_.Path x y, ∀ t, holds (γ t) p}) = AbstractEncodingBridge.pointLanguage := by
    ext bits
    simp only [Set.mem_iUnion, Set.mem_image, Set.mem_ofPred_eq, AbstractEncodingBridge.pointLanguage]
    constructor
    · rintro ⟨n, p, ⟨l, r⟩, ⟨x, y, hx, hy, hxy⟩, hb⟩
      obtain ⟨a, ha⟩ := formula_to_raw ti fi h p
      obtain ⟨b, hl⟩ := formula_to_raw ti fi h l
      obtain ⟨c, hr⟩ := formula_to_raw ti fi h r
      exact ⟨⟨⟨n, a⟩, b, c⟩, hb.symm.trans (point_code ha hl hr), ha.1,
        x, y, (singleton_iff hl x).mp hx, (singleton_iff hr y).mp hy,
        (solution_eq ha) ▸ hxy⟩
    · rintro ⟨⟨⟨n, a⟩, b, c⟩, hb, ha, x, y, hx, hy, hxy⟩
      obtain ⟨p, hp⟩ := formula_from_raw h a ha
      obtain ⟨l, hl⟩ := formula_from_raw h b hx.1
      obtain ⟨r, hr⟩ := formula_from_raw h c hy.1
      exact ⟨n, p, (l, r), ⟨x, y, (singleton_iff hl x).mpr hx,
        (singleton_iff hr y).mpr hy, (by
          have H : JoinedIn {v | holds v p} x y := (solution_eq hp).symm ▸ hxy
          exact H)⟩,
        (point_code hp hl hr).trans hb.symm⟩
  rw [HE]
  exact AbstractEncodingBridge.point_mem_PSPACE

/-! The compact entry points infer the syntax from the displayed language.
Default proof arguments supply its recursors and check its defining equations. -/

theorem etr_upper_bound
    (formulaInduction : ∀ {n} {P : F n → Prop}, P falsum → (∀ t, P (eqZero t)) →
      (∀ t, P (ltZero t)) → (∀ p, P p → P (neg p)) →
      (∀ p q, P p → P q → P (conj p q)) →
      (∀ p q, P p → P q → P (disj p q)) → ∀ p, P p := by bridge_induction)
    (termInduction : ∀ {n} {P : T n → Prop}, (∀ z, P (const z)) → (∀ i, P (var i)) →
      (∀ a b, P a → P b → P (add a b)) →
      (∀ a b, P a → P b → P (mul a b)) → ∀ t, P t := by bridge_induction)
    (laws : FiniteLaws (const := const) (var := var) (add := add) (mul := mul)
      (falsum := falsum) (eqZero := eqZero) (ltZero := ltZero)
      (neg := neg) (conj := conj) (disj := disj)
      (eval := eval) (solutions := solutions) (termCode := termCode) (formulaCode := formulaCode)
      := by constructor <;> intros <;> rfl) :
    (⋃ n, (fun p => encoding (@formulaCode n p)) '' {p | ∃ x, holds x p}) ∈
      Cslib.Complexity.PSPACE encBits :=
  finite_etr_upper_bound termInduction formulaInduction laws

theorem connected_upper_bound
    (formulaInduction : ∀ {n} {P : F n → Prop}, P falsum → (∀ t, P (eqZero t)) →
      (∀ t, P (ltZero t)) → (∀ p, P p → P (neg p)) →
      (∀ p q, P p → P q → P (conj p q)) →
      (∀ p q, P p → P q → P (disj p q)) → ∀ p, P p := by bridge_induction)
    (termInduction : ∀ {n} {P : T n → Prop}, (∀ z, P (const z)) → (∀ i, P (var i)) →
      (∀ a b, P a → P b → P (add a b)) →
      (∀ a b, P a → P b → P (mul a b)) → ∀ t, P t := by bridge_induction)
    (laws : FiniteLaws (const := const) (var := var) (add := add) (mul := mul)
      (falsum := falsum) (eqZero := eqZero) (ltZero := ltZero)
      (neg := neg) (conj := conj) (disj := disj)
      (eval := eval) (solutions := solutions) (termCode := termCode) (formulaCode := formulaCode)
      := by constructor <;> intros <;> rfl) :
    (⋃ n, (fun p : F n => encPair encUnary encoding (n, formulaCode p)) ''
      {p | IsPreconnected {x | holds x p}}) ∈ Cslib.Complexity.PSPACE encBits :=
  finite_connected_upper_bound termInduction formulaInduction laws

theorem point_upper_bound
    (formulaInduction : ∀ {n} {P : F n → Prop}, P falsum → (∀ t, P (eqZero t)) →
      (∀ t, P (ltZero t)) → (∀ p, P p → P (neg p)) →
      (∀ p q, P p → P q → P (conj p q)) →
      (∀ p q, P p → P q → P (disj p q)) → ∀ p, P p := by bridge_induction)
    (termInduction : ∀ {n} {P : T n → Prop}, (∀ z, P (const z)) → (∀ i, P (var i)) →
      (∀ a b, P a → P b → P (add a b)) →
      (∀ a b, P a → P b → P (mul a b)) → ∀ t, P t := by bridge_induction)
    (laws : FiniteLaws (const := const) (var := var) (add := add) (mul := mul)
      (falsum := falsum) (eqZero := eqZero) (ltZero := ltZero)
      (neg := neg) (conj := conj) (disj := disj)
      (eval := eval) (solutions := solutions) (termCode := termCode) (formulaCode := formulaCode)
      := by constructor <;> intros <;> rfl) :
    (⋃ n, ⋃ p : F n,
      (fun ab : F n × F n => encPair encUnary (encList encoding)
        (n, [formulaCode p, formulaCode ab.1, formulaCode ab.2])) ''
      {(a, b) | ∃ x y, {v | holds v a} = {x} ∧ {v | holds v b} = {y} ∧
        ∃ γ : _root_.Path x y, ∀ t, holds (γ t) p}) ∈ Cslib.Complexity.PSPACE encBits :=
  finite_point_upper_bound termInduction formulaInduction laws

end Finite

/-- Reduction closure with the arithmetic upper bound supplied automatically. -/
theorem existsReal_upper_bound {L : Set (List Bool)}
    (hL : L ∈ Cslib.Complexity.PSPACE encBits := by exact _root_.LeanCanny.AbstractBridge.etr_upper_bound) :
    {K | Cslib.Complexity.PolyTimeReducible encBits encBits K L} ⊆
      Cslib.Complexity.PSPACE encBits :=
  reduction_closure hL

end LeanCanny.AbstractBridge

end

/-! ## Generated input encodings

`derive_syntax_encoding` inspects the supplied inductive declarations. A sole
integer or natural/finite-index field is a scalar leaf; every other field must
be another supplied syntax type. Non-leaf constructors receive consecutive
unary tags in declaration order across the supplied types. Index leaves are
shifted past these tags. Children are concatenated in field order.

The command emits `Token`, each type's `tokens` function, and `encoding` into
the calling module. The resulting definitions contain only local syntax and
background-library operations; the metaprogram is absent from their values.
Nested, indexed and mutually recursive families are rejected.
-/

public meta section
namespace LeanCanny.AbstractBridge
open Lean Meta Elab Command Deriving Parser.Term

private def encodingRootIdent (name : Name) : Ident := mkIdent (`_root_ ++ name)

private def encodingLeaf (ind : InductiveVal) (ctor : ConstructorVal) : MetaM (Option Bool) :=
  forallTelescopeReducing ctor.type fun xs _ => do
    if ctor.numFields != 1 then return none
    let ty ← inferType xs[ind.numParams]!
    if ty.isConstOf ``Int then return some true
    if ty.isConstOf ``Nat || ty.isAppOf ``Fin then return some false
    return none

private def encodingAlts (types : Array InductiveVal) (ind : InductiveVal)
    (tags : NameMap Nat) (offset : Nat) : TermElabM (Array (TSyntax ``matchAlt)) := do
  let mut alts := #[]
  for ctorName in ind.ctors do
    let ctor ← getConstInfoCtor ctorName
    let alt ← forallTelescopeReducing ctor.type fun xs _ => do
      let mut args : Array Term := #[]
      for _ in [:ctor.numParams] do args := args.push (← `(_))
      let mut fields : Array Ident := #[]
      for _ in [:ctor.numFields] do
        let a := mkIdent (← mkFreshUserName `a)
        fields := fields.push a
        args := args.push a
      let pattern ← `(@$(mkCIdent ctorName):ident $args:term*)
      let rhs : Term ← match ← encodingLeaf ind ctor with
        | some true => `([.inl $(fields[0]!)])
        | some false =>
          let ty ← inferType xs[ind.numParams]!
          let value ← if ty.isAppOf ``Fin then `($(fields[0]!).val) else `($(fields[0]!))
          `([.inr ($value + $(quote offset))])
        | none =>
          let mut children : Array Term := #[]
          for i in [:ctor.numFields] do
            let ty ← inferType xs[ind.numParams + i]!
            let some target := types.find? (ty.isAppOf ·.name)
              | throwError "Unsupported field type {ty} in {ctorName}"
            children := children.push (← `($(mkIdent (target.name.str "tokens")) $(fields[i]!)))
          let payload ← if children.isEmpty then `([])
            else children.pop.foldrM (init := children.back!) fun child tail => `($child ++ $tail)
          let some tag := tags.find? ctorName | throwError "Missing constructor tag"
          `(.inr $(quote tag) :: $payload)
      `(matchAltExpr| | $pattern => $rhs)
    alts := alts.push alt
  return alts

/-- Generate local flat syntax encoders from constructor metadata. Integer and
index leaf constructors emit scalar tokens. Other constructors receive global
consecutive tags in the supplied type/declaration order. -/
elab "derive_syntax_encoding " inputs:ident+
    "(" &"integers" ":=" &"binary" ")" "(" &"indices" ":=" &"unary" ")" : command => do
  let mut types : Array InductiveVal := #[]
  for input in inputs do
    let name ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo input
    let info ← getConstInfoInduct name
    if info.isNested || info.isReflexive || info.numIndices != 0 then
      throwErrorAt input "Syntax encoding requires a non-nested, unindexed inductive type"
    if types.any (·.name == name) then throwErrorAt input "Duplicate syntax type"
    types := types.push info
  let mut tags : NameMap Nat := {}
  let mut offset := 0
  for typeIndex in [:types.size] do
    let ind := types[typeIndex]!
    let mut integerSeen := false
    let mut indexSeen := false
    for name in ind.ctors do
      let ctor ← getConstInfoCtor name
      match ← liftTermElabM (encodingLeaf ind ctor) with
      | some true =>
        if integerSeen then throwError "Multiple integer leaf constructors in {ind.name}"
        integerSeen := true
      | some false =>
        if indexSeen then throwError "Multiple index leaf constructors in {ind.name}"
        indexSeen := true
      | none =>
        liftTermElabM <| forallTelescopeReducing ctor.type fun fields _ => do
          for i in [:ctor.numFields] do
            let ty ← inferType fields[ind.numParams + i]!
            let some targetIndex := types.findIdx? (ty.isAppOf ·.name)
              | throwError "Unsupported field type {ty} in {name}; expected a supplied syntax type or a single integer/index leaf"
            if targetIndex > typeIndex then
              throwError "Put the field type {types[targetIndex]!.name} before {ind.name}; mutually recursive syntax families are not supported"
        tags := tags.insert name offset
        offset := offset + 1
  let ns ← getCurrNamespace
  let tokenName := encodingRootIdent (ns.str "Token")
  let encodingName := encodingRootIdent (ns.str "encoding")
  let aliasCmd ← `(command| public abbrev $tokenName:ident := Int ⊕ Nat)
  elabCommand aliasCmd
  for ind in types do
    let cmd ← liftTermElabM do
      let argNames ← mkInductArgNames ind
      let binders ← mkImplicitBinders argNames
      let targetType ← mkInductiveApp ind argNames
      let x := mkIdent (← mkFreshUserName `x)
      let alts ← encodingAlts types ind tags offset
      let discrs := #[← `(matchDiscr| $x:ident)]
      let body ← `(match $[$discrs],* with $alts:matchAlt*)
      let fn := encodingRootIdent (ind.name.str "tokens")
      `(command| @[expose] public def $fn:ident $binders:implicitBinder* ($x:ident : $targetType) :
          List $tokenName := $body)
    elabCommand cmd
  elabCommand (← `(command| @[expose] public def $encodingName:ident : List $tokenName ↪ List Bool :=
    Turing.MultiTapeTM.encList
      (Turing.MultiTapeTM.encSum Turing.MultiTapeTM.encIntBin Turing.MultiTapeTM.encUnary)))
end LeanCanny.AbstractBridge
end
