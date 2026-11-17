/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public meta import Lean.Elab.Deriving.Util
public meta import Lean.Elab.Tactic.Basic
public import LeanCanny.CountingHierarchy

/-! # Transfer from the independent CH abstract

The bridge identifies syntax, truth, and every encoded bit with the established
native language. Both reductions are the identity on bitstrings, with explicit
polynomial-time certificates, including malformed inputs. It does not assume
computability merely from a correspondence of real solution sets.
-/

@[expose] public section
namespace RealCountingHierarchy.AbstractBridge

open LeanCanny LeanCanny.ETR Turing.MultiTapeTM

open Lean Lean.Meta Lean.Elab Lean.Elab.Tactic in
elab "ch_bridge_induction" : tactic => withMainContext do
  let name ← forallTelescopeReducing (← getMainTarget) fun args _ => do
    if args.isEmpty then throwError "Expected an induction principle"
    let ty ← whnf (← inferType args.back!)
    let .const name _ := ty.getAppFn | throwError "Cannot infer the syntax type"
    discard <| getConstInfoInduct name
    return name.str "rec"
  evalTactic (← `(tactic| exact @$(mkCIdent name)))

variable {T F : Type}
  {const : ℤ → T} {var : ℕ → T} {add mul : T → T → T}
  {falsum : F} {eqZero ltZero : T → F} {neg : F → F} {conj disj : F → F → F}
  {eval : (ℕ → ℝ) → T → ℝ} {holds : (ℕ → ℝ) → F → Prop}
  {node : List (List Bool) → List Bool} {unary natural : ℕ → List Bool}
  {integer : ℤ → List Bool} {termCode : T → List Bool} {formulaCode : F → List Bool}

structure Laws : Prop where
  node_eq : ∀ children, node children = false :: (children.flatten ++ [true])
  unary_eq : ∀ n, unary n = node (List.replicate n (node []))
  natural_eq : ∀ n, natural n = node (n.bits.map fun b => if b then node [node []] else node [])
  integer_nat : ∀ n, integer (.ofNat n) = node [unary 0, natural n]
  integer_neg : ∀ n, integer (.negSucc n) = node [unary 1, natural n]
  eval_const : ∀ env z, eval env (const z) = z
  eval_var : ∀ env i, eval env (var i) = env i
  eval_add : ∀ env a b, eval env (add a b) = eval env a + eval env b
  eval_mul : ∀ env a b, eval env (mul a b) = eval env a * eval env b
  holds_falsum : ∀ env, holds env falsum ↔ False
  holds_eqZero : ∀ env t, holds env (eqZero t) ↔ eval env t = 0
  holds_ltZero : ∀ env t, holds env (ltZero t) ↔ eval env t < 0
  holds_not : ∀ env p, holds env (neg p) ↔ ¬holds env p
  holds_and : ∀ env p q, holds env (conj p q) ↔ holds env p ∧ holds env q
  holds_or : ∀ env p q, holds env (disj p q) ↔ holds env p ∨ holds env q
  code_const : ∀ z, termCode (const z) = node [unary 0, integer z]
  code_var : ∀ i, termCode (var i) = node [unary 1, unary i]
  code_add : ∀ a b, termCode (add a b) = node [unary 2, termCode a, termCode b]
  code_mul : ∀ a b, termCode (mul a b) = node [unary 3, termCode a, termCode b]
  code_falsum : formulaCode falsum = node [unary 0]
  code_eqZero : ∀ t, formulaCode (eqZero t) = node [unary 1, termCode t]
  code_ltZero : ∀ t, formulaCode (ltZero t) = node [unary 2, termCode t]
  code_not : ∀ p, formulaCode (neg p) = node [unary 3, formulaCode p]
  code_and : ∀ p q, formulaCode (conj p q) = node [unary 4, formulaCode p, formulaCode q]
  code_or : ∀ p q, formulaCode (disj p q) = node [unary 5, formulaCode p, formulaCode q]

variable (h : Laws (const := const) (var := var) (add := add) (mul := mul)
  (falsum := falsum) (eqZero := eqZero) (ltZero := ltZero) (neg := neg) (conj := conj) (disj := disj)
  (eval := eval) (holds := holds) (node := node) (unary := unary) (natural := natural)
  (integer := integer) (termCode := termCode) (formulaCode := formulaCode))

include h in
private theorem node_code (ds : List Data) : node (ds.map Data.toBits) = (Data.l ds).toBits := by
  rw [h.node_eq, Data.toBits_l]

include h in
private theorem unary_code (n : ℕ) : unary n = (Codec.unary n).toBits := by
  simp only [h.unary_eq, h.node_eq, Codec.unary, Data.toBits_l, List.map_replicate]
  rfl

include h in
private theorem natural_code (n : ℕ) : natural n = (Codec.natural n).toBits := by
  rw [h.natural_eq]
  change node (n.bits.map fun b => if b then node [node []] else node []) =
    (Data.l (n.bits.map Codec.bit)).toBits
  rw [← node_code h, List.map_map]
  congr 1
  apply List.map_congr_left
  intro b _
  cases b <;> simp [h.node_eq, Codec.bit, Data.toBits_l]

include h in
private theorem integer_code (z : ℤ) : integer z = (Codec.integer z).toBits := by
  cases z with
  | ofNat n =>
    rw [h.integer_nat, unary_code h, natural_code h]
    exact node_code h [Codec.unary 0, Codec.natural n]
  | negSucc n =>
    rw [h.integer_neg, unary_code h, natural_code h]
    exact node_code h [Codec.unary 1, Codec.natural n]

private def TermRep (t : T) (a : ETR.Term) : Prop :=
  termCode t = a.toData.toBits ∧ ∀ env : ℕ → ℝ, eval env t = a.eval env
private def FormulaRep (p : F) (a : ETR.Formula) : Prop :=
  formulaCode p = a.encode ∧ ∀ env : ℕ → ℝ, holds env p ↔ a.Holds env

include h in
private theorem term_const (z : ℤ) : TermRep (eval := eval) (termCode := termCode) (const z) (.const z) := by
  refine ⟨?_, fun env => h.eval_const env z⟩
  rw [h.code_const, unary_code h, integer_code h]
  exact node_code h [Codec.unary 0, Codec.integer z]

include h in
private theorem term_var (i : ℕ) : TermRep (eval := eval) (termCode := termCode) (var i) (.var i) := by
  refine ⟨?_, fun env => h.eval_var env i⟩
  rw [h.code_var, unary_code h, unary_code h]
  exact node_code h [Codec.unary 1, Codec.unary i]

include h in
private theorem term_add {t u : T} {a b : ETR.Term}
    (ht : TermRep (eval := eval) (termCode := termCode) t a)
    (hu : TermRep (eval := eval) (termCode := termCode) u b) :
    TermRep (eval := eval) (termCode := termCode) (add t u) (.add a b) := by
  refine ⟨?_, fun env => by rw [h.eval_add, ht.2, hu.2]; rfl⟩
  rw [h.code_add, unary_code h, ht.1, hu.1]
  exact node_code h [Codec.unary 2, a.toData, b.toData]

include h in
private theorem term_mul {t u : T} {a b : ETR.Term}
    (ht : TermRep (eval := eval) (termCode := termCode) t a)
    (hu : TermRep (eval := eval) (termCode := termCode) u b) :
    TermRep (eval := eval) (termCode := termCode) (mul t u) (.mul a b) := by
  refine ⟨?_, fun env => by rw [h.eval_mul, ht.2, hu.2]; rfl⟩
  rw [h.code_mul, unary_code h, ht.1, hu.1]
  exact node_code h [Codec.unary 3, a.toData, b.toData]

variable
  (ti : ∀ {P : T → Prop}, (∀ z, P (const z)) → (∀ i, P (var i)) →
    (∀ a b, P a → P b → P (add a b)) → (∀ a b, P a → P b → P (mul a b)) → ∀ t, P t)
  (fi : ∀ {P : F → Prop}, P falsum → (∀ t, P (eqZero t)) → (∀ t, P (ltZero t)) →
    (∀ p, P p → P (neg p)) → (∀ p q, P p → P q → P (conj p q)) →
    (∀ p q, P p → P q → P (disj p q)) → ∀ p, P p)

include h ti in
private theorem term_to_raw (t : T) : ∃ a, TermRep (eval := eval) (termCode := termCode) t a := by
  apply ti (P := fun t => ∃ a, TermRep (eval := eval) (termCode := termCode) t a)
  · intro z; exact ⟨.const z, term_const h z⟩
  · intro i; exact ⟨.var i, term_var h i⟩
  · rintro t u ⟨a, ha⟩ ⟨b, hb⟩; exact ⟨.add a b, term_add h ha hb⟩
  · rintro t u ⟨a, ha⟩ ⟨b, hb⟩; exact ⟨.mul a b, term_mul h ha hb⟩

include h in
private theorem term_from_raw (a : ETR.Term) : ∃ t, TermRep (eval := eval) (termCode := termCode) t a := by
  induction a with
  | const z => exact ⟨const z, term_const h z⟩
  | var i => exact ⟨var i, term_var h i⟩
  | add a b ia ib =>
    obtain ⟨t, ht⟩ := ia
    obtain ⟨u, hu⟩ := ib
    exact ⟨add t u, term_add h ht hu⟩
  | mul a b ia ib =>
    obtain ⟨t, ht⟩ := ia
    obtain ⟨u, hu⟩ := ib
    exact ⟨mul t u, term_mul h ht hu⟩

include h in
private theorem formula_falsum : FormulaRep (holds := holds) (formulaCode := formulaCode) falsum .falsum := by
  refine ⟨?_, fun env => h.holds_falsum env⟩
  rw [h.code_falsum, unary_code h]
  exact node_code h [Codec.unary 0]

include h in
private theorem formula_eqZero {t : T} {a : ETR.Term}
    (ht : TermRep (eval := eval) (termCode := termCode) t a) :
    FormulaRep (holds := holds) (formulaCode := formulaCode) (eqZero t) (.eqZero a) := by
  refine ⟨?_, fun env => by rw [h.holds_eqZero, ht.2]; rfl⟩
  rw [h.code_eqZero, unary_code h, ht.1]
  exact node_code h [Codec.unary 1, a.toData]

include h in
private theorem formula_ltZero {t : T} {a : ETR.Term}
    (ht : TermRep (eval := eval) (termCode := termCode) t a) :
    FormulaRep (holds := holds) (formulaCode := formulaCode) (ltZero t) (.ltZero a) := by
  refine ⟨?_, fun env => by rw [h.holds_ltZero, ht.2]; rfl⟩
  rw [h.code_ltZero, unary_code h, ht.1]
  exact node_code h [Codec.unary 2, a.toData]

include h in
private theorem formula_not {p : F} {a : ETR.Formula}
    (hp : FormulaRep (holds := holds) (formulaCode := formulaCode) p a) :
    FormulaRep (holds := holds) (formulaCode := formulaCode) (neg p) (.not a) := by
  refine ⟨?_, fun env => by rw [h.holds_not, hp.2]; rfl⟩
  rw [h.code_not, unary_code h, hp.1]
  exact node_code h [Codec.unary 3, a.toData]

include h in
private theorem formula_and {p q : F} {a b : ETR.Formula}
    (hp : FormulaRep (holds := holds) (formulaCode := formulaCode) p a)
    (hq : FormulaRep (holds := holds) (formulaCode := formulaCode) q b) :
    FormulaRep (holds := holds) (formulaCode := formulaCode) (conj p q) (.and a b) := by
  refine ⟨?_, fun env => by rw [h.holds_and, hp.2, hq.2]; rfl⟩
  rw [h.code_and, unary_code h, hp.1, hq.1]
  exact node_code h [Codec.unary 4, a.toData, b.toData]

include h in
private theorem formula_or {p q : F} {a b : ETR.Formula}
    (hp : FormulaRep (holds := holds) (formulaCode := formulaCode) p a)
    (hq : FormulaRep (holds := holds) (formulaCode := formulaCode) q b) :
    FormulaRep (holds := holds) (formulaCode := formulaCode) (disj p q) (.or a b) := by
  refine ⟨?_, fun env => by rw [h.holds_or, hp.2, hq.2]; rfl⟩
  rw [h.code_or, unary_code h, hp.1, hq.1]
  exact node_code h [Codec.unary 5, a.toData, b.toData]

include h ti fi in
private theorem formula_to_raw (p : F) : ∃ a, FormulaRep (holds := holds) (formulaCode := formulaCode) p a := by
  apply fi (P := fun p => ∃ a, FormulaRep (holds := holds) (formulaCode := formulaCode) p a)
  · exact ⟨.falsum, formula_falsum h⟩
  · intro t; obtain ⟨a, ha⟩ := term_to_raw h ti t; exact ⟨.eqZero a, formula_eqZero h ha⟩
  · intro t; obtain ⟨a, ha⟩ := term_to_raw h ti t; exact ⟨.ltZero a, formula_ltZero h ha⟩
  · rintro p ⟨a, ha⟩; exact ⟨.not a, formula_not h ha⟩
  · rintro p q ⟨a, ha⟩ ⟨b, hb⟩; exact ⟨.and a b, formula_and h ha hb⟩
  · rintro p q ⟨a, ha⟩ ⟨b, hb⟩; exact ⟨.or a b, formula_or h ha hb⟩

include h in
private theorem formula_from_raw (a : ETR.Formula) :
    ∃ p, FormulaRep (holds := holds) (formulaCode := formulaCode) p a := by
  induction a with
  | falsum => exact ⟨falsum, formula_falsum h⟩
  | eqZero t => obtain ⟨a, ha⟩ := term_from_raw h t; exact ⟨eqZero a, formula_eqZero h ha⟩
  | ltZero t => obtain ⟨a, ha⟩ := term_from_raw h t; exact ⟨ltZero a, formula_ltZero h ha⟩
  | not p hp => obtain ⟨a, ha⟩ := hp; exact ⟨neg a, formula_not h ha⟩
  | and p q hp hq =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    exact ⟨conj a b, formula_and h ha hb⟩
  | or p q hp hq =>
    obtain ⟨a, ha⟩ := hp
    obtain ⟨b, hb⟩ := hq
    exact ⟨disj a b, formula_or h ha hb⟩

include h ti fi in
/-- The translations on encoded inputs are literally the identity. Their native
polynomial-time certificates cover all words, including malformed encodings. -/
theorem etr_reduction : PolyTimeReduces
    {w | ∃ p : F, w = formulaCode p ∧ ∃ env : ℕ → ℝ, holds env p} ETR.language := by
  refine ⟨id, ComputableInPolyTime.id', ?_⟩
  intro w
  rw [ETR.mem_language_iff]
  constructor
  · rintro ⟨p, hc, env, hp⟩
    obtain ⟨a, ha⟩ := formula_to_raw h ti fi p
    exact ⟨a, hc.trans ha.1, env, (ha.2 env).mp hp⟩
  · rintro ⟨a, hc, env, ha⟩
    obtain ⟨p, hp⟩ := formula_from_raw h a
    exact ⟨p, hc.trans hp.1.symm, env, (hp.2 env).mpr ha⟩

include h ti fi in
theorem existsForall_reduction : PolyTimeReduces
    {w | ∃ r : ℕ, ∃ p : F,
      w = encPair encUnary encBits (r, formulaCode p) ∧
        ∃ x : Fin r → ℝ, ∀ env : ℕ → ℝ, (∀ i : Fin r, env i.val = x i) → holds env p}
    CountingHierarchy.ExistsForall.language := by
  refine ⟨id, ComputableInPolyTime.id', ?_⟩
  intro w
  constructor
  · rintro ⟨r, p, hc, x, hp⟩
    obtain ⟨a, ha⟩ := formula_to_raw h ti fi p
    refine ⟨r, a, hc.trans (congrArg (fun bits => encPair encUnary encBits (r, bits)) ha.1), x, ?_⟩
    intro env he
    exact (ha.2 env).mp (hp env he)
  · rintro ⟨r, a, hc, x, ha⟩
    obtain ⟨p, hp⟩ := formula_from_raw h a
    refine ⟨r, p, hc.trans (congrArg (fun bits => encPair encUnary encBits (r, bits)) hp.1.symm), x, ?_⟩
    intro env he
    exact (hp.2 env).mpr (ha env he)

/-- Checked transfer for the public existential language. The short abstract proof
supplies only its syntax recursors and its defining equations. -/
theorem etr_upper_bound
    (termInduction : ∀ {P : T → Prop}, (∀ z, P (const z)) → (∀ i, P (var i)) →
      (∀ a b, P a → P b → P (add a b)) → (∀ a b, P a → P b → P (mul a b)) → ∀ t, P t := by ch_bridge_induction)
    (formulaInduction : ∀ {P : F → Prop}, P falsum → (∀ t, P (eqZero t)) → (∀ t, P (ltZero t)) →
      (∀ p, P p → P (neg p)) → (∀ p q, P p → P q → P (conj p q)) →
      (∀ p q, P p → P q → P (disj p q)) → ∀ p, P p := by ch_bridge_induction)
    (laws : Laws (const := const) (var := var) (add := add) (mul := mul)
      (falsum := falsum) (eqZero := eqZero) (ltZero := ltZero) (neg := neg) (conj := conj) (disj := disj)
      (eval := eval) (holds := holds) (node := node) (unary := unary) (natural := natural)
      (integer := integer) (termCode := termCode) (formulaCode := formulaCode)
      := by constructor <;> intros <;> rfl) :
    {w | ∃ p : F, w = formulaCode p ∧ ∃ env : ℕ → ℝ, holds env p} ∈
      Cslib.Complexity.CountingLevel 26 encBits :=
  (etr_reduction laws termInduction formulaInduction).mem_CountingLevel CountingHierarchy.etr_mem_CountingLevel

/-- Checked transfer for the public two-block language. -/
theorem existsForall_upper_bound
    (termInduction : ∀ {P : T → Prop}, (∀ z, P (const z)) → (∀ i, P (var i)) →
      (∀ a b, P a → P b → P (add a b)) → (∀ a b, P a → P b → P (mul a b)) → ∀ t, P t := by ch_bridge_induction)
    (formulaInduction : ∀ {P : F → Prop}, P falsum → (∀ t, P (eqZero t)) → (∀ t, P (ltZero t)) →
      (∀ p, P p → P (neg p)) → (∀ p q, P p → P q → P (conj p q)) →
      (∀ p q, P p → P q → P (disj p q)) → ∀ p, P p := by ch_bridge_induction)
    (laws : Laws (const := const) (var := var) (add := add) (mul := mul)
      (falsum := falsum) (eqZero := eqZero) (ltZero := ltZero) (neg := neg) (conj := conj) (disj := disj)
      (eval := eval) (holds := holds) (node := node) (unary := unary) (natural := natural)
      (integer := integer) (termCode := termCode) (formulaCode := formulaCode)
      := by constructor <;> intros <;> rfl) :
    {w | ∃ r : ℕ, ∃ p : F,
      w = encPair encUnary encBits (r, formulaCode p) ∧
        ∃ x : Fin r → ℝ, ∀ env : ℕ → ℝ, (∀ i : Fin r, env i.val = x i) → holds env p} ∈
      Cslib.Complexity.CountingLevel 60 encBits :=
  (existsForall_reduction laws termInduction formulaInduction).mem_CountingLevel
    CountingHierarchy.ExistsForall.mem_CountingLevel

end RealCountingHierarchy.AbstractBridge
