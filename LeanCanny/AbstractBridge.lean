/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.CoercivePSPACE

/-! # Transfer to an independent presentation of real arithmetic

The abstract supplies its syntax, semantics, and literal serialization. Structural
induction identifies its binary language with the established ETR language.
Thus the decision algorithm receives identical input bits; transferring the
space bound requires no additional serialization or parsing computation.
-/

@[expose] public section
namespace LeanCanny.AbstractBridge

def node (children : List (List Bool)) : List Bool :=
  false :: (children.flatten ++ [true])

def unary (n : ℕ) : List Bool := node (List.replicate n (node []))

def bit (b : Bool) : List Bool := if b then node [node []] else node []

def integer : ℤ → List Bool
  | .ofNat n => node [unary 0, node (n.bits.map bit)]
  | .negSucc n => node [unary 1, node (n.bits.map bit)]

structure Presentation where
  Term : Type
  Formula : Type
  const : ℤ → Term
  var : ℕ → Term
  add : Term → Term → Term
  mul : Term → Term → Term
  falsum : Formula
  eqZero : Term → Formula
  ltZero : Term → Formula
  not : Formula → Formula
  and : Formula → Formula → Formula
  or : Formula → Formula → Formula
  term_induction {P : Term → Prop} :
    (∀ z, P (const z)) → (∀ i, P (var i)) →
    (∀ a b, P a → P b → P (add a b)) →
    (∀ a b, P a → P b → P (mul a b)) → ∀ t, P t
  formula_induction {P : Formula → Prop} :
    P falsum → (∀ t, P (eqZero t)) → (∀ t, P (ltZero t)) →
    (∀ p, P p → P (not p)) →
    (∀ p q, P p → P q → P (and p q)) →
    (∀ p q, P p → P q → P (or p q)) → ∀ p, P p
  eval : (ℕ → ℝ) → Term → ℝ
  holds : (ℕ → ℝ) → Formula → Prop
  termCode : Term → List Bool
  formulaCode : Formula → List Bool

structure Laws (S : Presentation) : Prop where
  eval_const : ∀ x z, S.eval x (S.const z) = z
  eval_var : ∀ x i, S.eval x (S.var i) = x i
  eval_add : ∀ x a b, S.eval x (S.add a b) = S.eval x a + S.eval x b
  eval_mul : ∀ x a b, S.eval x (S.mul a b) = S.eval x a * S.eval x b
  holds_falsum : ∀ x, S.holds x S.falsum ↔ False
  holds_eqZero : ∀ x t, S.holds x (S.eqZero t) ↔ S.eval x t = 0
  holds_ltZero : ∀ x t, S.holds x (S.ltZero t) ↔ S.eval x t < 0
  holds_not : ∀ x p, S.holds x (S.not p) ↔ ¬ S.holds x p
  holds_and : ∀ x p q, S.holds x (S.and p q) ↔ S.holds x p ∧ S.holds x q
  holds_or : ∀ x p q, S.holds x (S.or p q) ↔ S.holds x p ∨ S.holds x q
  code_const : ∀ z, S.termCode (S.const z) = node [unary 0, integer z]
  code_var : ∀ i, S.termCode (S.var i) = node [unary 1, unary i]
  code_add : ∀ a b, S.termCode (S.add a b) = node [unary 2, S.termCode a, S.termCode b]
  code_mul : ∀ a b, S.termCode (S.mul a b) = node [unary 3, S.termCode a, S.termCode b]
  code_falsum : S.formulaCode S.falsum = node [unary 0]
  code_eqZero : ∀ t, S.formulaCode (S.eqZero t) = node [unary 1, S.termCode t]
  code_ltZero : ∀ t, S.formulaCode (S.ltZero t) = node [unary 2, S.termCode t]
  code_not : ∀ p, S.formulaCode (S.not p) = node [unary 3, S.formulaCode p]
  code_and : ∀ p q,
    S.formulaCode (S.and p q) = node [unary 4, S.formulaCode p, S.formulaCode q]
  code_or : ∀ p q,
    S.formulaCode (S.or p q) = node [unary 5, S.formulaCode p, S.formulaCode q]

def translateTerm (S : Presentation) : ETR.Term → S.Term
  | .const z => S.const z
  | .var i => S.var i
  | .add a b => S.add (translateTerm S a) (translateTerm S b)
  | .mul a b => S.mul (translateTerm S a) (translateTerm S b)

def translateFormula (S : Presentation) : ETR.Formula → S.Formula
  | .falsum => S.falsum
  | .eqZero t => S.eqZero (translateTerm S t)
  | .ltZero t => S.ltZero (translateTerm S t)
  | .not p => S.not (translateFormula S p)
  | .and p q => S.and (translateFormula S p) (translateFormula S q)
  | .or p q => S.or (translateFormula S p) (translateFormula S q)

theorem translateTerm_surjective (S : Presentation) : Function.Surjective (translateTerm S) := by
  intro t
  refine S.term_induction (P := fun t => ∃ a, translateTerm S a = t) ?_ ?_ ?_ ?_ t
  · intro z; exact ⟨.const z, rfl⟩
  · intro i; exact ⟨.var i, rfl⟩
  · rintro a b ⟨a', rfl⟩ ⟨b', rfl⟩; exact ⟨.add a' b', rfl⟩
  · rintro a b ⟨a', rfl⟩ ⟨b', rfl⟩; exact ⟨.mul a' b', rfl⟩

theorem translateFormula_surjective (S : Presentation) :
    Function.Surjective (translateFormula S) := by
  intro p
  refine S.formula_induction (P := fun p => ∃ a, translateFormula S a = p)
    ?_ ?_ ?_ ?_ ?_ ?_ p
  · exact ⟨.falsum, rfl⟩
  · intro t; obtain ⟨t, rfl⟩ := translateTerm_surjective S t; exact ⟨.eqZero t, rfl⟩
  · intro t; obtain ⟨t, rfl⟩ := translateTerm_surjective S t; exact ⟨.ltZero t, rfl⟩
  · rintro p ⟨p', rfl⟩; exact ⟨.not p', rfl⟩
  · rintro p q ⟨p', rfl⟩ ⟨q', rfl⟩; exact ⟨.and p' q', rfl⟩
  · rintro p q ⟨p', rfl⟩ ⟨q', rfl⟩; exact ⟨.or p' q', rfl⟩

theorem eval_translate (S : Presentation) (h : Laws S) (x : ℕ → ℝ) (t : ETR.Term) :
    S.eval x (translateTerm S t) = t.eval x := by
  induction t <;> simp_all [translateTerm, ETR.Term.eval,
    h.eval_const, h.eval_var, h.eval_add, h.eval_mul]

theorem holds_translate (S : Presentation) (h : Laws S) (x : ℕ → ℝ) (p : ETR.Formula) :
    S.holds x (translateFormula S p) ↔ p.Holds x := by
  induction p <;> simp_all [translateFormula, ETR.Formula.Holds,
    h.holds_falsum, h.holds_eqZero, h.holds_ltZero, h.holds_not,
    h.holds_and, h.holds_or, eval_translate S h]

private theorem unary_eq (n : ℕ) : (ETR.Codec.unary n).toBits = unary n := by
  simp [ETR.Codec.unary, unary, node, Data.toBits_l]

private theorem bit_eq (b : Bool) : (ETR.Codec.bit b).toBits = bit b := by
  cases b <;> simp [ETR.Codec.bit, bit, node, Data.toBits_l]

private theorem integer_eq (z : ℤ) : (ETR.Codec.integer z).toBits = integer z := by
  cases z <;> simp [ETR.Codec.integer, ETR.Codec.natural, integer, node,
    Data.toBits_l, unary_eq, List.map_map, Function.comp_def, bit_eq]

theorem termCode_translate (S : Presentation) (h : Laws S) (t : ETR.Term) :
    S.termCode (translateTerm S t) = t.toData.toBits := by
  induction t <;> simp_all [translateTerm, h.code_const, h.code_var, h.code_add,
    h.code_mul, ETR.Term.toData, Data.toBits_l, unary_eq, integer_eq, node]

theorem formulaCode_translate (S : Presentation) (h : Laws S) (p : ETR.Formula) :
    S.formulaCode (translateFormula S p) = p.encode := by
  induction p <;> simp_all [translateFormula, h.code_falsum, h.code_eqZero,
    h.code_ltZero, h.code_not, h.code_and, h.code_or, ETR.Formula.encode,
    ETR.Formula.toData, Data.toBits_l, unary_eq, termCode_translate S h, node]

theorem language_eq (S : Presentation) (h : Laws S) :
    {bits | ∃ p, bits = S.formulaCode p ∧ ∃ x, S.holds x p} = ETR.language := by
  ext bits
  rw [ETR.mem_language_iff]
  constructor
  · rintro ⟨p, hp, x, hx⟩
    obtain ⟨p, rfl⟩ := translateFormula_surjective S p
    exact ⟨p, hp.trans (formulaCode_translate S h p), x, (holds_translate S h x p).mp hx⟩
  · rintro ⟨p, hp, x, hx⟩
    exact ⟨translateFormula S p, hp.trans (formulaCode_translate S h p).symm,
      x, (holds_translate S h x p).mpr hx⟩

theorem upper_bound (S : Presentation) (h : Laws S) :
    {bits | ∃ p, bits = S.formulaCode p ∧ ∃ x, S.holds x p} ∈
      Cslib.Complexity.PSPACE Turing.MultiTapeTM.encBits := by
  rw [language_eq S h]
  exact ETR.etr_mem_PSPACE

theorem reduction_closure {L : Set (List Bool)}
    (h : L ∈ Cslib.Complexity.PSPACE Turing.MultiTapeTM.encBits) :
    {K | Cslib.Complexity.PolyTimeReducible Turing.MultiTapeTM.encBits
      Turing.MultiTapeTM.encBits K L} ⊆
        Cslib.Complexity.PSPACE Turing.MultiTapeTM.encBits := by
  intro K hK
  exact Computation.mem_PSPACE_of_reduction hK h

end LeanCanny.AbstractBridge
