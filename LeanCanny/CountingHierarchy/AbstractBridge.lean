/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.AbstractBridge
public import LeanCanny.CountingHierarchy.DerivedSentenceEncoding

/-! # Counting-hierarchy proofs for the shared formal abstract

The PSPACE and CH results share the same finite syntax, solution sets, and flat
input convention. This bridge retains their common representation proof and
uses the uniform derived-to-native compiler to preserve the stated counting levels.
-/

@[expose] public section
namespace LeanCanny.CountingHierarchy.AbstractBridge

open Turing.MultiTapeTM LeanCanny.Encoding.DerivedSyntax LeanCanny.ETR

private theorem native_twoBlock_iff_fin (r s : ℕ) (a : ETR.Formula) (ha : a.arity ≤ r + s) :
    (∃ x : Fin r → ℝ, ∀ y : Fin s → ℝ, a.Holds (ETR.Formula.extend (Fin.addCases x y))) ↔
      ExistsForall.SentenceHolds r a := by
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    intro env he
    let y : Fin s → ℝ := fun j => env (r + j.val)
    have hp : ∀ i : Fin (r + s), Fin.addCases x y i = env i.val := by
      intro i
      refine Fin.addCases (fun j => ?_) (fun j => ?_) i
      · rw [Fin.addCases_left]
        exact (he j).symm
      · rw [Fin.addCases_right]
        rfl
    apply (a.holds_congr (ETR.Formula.extend (Fin.addCases x y)) env ?_).mp (hx y)
    intro i hi
    have hib : i < r + s := hi.trans_le ha
    rw [ETR.Formula.extend, dite_eq_left hib]
    exact hp ⟨i, hib⟩
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    intro y
    apply hx (ETR.Formula.extend (Fin.addCases x y))
    intro i
    have hi : i.val < r + s := i.isLt.trans_le (Nat.le_add_right _ _)
    rw [ETR.Formula.extend, dite_eq_left hi]
    change Fin.addCases x y (Fin.castAdd s i) = x i
    rw [Fin.addCases_left]

variable {T F : ℕ → Type}
  {const : ∀ {n}, ℤ → T n} {var : ∀ {n}, Fin n → T n}
  {add mul : ∀ {n}, T n → T n → T n}
  {falsum : ∀ {n}, F n} {eqZero ltZero : ∀ {n}, T n → F n}
  {neg : ∀ {n}, F n → F n} {conj disj : ∀ {n}, F n → F n → F n}
  {eval : ∀ {n}, (Fin n → ℝ) → T n → ℝ}
  {solutions : ∀ {n}, F n → Set (Fin n → ℝ)}
  {termCode : ∀ {n}, T n → List Bool} {formulaCode : ∀ {n}, F n → List Bool}

local notation "holds" => (fun {n : ℕ} (x : Fin n → ℝ) (p : F n) => x ∈ solutions p)

variable
  (ti : ∀ {n} {P : T n → Prop}, (∀ z, P (const z)) → (∀ i, P (var i)) →
    (∀ a b, P a → P b → P (add a b)) → (∀ a b, P a → P b → P (mul a b)) → ∀ t, P t)
  (fi : ∀ {n} {P : F n → Prop}, P falsum → (∀ t, P (eqZero t)) → (∀ t, P (ltZero t)) →
    (∀ p, P p → P (neg p)) → (∀ p q, P p → P q → P (conj p q)) →
    (∀ p q, P p → P q → P (disj p q)) → ∀ p, P p)
  (h : LeanCanny.AbstractBridge.FiniteLaws (const := const) (var := var) (add := add) (mul := mul)
    (falsum := falsum) (eqZero := eqZero) (ltZero := ltZero) (neg := neg) (conj := conj) (disj := disj)
    (eval := eval) (solutions := solutions) (termCode := termCode) (formulaCode := formulaCode))

include ti fi h in
private theorem etr_language_eq :
    (⋃ n, (fun p => encBits (@formulaCode n p)) '' {p | ∃ x, holds x p}) =
      DerivedSentenceEncoding.etrLanguage := by
  ext w
  simp only [Set.mem_iUnion, Set.mem_image, Set.mem_ofPred_eq, DerivedSentenceEncoding.etrLanguage]
  constructor
  · rintro ⟨n, p, ⟨x, hx⟩, hw⟩
    obtain ⟨a, _, hc, he⟩ := LeanCanny.AbstractBridge.finite_formula_to_raw ti fi h p
    exact ⟨a, hw.symm.trans (congrArg encBits hc), ETR.Formula.extend x, (he x).mp hx⟩
  · rintro ⟨a, hw, ha⟩
    obtain ⟨p, hc, he⟩ := LeanCanny.AbstractBridge.finite_formula_from_raw h a le_rfl
    obtain ⟨x, hx⟩ := (a.satisfiable_iff_fin).mp ha
    exact ⟨a.arity, p, ⟨x, (he x).mpr hx⟩, (congrArg encBits hc).trans hw.symm⟩

include ti fi h in
private theorem twoBlock_language_eq :
    (⋃ r, ⋃ s, (fun p : F (r + s) => encPair encUnary encBits (r, formulaCode p)) ''
      {p | ∃ x : Fin r → ℝ, ∀ y : Fin s → ℝ, holds (Fin.addCases x y) p}) =
        DerivedSentenceEncoding.twoBlockLanguage := by
  ext w
  simp only [Set.mem_iUnion, Set.mem_image, Set.mem_ofPred_eq, DerivedSentenceEncoding.twoBlockLanguage]
  constructor
  · rintro ⟨r, s, p, ⟨x, hx⟩, hw⟩
    obtain ⟨a, ha, hc, he⟩ := LeanCanny.AbstractBridge.finite_formula_to_raw ti fi h p
    refine ⟨r, a, hw.symm.trans (congrArg (fun ts => encPair encUnary encBits (r, ts)) hc), ?_⟩
    apply (native_twoBlock_iff_fin r s a ha).mp
    exact ⟨x, fun y => (he _).mp (hx y)⟩
  · rintro ⟨r, a, hw, hs⟩
    let s := a.arity
    have ha : a.arity ≤ r + s := Nat.le_add_left _ _
    obtain ⟨p, hc, he⟩ := LeanCanny.AbstractBridge.finite_formula_from_raw h a ha
    obtain ⟨x, hx⟩ := (native_twoBlock_iff_fin r s a ha).mpr hs
    refine ⟨r, s, p, ⟨x, fun y => (he _).mpr (hx y)⟩, ?_⟩
    exact (congrArg (fun ts => encPair encUnary encBits (r, ts)) hc).trans hw.symm

/-- The derived encoding is compiled uniformly, retaining the existential bound.
Inferring formula induction first determines the arithmetic term type, so both
syntax recursors can be supplied by the bridge's default arguments. -/
theorem etr_upper_bound
    (formulaInduction : ∀ {n} {P : F n → Prop}, P falsum → (∀ t, P (eqZero t)) → (∀ t, P (ltZero t)) →
      (∀ p, P p → P (neg p)) → (∀ p q, P p → P q → P (conj p q)) →
      (∀ p q, P p → P q → P (disj p q)) → ∀ p, P p := by bridge_induction)
    (termInduction : ∀ {n} {P : T n → Prop}, (∀ z, P (const z)) → (∀ i, P (var i)) →
      (∀ a b, P a → P b → P (add a b)) → (∀ a b, P a → P b → P (mul a b)) → ∀ t, P t := by bridge_induction)
    (laws : LeanCanny.AbstractBridge.FiniteLaws (const := const) (var := var) (add := add) (mul := mul)
      (falsum := falsum) (eqZero := eqZero) (ltZero := ltZero) (neg := neg) (conj := conj) (disj := disj)
      (eval := eval) (solutions := solutions) (termCode := termCode) (formulaCode := formulaCode)
      := by constructor <;> intros <;> (first | rfl | (solve | simp |
        simp [LeanCanny.Encoding.DerivedSyntax.finite_variable_encoding]))) :
    (⋃ n, (fun p => encBits (@formulaCode n p)) '' {p | ∃ x, holds x p}) ∈
      Cslib.Complexity.CountingLevel 26 encBits := by
  rw [etr_language_eq termInduction formulaInduction laws]
  exact DerivedSentenceEncoding.etr_mem

/-- The two finite quantifier blocks use the same syntax and input convention. -/
theorem twoBlock_upper_bound
    (formulaInduction : ∀ {n} {P : F n → Prop}, P falsum → (∀ t, P (eqZero t)) → (∀ t, P (ltZero t)) →
      (∀ p, P p → P (neg p)) → (∀ p q, P p → P q → P (conj p q)) →
      (∀ p q, P p → P q → P (disj p q)) → ∀ p, P p := by bridge_induction)
    (termInduction : ∀ {n} {P : T n → Prop}, (∀ z, P (const z)) → (∀ i, P (var i)) →
      (∀ a b, P a → P b → P (add a b)) → (∀ a b, P a → P b → P (mul a b)) → ∀ t, P t := by bridge_induction)
    (laws : LeanCanny.AbstractBridge.FiniteLaws (const := const) (var := var) (add := add) (mul := mul)
      (falsum := falsum) (eqZero := eqZero) (ltZero := ltZero) (neg := neg) (conj := conj) (disj := disj)
      (eval := eval) (solutions := solutions) (termCode := termCode) (formulaCode := formulaCode)
      := by constructor <;> intros <;> (first | rfl | (solve | simp |
        simp [LeanCanny.Encoding.DerivedSyntax.finite_variable_encoding]))) :
    (⋃ r, ⋃ s, (fun p : F (r + s) => encPair encUnary encBits (r, formulaCode p)) ''
      {p | ∃ x : Fin r → ℝ, ∀ y : Fin s → ℝ, holds (Fin.addCases x y) p}) ∈
        Cslib.Complexity.CountingLevel 60 encBits := by
  rw [twoBlock_language_eq termInduction formulaInduction laws]
  exact DerivedSentenceEncoding.twoBlock_mem

/-- Polynomial-time reductions transfer the existential bound to all of ∃ℝ. -/
theorem existsReal_upper_bound {L : Set (List Bool)}
    (hL : L ∈ Cslib.Complexity.CountingLevel 26 encBits := by
      bridge_existing_bound etr_in_CountingLevel) :
    {K | Cslib.Complexity.PolyTimeReducible encBits encBits K L} ⊆
      Cslib.Complexity.CountingLevel 26 encBits := by
  intro K hK
  exact hK.mem_CountingLevel hL

end LeanCanny.CountingHierarchy.AbstractBridge
