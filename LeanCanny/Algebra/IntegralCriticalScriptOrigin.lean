/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalScript
public import LeanCanny.Algebra.IntegralScalarGeneratorOrigin

/-! # Deterministic creating commands for retained generators

A newest-first bank index selects the same command in the original script.
Its older suffix constructs the exact creating prefix and polynomial.
The recorded embedding reaches the current canonical generator and keeps
its denominator. This identifies the source behind earlier-birth queries.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalScript
open LeanCanny.Encoding LeanCanny.Computation UniformIntegralPrefix
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {S B n W D C : ℕ}

def older (rules : List (Command n W D C)) (i : Fin rules.length) := rules.drop (i.val + 1)
def chosen (rules : List (Command n W D C)) (i : Fin rules.length) := rules[i.val]

theorem older_length (rules : List (Command n W D C)) (i : Fin rules.length) :
    (older rules i).length = rules.length - 1 - i.val := by
  simp only [older, List.length_drop]
  omega

theorem older_bound (rules : List (Command n W D C)) (h : rules.length ≤ S + 1) (i : Fin rules.length) :
    (older rules i).length ≤ S := by
  have H := i.isLt
  rw [older_length]
  omega

theorem past_bound (rules : List (Command n W D C)) (h : rules.length ≤ S + 1) (j : ℕ) :
    (past rules j).length ≤ S + 1 := by
  rw [past_length]
  exact (min_le_right j rules.length).trans h

def pastIndex (rules : List (Command n W D C)) (j : ℕ) (hj : j ≤ rules.length)
    (i : Fin (past rules j).length) : Fin rules.length :=
  ⟨rules.length - j + i.val, by
    have H : i.val < j := i.isLt.trans_le ((past_length rules j).le.trans (min_le_left j rules.length))
    omega⟩

theorem older_past (rules : List (Command n W D C)) (j : ℕ) (hj : j ≤ rules.length) (i : Fin (past rules j).length) :
    older (past rules j) i = older rules (pastIndex rules j hj i) := by
  simp only [older, past, pastIndex, min_eq_left hj, List.drop_drop, Nat.add_assoc]

theorem chosen_past (rules : List (Command n W D C)) (j : ℕ) (hj : j ≤ rules.length) (i : Fin (past rules j).length) :
    chosen (past rules j) i = chosen rules (pastIndex rules j hj i) := by
  simp only [chosen, past, pastIndex, min_eq_left hj, List.getElem_drop]

noncomputable def birthState (rules : List (Command n W D C)) (h : rules.length ≤ S + 1)
    (hN : PurePowerReductionBounds.dimension (n + 1) D ≤ 2 ^ B) (i : Fin rules.length) :=
  run (older rules i) ((older_bound rules h i).trans (Nat.le_add_right S 1)) hN

noncomputable def birthFamily (rules : List (Command n W D C)) (h : rules.length ≤ S + 1)
    (hN : PurePowerReductionBounds.dimension (n + 1) D ≤ 2 ^ B) (i : Fin rules.length) :=
  family (birthState rules h hN i) (older_bound rules h i) (chosen rules i)

theorem birthFamily_past (rules : List (Command n W D C)) (h : rules.length ≤ S + 1)
    (hN : PurePowerReductionBounds.dimension (n + 1) D ≤ 2 ^ B) (j : ℕ) (hj : j ≤ rules.length)
    (i : Fin (past rules j).length) :
    birthFamily (past rules j) (past_bound rules h j) hN i = birthFamily rules h hN (pastIndex rules j hj i) := by
  have HC (a b : List (Command n W D C)) (ha : a.length ≤ S) (hb : b.length ≤ S) (he : a = b) :
      family (run a (ha.trans (Nat.le_add_right S 1)) hN) ha (chosen rules (pastIndex rules j hj i)) =
        family (run b (hb.trans (Nat.le_add_right S 1)) hN) hb (chosen rules (pastIndex rules j hj i)) := by
    subst b
    rfl
  simp only [birthFamily, birthState, chosen_past rules j hj i]
  exact HC _ _ _ _ (older_past rules j hj i)

noncomputable def birthStep (rules : List (Command n W D C)) (h : rules.length ≤ S + 1)
    (hN : PurePowerReductionBounds.dimension (n + 1) D ≤ 2 ^ B) (i : Fin rules.length) :=
  step (birthState rules h hN i) (older_bound rules h i) (chosen rules i) hN

structure Origin (rules : List (Command n W D C)) (h : rules.length ≤ S + 1)
    (hN : PurePowerReductionBounds.dimension (n + 1) D ≤ 2 ^ B) (i : Fin rules.length) where
  chain : Chain S B (birthStep rules h hN i).scalarPrefix (run rules h hN).scalarPrefix
  generator_eq : chain.embed (AdjoinRoot.root _) = (run rules h hN).scalarPrefix.basis.generator i
  denominator_eq : (run rules h hN).bank.denominator i =
    IntegralClearedCriticalLeadingBits.integer (IntegralHistoryCriticalBits.source (birthFamily rules h hN i)) []

noncomputable def origin (rules : List (Command n W D C))
    (hN : PurePowerReductionBounds.dimension (n + 1) D ≤ 2 ^ B) :
    ∀ (h : rules.length ≤ S + 1) (i : Fin rules.length), Origin rules h hN i := by
  induction rules with
  | nil => intro h i; exact Fin.elim0 i
  | cons r rs ih =>
    intro h i
    have HT : rs.length ≤ S + 1 := by simp only [List.length_cons] at h; omega
    have HS : rs.length ≤ S := by simp only [List.length_cons] at h; omega
    refine Fin.cases ?_ (fun j => ?_) i
    · exact ⟨.refl _, rfl, rfl⟩
    · let o := ih HT j
      refine {
        chain := o.chain.step HS ((IntegralHistoryCriticalBits.source (family (run rs HT hN) HS r)).annihilator [])
          (IntegralScalarRootHistoryBounds.degree (family (run rs HT hN) HS r) [])
        generator_eq := ?_
        denominator_eq := o.denominator_eq }
      change AdjoinRoot.of _ (o.chain.embed (AdjoinRoot.root _)) =
        AdjoinRoot.of _ ((run rs HT hN).scalarPrefix.basis.generator j)
      rw [o.generator_eq]

noncomputable def Origin.toGeneratorOrigin {rules : List (Command n W D C)} {h : rules.length ≤ S + 1}
    {hN : PurePowerReductionBounds.dimension (n + 1) D ≤ 2 ^ B} {i : Fin rules.length} (o : Origin rules h hN i) :
    IntegralScalarRootHistoryBounds.GeneratorOrigin (run rules h hN).scalarPrefix (run rules h hN).bank i where
  birth := (older rules i).length
  order := by have H := i.isLt; rw [older_length]; omega
  oldPrefix := (birthState rules h hN i).scalarPrefix
  birth_bound := older_bound rules h i
  polynomial := (IntegralHistoryCriticalBits.source (birthFamily rules h hN i)).annihilator []
  degree := IntegralScalarRootHistoryBounds.degree (birthFamily rules h hN i) []
  degree_bound := degree_le (birthState rules h hN i) (older_bound rules h i) (chosen rules i) hN
  leading := IntegralClearedCriticalLeadingBits.integer (IntegralHistoryCriticalBits.source (birthFamily rules h hN i)) []
  leading_eq := IntegralClearedCriticalLeadingBits.coefficient _ []
  leading_ne_zero := IntegralScalarRootHistoryBounds.integer_nonzero _ []
  chain := o.chain
  generator_eq := o.generator_eq
  denominator_eq := o.denominator_eq

theorem Origin.matrix {rules : List (Command n W D C)} {h : rules.length ≤ S + 1}
    {hN : PurePowerReductionBounds.dimension (n + 1) D ≤ 2 ^ B} {i : Fin rules.length}
    (o : Origin rules h hN i) (r t : Fin (FixedWidthPolynomial.count rules.length B)) :
    Algebra.leftMulMatrix (run rules h hN).scalarPrefix.basis.finBasis
      ((run rules h hN).scalarPrefix.basis.generator i) r t =
      if r.val % o.chain.radix = t.val % o.chain.radix then
        Algebra.leftMulMatrix (birthStep rules h hN i).scalarPrefix.basis.finBasis
          (AdjoinRoot.root _) (o.chain.oldIndex r) (o.chain.oldIndex t) else 0 := by
  rw [← o.generator_eq]
  exact o.chain.matrix _ r t

end LeanCanny.Algebra.IntegralCriticalScript
