/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedCriticalIntervalPredicate
public import LeanCanny.Encoding.CoefficientMarkedCriticalRootContext
/-! # The shared critical counterexample predicate forgets the parent word -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedCriticalPredicateContext
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false

abbrev rooted (q : List Bool) := pair (IntegralMixedPhysicalCriticalQuery.root q) []

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

private noncomputable def predicate {P C I : ℕ}
    (family : Bool → Fin I → ℕ → MvPolynomial ℕ ℤ[X]) (degree : ℕ)
    (β : ℝ) (parent : Fin P → ℝ) (child : Fin C → ℝ) : Prop :=
  ∀ i : Fin I, ∀ k < degree + 1,
    SignType.sign ((family false i k).eval₂ (SymbolicScaledSquarefree.scalarEvaluation β)
      (CoefficientMarkedCriticalBankIncidence.natural parent)) =
    SignType.sign ((family true i k).eval₂ (SymbolicScaledSquarefree.scalarEvaluation β)
      (CoefficientMarkedCriticalBankIncidence.natural child))

private theorem predicate_heq {P C I P' C' I' : ℕ}
    (f : Bool → Fin I → ℕ → MvPolynomial ℕ ℤ[X])
    (g : Bool → Fin I' → ℕ → MvPolynomial ℕ ℤ[X]) (d e : ℕ)
    (hp : P = P') (hc : C = C') (hi : I = I') (hd : d = e) (hf : HEq f g) :
    HEq (predicate (P := P) (C := C) f d) (predicate (P := P') (C := C') g e) := by
  cases hp
  cases hc
  cases hi
  cases hd
  cases eq_of_heq hf
  rfl

private noncomputable def count (child : Bool) (q : List Bool) :=
  (CoefficientMarkedRecordRows.symbolic hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
    (CoefficientMarkedCriticalBankQuery.stage child q) (Nat.sub_le _ _)).count

private theorem count_root (child : Bool) (q : List Bool) :
    count hn ht ha child q = count hn ht ha child (rooted q) := by
  unfold count CoefficientMarkedCriticalBankQuery.stage
  simp only [rooted, IntegralMixedPhysicalCriticalQuery.root, pairFst_pair]

private theorem birth_root (q : List Bool) :
    CoefficientMarkedCriticalBankSource.birth n q = CoefficientMarkedCriticalBankSource.birth n (rooted q) := by
  unfold CoefficientMarkedCriticalBankSource.birth CoefficientMarkedCriticalBankSource.stage
  simp only [rooted, IntegralMixedPhysicalCriticalQuery.root, pairFst_pair]

private theorem degree_root (q : List Bool) :
    IntegralMixedPhysicalCriticalBankEquality.catalogDegree hn ht ha q =
      IntegralMixedPhysicalCriticalBankEquality.catalogDegree hn ht ha (rooted q) := by
  unfold IntegralMixedPhysicalCriticalBankEquality.catalogDegree
    IntegralMixedPhysicalCriticalPrefixes.birth IntegralMixedPhysicalMarkedPlan.leafCount
  simp only [rooted, IntegralMixedPhysicalCriticalQuery.root, pairFst_pair]

attribute [local irreducible] CoefficientMarkedRecordRows.symbolic
  CoefficientMarkedCriticalBankQuery.physical predicate

private theorem agrees_factor (q : List Bool) :
    HEq (CoefficientMarkedCriticalBankIncidence.Agrees hn ht ha q)
      (predicate (P := count hn ht ha false q) (C := count hn ht ha true q)
        (fun child (i : Fin (CoefficientMarkedCriticalBankSource.birth n q)) k =>
          CoefficientMarkedCriticalBankQuery.physical hn ht ha child q i k)
        (IntegralMixedPhysicalCriticalBankEquality.catalogDegree hn ht ha q)) := by
  unfold predicate count
  rfl

/-- The whole bank incidence predicate, including both raw point types, is
determined by ROOT. -/
theorem bank_agrees_root (q : List Bool) :
    HEq (CoefficientMarkedCriticalBankIncidence.Agrees hn ht ha q)
      (CoefficientMarkedCriticalBankIncidence.Agrees hn ht ha (rooted q)) := by
  have hf := CoefficientMarkedCriticalRootContext.bank_queries_root hn ht ha q (rooted q)
    (by simp only [rooted, IntegralMixedPhysicalCriticalQuery.root, pairFst_pair])
  have hh := predicate_heq
    (P := count hn ht ha false q) (C := count hn ht ha true q)
    (P' := count hn ht ha false (rooted q)) (C' := count hn ht ha true (rooted q))
    (fun child (i : Fin (CoefficientMarkedCriticalBankSource.birth n q)) k =>
      CoefficientMarkedCriticalBankQuery.physical hn ht ha child q i k)
    (fun child (i : Fin (CoefficientMarkedCriticalBankSource.birth n (rooted q))) k =>
      CoefficientMarkedCriticalBankQuery.physical hn ht ha child (rooted q) i k)
    _ _ (count_root hn ht ha false q) (count_root hn ht ha true q)
    (birth_root (n := n) q) (degree_root hn ht ha q) hf
  exact (agrees_factor hn ht ha q).trans (hh.trans (agrees_factor hn ht ha (rooted q)).symm)

private theorem dependent_heq {α : Sort*} {B : α → Sort*} (f : (a : α) → B a)
    (a b : α) (h : a = b) : HEq (f a) (f b) := by
  subst b
  rfl

private noncomputable def correlationAt (ctx aux : List Bool) :=
  CoefficientMarkedRecordCriticalFullQuery.polynomial hn ht ha ctx
    (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl aux
    (IntegralMixedPhysicalMarkedPlan.leafCount n false (pair ctx []) + IntegralMixedCausalRecordPlanBits.count ctx - 1)

private theorem correlation_factor (q : List Bool) :
    HEq (CoefficientMarkedCriticalCorrelationIncidence.polynomial hn ht ha q)
      (correlationAt hn ht ha (IntegralMixedPhysicalCriticalQuery.root q) q) := by
  unfold correlationAt CoefficientMarkedCriticalCorrelationIncidence.polynomial
    IntegralMixedPhysicalCriticalPrefixes.birth
  rfl

theorem correlation_root (q : List Bool) :
    HEq (CoefficientMarkedCriticalCorrelationIncidence.polynomial hn ht ha q)
      (CoefficientMarkedCriticalCorrelationIncidence.polynomial hn ht ha (rooted q)) := by
  have haux : correlationAt hn ht ha (IntegralMixedPhysicalCriticalQuery.root q) q =
      correlationAt hn ht ha (IntegralMixedPhysicalCriticalQuery.root q) (rooted q) :=
    CoefficientMarkedCriticalRootContext.correlation_aux hn ht ha (IntegralMixedPhysicalCriticalQuery.root q)
      (IntegralMixedCausalRecordPlanBits.count (IntegralMixedPhysicalCriticalQuery.root q)) le_rfl q (rooted q) _
  have hroot := dependent_heq (fun ctx => correlationAt hn ht ha ctx (rooted q))
    (IntegralMixedPhysicalCriticalQuery.root q) (IntegralMixedPhysicalCriticalQuery.root (rooted q))
    (by simp only [rooted, IntegralMixedPhysicalCriticalQuery.root, pairFst_pair])
  exact (correlation_factor hn ht ha q).trans ((heq_of_eq haux).trans
    (hroot.trans (correlation_factor hn ht ha (rooted q)).symm))

private theorem interval_root (upper : Bool) (q : List Bool) :
    HEq (CoefficientMarkedCriticalIntervalQuery.polynomial hn ht ha upper
      (IntegralMixedPhysicalCriticalQuery.root q))
      (CoefficientMarkedCriticalIntervalQuery.polynomial hn ht ha upper
        (IntegralMixedPhysicalCriticalQuery.root (rooted q))) :=
  dependent_heq (CoefficientMarkedCriticalIntervalQuery.polynomial hn ht ha upper) _ _
    (by simp only [rooted, IntegralMixedPhysicalCriticalQuery.root, pairFst_pair])

private noncomputable def tests {P C : ℕ}
    (bank : ℝ → (Fin P → ℝ) → (Fin C → ℝ) → Prop)
    (correlation lower upper : MvPolynomial (Fin C) ℤ[X])
    (β : ℝ) (parent : Fin P → ℝ) (child : Fin C → ℝ) : Prop :=
  bank β parent child ∧ correlation.eval₂ (SymbolicScaledSquarefree.scalarEvaluation β) child = 0 ∧
    SignType.sign (lower.eval₂ (SymbolicScaledSquarefree.scalarEvaluation β) child) = 1 ∧
    SignType.sign (upper.eval₂ (SymbolicScaledSquarefree.scalarEvaluation β) child) = 1

private theorem tests_heq {P C P' C' : ℕ}
    (bank : ℝ → (Fin P → ℝ) → (Fin C → ℝ) → Prop)
    (bank' : ℝ → (Fin P' → ℝ) → (Fin C' → ℝ) → Prop)
    (correlation lower upper : MvPolynomial (Fin C) ℤ[X])
    (correlation' lower' upper' : MvPolynomial (Fin C') ℤ[X])
    (hp : P = P') (hc : C = C') (hb : HEq bank bank') (hcor : HEq correlation correlation')
    (hl : HEq lower lower') (hu : HEq upper upper') :
    HEq (tests bank correlation lower upper) (tests bank' correlation' lower' upper') := by
  cases hp
  cases hc
  cases eq_of_heq hb
  cases eq_of_heq hcor
  cases eq_of_heq hl
  cases eq_of_heq hu
  rfl

private theorem tests_factor (q : List Bool) :
    HEq (CoefficientMarkedCriticalIntervalPredicate.Tests hn ht ha q)
      (tests (P := count hn ht ha false q) (C := count hn ht ha true q)
        (CoefficientMarkedCriticalBankIncidence.Agrees hn ht ha q)
        (CoefficientMarkedCriticalCorrelationIncidence.polynomial hn ht ha q)
        (CoefficientMarkedCriticalIntervalQuery.polynomial hn ht ha false (IntegralMixedPhysicalCriticalQuery.root q))
        (CoefficientMarkedCriticalIntervalQuery.polynomial hn ht ha true (IntegralMixedPhysicalCriticalQuery.root q))) := by
  unfold tests count
  rfl

/-- All four conjuncts use the same tuples after AUX is erased. -/
theorem tests_root (q : List Bool) :
    HEq (CoefficientMarkedCriticalIntervalPredicate.Tests hn ht ha q)
      (CoefficientMarkedCriticalIntervalPredicate.Tests hn ht ha (rooted q)) := by
  have hh := tests_heq
    (P := count hn ht ha false q) (C := count hn ht ha true q)
    (P' := count hn ht ha false (rooted q)) (C' := count hn ht ha true (rooted q))
    (CoefficientMarkedCriticalBankIncidence.Agrees hn ht ha q)
    (CoefficientMarkedCriticalBankIncidence.Agrees hn ht ha (rooted q))
    (CoefficientMarkedCriticalCorrelationIncidence.polynomial hn ht ha q)
    (CoefficientMarkedCriticalIntervalQuery.polynomial hn ht ha false (IntegralMixedPhysicalCriticalQuery.root q))
    (CoefficientMarkedCriticalIntervalQuery.polynomial hn ht ha true (IntegralMixedPhysicalCriticalQuery.root q))
    (CoefficientMarkedCriticalCorrelationIncidence.polynomial hn ht ha (rooted q))
    (CoefficientMarkedCriticalIntervalQuery.polynomial hn ht ha false (IntegralMixedPhysicalCriticalQuery.root (rooted q)))
    (CoefficientMarkedCriticalIntervalQuery.polynomial hn ht ha true (IntegralMixedPhysicalCriticalQuery.root (rooted q)))
    (count_root hn ht ha false q) (count_root hn ht ha true q)
    (bank_agrees_root hn ht ha q) (correlation_root hn ht ha q)
    (interval_root hn ht ha false q) (interval_root hn ht ha true q)
  exact (tests_factor hn ht ha q).trans (hh.trans (tests_factor hn ht ha (rooted q)).symm)

private noncomputable def counterexample {P C : ℕ}
    (rows : ℝ → (Fin C → ℝ) → Prop)
    (conditions : ℝ → (Fin P → ℝ) → (Fin C → ℝ) → Prop)
    (β : ℝ) (parent : Fin P → ℝ) : Prop :=
  ∃ child : Fin C → ℝ, rows β child ∧ conditions β parent child

private theorem counterexample_heq {P C P' C' : ℕ}
    (rows : ℝ → (Fin C → ℝ) → Prop) (rows' : ℝ → (Fin C' → ℝ) → Prop)
    (conditions : ℝ → (Fin P → ℝ) → (Fin C → ℝ) → Prop)
    (conditions' : ℝ → (Fin P' → ℝ) → (Fin C' → ℝ) → Prop)
    (hp : P = P') (hc : C = C') (hr : HEq rows rows') (ht : HEq conditions conditions') :
    HEq (counterexample rows conditions) (counterexample rows' conditions') := by
  cases hp
  cases hc
  cases eq_of_heq hr
  cases eq_of_heq ht
  rfl

private noncomputable def rowsAt (ctx : List Bool) :=
  CoefficientMarkedRecordRootBranches.RowsAt hn ht ha ctx
    (IntegralMixedCausalRecordPlanBits.count ctx) le_rfl

private theorem counterexample_factor (q : List Bool) :
    HEq (CoefficientMarkedCriticalIntervalPredicate.Counterexample hn ht ha q)
      (counterexample (P := count hn ht ha false q) (C := count hn ht ha true q)
        (rowsAt hn ht ha (IntegralMixedPhysicalCriticalQuery.root q))
        (CoefficientMarkedCriticalIntervalPredicate.Tests hn ht ha q)) := by
  unfold counterexample rowsAt count
  rfl

/-- The rejected complete child search is ROOT determined as a whole,
including the fixed parent tuple and the quantified SAME complete child tuple. -/
theorem counterexample_root (q : List Bool) :
    HEq (CoefficientMarkedCriticalIntervalPredicate.Counterexample hn ht ha q)
      (CoefficientMarkedCriticalIntervalPredicate.Counterexample hn ht ha (rooted q)) := by
  have hr := dependent_heq (rowsAt hn ht ha)
    (IntegralMixedPhysicalCriticalQuery.root q) (IntegralMixedPhysicalCriticalQuery.root (rooted q))
    (by simp only [rooted, IntegralMixedPhysicalCriticalQuery.root, pairFst_pair])
  have hh := counterexample_heq
    (P := count hn ht ha false q) (C := count hn ht ha true q)
    (P' := count hn ht ha false (rooted q)) (C' := count hn ht ha true (rooted q))
    (rowsAt hn ht ha (IntegralMixedPhysicalCriticalQuery.root q))
    (rowsAt hn ht ha (IntegralMixedPhysicalCriticalQuery.root (rooted q)))
    (CoefficientMarkedCriticalIntervalPredicate.Tests hn ht ha q)
    (CoefficientMarkedCriticalIntervalPredicate.Tests hn ht ha (rooted q))
    (count_root hn ht ha false q) (count_root hn ht ha true q) hr (tests_root hn ht ha q)
  exact (counterexample_factor hn ht ha q).trans (hh.trans (counterexample_factor hn ht ha (rooted q)).symm)

private theorem apply_one {A B : Type} (f : ℝ → A → Prop) (g : ℝ → B → Prop)
    (hf : HEq f g) (β : ℝ) (a : A) (b : B) (ha : HEq a b) : f β a ↔ g β b := by
  cases ha
  cases eq_of_heq hf
  rfl

private theorem apply_two {A B C D : Type} (f : ℝ → A → C → Prop) (g : ℝ → B → D → Prop)
    (hf : HEq f g) (β : ℝ) (a : A) (b : B) (c : C) (d : D) (ha : HEq a b) (hc : HEq c d) :
    f β a c ↔ g β b d := by
  cases ha
  cases hc
  cases eq_of_heq hf
  rfl

/-- Equality of the prepared ROOT transports actual bank incidence on the
SAME two entire tuples, including their dependent native dimensions. -/
theorem bank_agrees_iff (q r : List Bool)
    (hroot : IntegralMixedPhysicalCriticalQuery.root q = IntegralMixedPhysicalCriticalQuery.root r) (β : ℝ)
    (parent : CoefficientMarkedCriticalIntervalPredicate.Point hn ht ha false q)
    (child : CoefficientMarkedCriticalIntervalPredicate.Point hn ht ha true q)
    (parent' : CoefficientMarkedCriticalIntervalPredicate.Point hn ht ha false r)
    (child' : CoefficientMarkedCriticalIntervalPredicate.Point hn ht ha true r)
    (hp : HEq parent parent') (hc : HEq child child') :
    CoefficientMarkedCriticalBankIncidence.Agrees hn ht ha q β parent child ↔
      CoefficientMarkedCriticalBankIncidence.Agrees hn ht ha r β parent' child' := by
  have hm := dependent_heq (fun ctx => CoefficientMarkedCriticalBankIncidence.Agrees hn ht ha (pair ctx []))
    (IntegralMixedPhysicalCriticalQuery.root q) (IntegralMixedPhysicalCriticalQuery.root r) hroot
  have hf := (bank_agrees_root hn ht ha q).trans (hm.trans (bank_agrees_root hn ht ha r).symm)
  exact apply_two _ _ hf β parent parent' child child' hp hc

/-- ROOT equality transports the whole existential complete-child search;
every quantified child tuple is retained, rather than a selected witness. -/
theorem counterexample_iff (q r : List Bool)
    (hroot : IntegralMixedPhysicalCriticalQuery.root q = IntegralMixedPhysicalCriticalQuery.root r) (β : ℝ)
    (parent : CoefficientMarkedCriticalIntervalPredicate.Point hn ht ha false q)
    (parent' : CoefficientMarkedCriticalIntervalPredicate.Point hn ht ha false r)
    (hp : HEq parent parent') :
    CoefficientMarkedCriticalIntervalPredicate.Counterexample hn ht ha q β parent ↔
      CoefficientMarkedCriticalIntervalPredicate.Counterexample hn ht ha r β parent' := by
  have hm := dependent_heq (fun ctx => CoefficientMarkedCriticalIntervalPredicate.Counterexample hn ht ha (pair ctx []))
    (IntegralMixedPhysicalCriticalQuery.root q) (IntegralMixedPhysicalCriticalQuery.root r) hroot
  have hf := (counterexample_root hn ht ha q).trans (hm.trans (counterexample_root hn ht ha r).symm)
  exact apply_one _ _ hf β parent parent' hp

end LeanCanny.Encoding.CoefficientMarkedCriticalPredicateContext
