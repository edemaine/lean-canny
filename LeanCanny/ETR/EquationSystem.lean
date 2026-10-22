/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.Normalization
public import LeanCanny.ETR.EncodingBounds

/-!
# Boolean formulas as systems of polynomial equations

Negations are first pushed to the atoms. Conjunction concatenates equation lists.
Disjunction introduces a fresh Boolean selector and multiplies each branch's equations
by its selector. Each equation is retained once, so nested conjunctions do not cause
the exponential copying that repeated sums of squares would cause.
-/

@[expose] public section

namespace LeanCanny.ETR

/-- Negation normal form, including the complements of the original atomic relations. -/
inductive SignedFormula where
  | truth | falsum
  | eqZero : Term → SignedFormula
  | neZero : Term → SignedFormula
  | ltZero : Term → SignedFormula
  | nonneg : Term → SignedFormula
  | and : SignedFormula → SignedFormula → SignedFormula
  | or : SignedFormula → SignedFormula → SignedFormula
  deriving DecidableEq, Repr

namespace SignedFormula

def Holds (env : ℕ → ℝ) : SignedFormula → Prop
  | .truth => True
  | .falsum => False
  | .eqZero t => t.eval env = 0
  | .neZero t => t.eval env ≠ 0
  | .ltZero t => t.eval env < 0
  | .nonneg t => 0 ≤ t.eval env
  | .and p q => p.Holds env ∧ q.Holds env
  | .or p q => p.Holds env ∨ q.Holds env

def arity : SignedFormula → ℕ
  | .truth | .falsum => 0
  | .eqZero t | .neZero t | .ltZero t | .nonneg t => t.arity
  | .and p q | .or p q => max p.arity q.arity

theorem holds_congr (p : SignedFormula) (env env' : ℕ → ℝ)
    (h : ∀ i < p.arity, env i = env' i) : p.Holds env ↔ p.Holds env' := by
  induction p with
  | truth => rfl
  | falsum => rfl
  | eqZero t | neZero t | ltZero t | nonneg t =>
      simp only [Holds, t.eval_congr env env' h]
  | and p q hp hq =>
      exact and_congr (hp fun i hi => h i (hi.trans_le (Nat.le_max_left ..)))
        (hq fun i hi => h i (hi.trans_le (Nat.le_max_right ..)))
  | or p q hp hq =>
      exact or_congr (hp fun i hi => h i (hi.trans_le (Nat.le_max_left ..)))
        (hq fun i hi => h i (hi.trans_le (Nat.le_max_right ..)))

end SignedFormula

namespace Formula

/-- `positive = false` normalizes the complement, without duplicating subformulas. -/
def toSigned : Formula → Bool → SignedFormula
  | .falsum, positive => if positive then .falsum else .truth
  | .eqZero t, positive => if positive then .eqZero t else .neZero t
  | .ltZero t, positive => if positive then .ltZero t else .nonneg t
  | .not p, positive => p.toSigned (!positive)
  | .and p q, positive =>
      if positive then .and (p.toSigned true) (q.toSigned true)
      else .or (p.toSigned false) (q.toSigned false)
  | .or p q, positive =>
      if positive then .or (p.toSigned true) (q.toSigned true)
      else .and (p.toSigned false) (q.toSigned false)

@[simp] theorem toSigned_arity (p : Formula) (positive : Bool) :
    (p.toSigned positive).arity = p.arity := by
  induction p generalizing positive <;> cases positive <;>
    simp_all [toSigned, arity, SignedFormula.arity]

theorem holds_toSigned (p : Formula) (positive : Bool) (env : ℕ → ℝ) :
    (p.toSigned positive).Holds env ↔ if positive then p.Holds env else ¬ p.Holds env := by
  classical
  induction p generalizing positive <;> cases positive <;>
    simp_all [toSigned, Holds, SignedFormula.Holds]
  all_goals tauto

end Formula

namespace Term

/-- `1-x_i`, the complementary branch selector. -/
def oneMinus (i : ℕ) : Term := .add (.const 1) (.mul (.const (-1)) (.var i))

/-- Enforce `x_i ∈ {0,1}`. -/
def booleanEquation (i : ℕ) : Term := .mul (.var i) (.add (.var i) (.const (-1)))

/-- A nonnegative term is the square of a fresh witness. -/
def nonnegativeEquation (t : Term) (i : ℕ) : Term :=
  .add t (.mul (.const (-1)) (.square (.var i)))

@[simp] theorem eval_oneMinus (i : ℕ) (env : ℕ → ℝ) :
    (oneMinus i).eval env = 1 - env i := by
  simp [oneMinus, eval, sub_eq_add_neg]

theorem eval_booleanEquation_eq_zero_iff (i : ℕ) (env : ℕ → ℝ) :
    (booleanEquation i).eval env = 0 ↔ env i = 0 ∨ env i = 1 := by
  simp [booleanEquation, eval, mul_eq_zero, add_neg_eq_zero]

end Term

/-- A finite conjunction of zero equations, with the next available variable index. -/
structure EquationSystem where
  terms : List Term
  next : ℕ
  deriving DecidableEq, Repr

namespace EquationSystem

def Holds (s : EquationSystem) (env : ℕ → ℝ) : Prop :=
  ∀ t ∈ s.terms, t.eval env = 0

def Satisfiable (s : EquationSystem) : Prop := ∃ env : ℕ → ℝ, s.Holds env

def conjunction (a b : EquationSystem) : EquationSystem := ⟨a.terms ++ b.terms, b.next⟩

/-- Both branches have been compiled into disjoint fresh-variable intervals. The selector
is allocated after them. Multiplication retains each branch equation exactly once. -/
def disjunction (a b : EquationSystem) : EquationSystem :=
  ⟨Term.booleanEquation b.next ::
    (a.terms.map (Term.mul (.var b.next)) ++
      b.terms.map (Term.mul (Term.oneMinus b.next))), b.next + 1⟩

@[simp] theorem holds_conjunction (a b : EquationSystem) (env : ℕ → ℝ) :
    (conjunction a b).Holds env ↔ a.Holds env ∧ b.Holds env := by
  simp only [conjunction, Holds, List.mem_append, or_imp, forall_and]

theorem holds_disjunction_iff (a b : EquationSystem) (env : ℕ → ℝ) :
    (disjunction a b).Holds env ↔
      (env b.next = 1 ∧ a.Holds env) ∨ (env b.next = 0 ∧ b.Holds env) := by
  simp only [disjunction, Holds, List.mem_cons, List.mem_append, or_imp, forall_and,
    forall_eq,
    List.forall_mem_map, Term.eval, Term.eval_oneMinus, Term.eval_booleanEquation_eq_zero_iff]
  constructor
  · rintro ⟨hbool, ha, hb⟩
    rcases hbool with hzero | hone
    · right
      exact ⟨hzero, by simpa [hzero] using hb⟩
    · left
      exact ⟨hone, by simpa [hone] using ha⟩
  · rintro (⟨hone, ha⟩ | ⟨hzero, hb⟩)
    · simpa [hone] using ha
    · simpa [hzero] using hb

end EquationSystem

namespace SignedFormula

/-- Compile to equations, reserving all indices below `start` for the original variables. -/
def equations : SignedFormula → ℕ → EquationSystem
  | .truth, start => ⟨[], start⟩
  | .falsum, start => ⟨[.const 1], start⟩
  | .eqZero t, start => ⟨[t], start⟩
  | .neZero t, start => ⟨[t.nonzeroEquation start], start + 1⟩
  | .ltZero t, start => ⟨[t.negativeEquation start], start + 1⟩
  | .nonneg t, start => ⟨[t.nonnegativeEquation start], start + 1⟩
  | .and p q, start =>
      let a := p.equations start
      let b := q.equations a.next
      a.conjunction b
  | .or p q, start =>
      let a := p.equations start
      let b := q.equations a.next
      a.disjunction b

theorem equations_next_ge (p : SignedFormula) (start : ℕ) :
    start ≤ (p.equations start).next := by
  induction p generalizing start with
  | and p q ihp ihq => exact (ihp start).trans (ihq _)
  | or p q ihp ihq => exact ((ihp start).trans (ihq _)).trans (Nat.le_succ _)
  | _ => simp [equations]

theorem equations_scoped (p : SignedFormula) (start : ℕ) (hp : p.arity ≤ start) :
    ∀ t ∈ (p.equations start).terms, t.arity ≤ (p.equations start).next := by
  induction p generalizing start with
  | truth => simp [equations]
  | falsum => simp [equations, Term.arity]
  | eqZero t => simpa [equations, arity] using hp
  | neZero t =>
      simp only [equations, List.mem_singleton, forall_eq, Term.nonzeroEquation, Term.arity]
      simp only [arity] at hp
      omega
  | ltZero t =>
      simp only [equations, List.mem_singleton, forall_eq, Term.negativeEquation,
        Term.square, Term.arity]
      simp only [arity] at hp
      omega
  | nonneg t =>
      simp only [equations, List.mem_singleton, forall_eq, Term.nonnegativeEquation,
        Term.square, Term.arity]
      simp only [arity] at hp
      omega
  | and p q ihp ihq =>
      have hp' : p.arity ≤ start := (Nat.le_max_left ..).trans hp
      have hq' : q.arity ≤ start := (Nat.le_max_right ..).trans hp
      have hn := equations_next_ge p start
      have hn' := equations_next_ge q (p.equations start).next
      simp only [equations, EquationSystem.conjunction, List.mem_append, or_imp, forall_and]
      exact ⟨fun t ht => (ihp start hp' t ht).trans hn',
        ihq _ (hq'.trans hn)⟩
  | or p q ihp ihq =>
      have hp' : p.arity ≤ start := (Nat.le_max_left ..).trans hp
      have hq' : q.arity ≤ start := (Nat.le_max_right ..).trans hp
      have hn := equations_next_ge p start
      have hn' := equations_next_ge q (p.equations start).next
      simp only [equations, EquationSystem.disjunction, List.mem_cons, List.mem_append,
        or_imp, forall_and, forall_eq, List.forall_mem_map]
      constructor
      · simp [Term.booleanEquation, Term.arity]
      constructor
      · intro t ht
        have := ihp start hp' t ht
        simp only [Term.arity]
        omega
      · intro t ht
        have := ihq _ (hq'.trans hn) t ht
        simp only [Term.arity, Term.oneMinus]
        omega

end SignedFormula

/-- Nonnegative reals are exactly the squares of real witnesses. -/
theorem nonneg_iff_exists_sub_sq_eq_zero (x : ℝ) :
    0 ≤ x ↔ ∃ y : ℝ, x + (-1) * (y * y) = 0 := by
  constructor
  · intro hx
    refine ⟨Real.sqrt x, ?_⟩
    rw [← pow_two, Real.sq_sqrt hx]
    ring
  · rintro ⟨y, hy⟩
    have := mul_self_nonneg y
    linarith

namespace SignedFormula

/-- Every solution of the compiled equations satisfies the original formula. -/
theorem equations_sound (p : SignedFormula) (start : ℕ) (env : ℕ → ℝ)
    (h : (p.equations start).Holds env) : p.Holds env := by
  induction p generalizing start with
  | truth => trivial
  | falsum => simp [equations, EquationSystem.Holds, Term.eval] at h
  | eqZero t => simpa [equations, EquationSystem.Holds, Holds] using h
  | neZero t =>
      have hh := h (t.nonzeroEquation start) (by simp [equations])
      simp only [Term.nonzeroEquation, Term.eval, Int.cast_neg, Int.cast_one] at hh
      exact (ne_zero_iff_exists_mul_eq_one _).mpr ⟨env start, by linarith⟩
  | ltZero t =>
      have hh := h (t.negativeEquation start) (by simp [equations])
      simp only [Term.negativeEquation, Term.square, Term.eval, Int.cast_one] at hh
      exact (lt_zero_iff_exists_mul_sq_add_one_eq_zero _).mpr ⟨env start, hh⟩
  | nonneg t =>
      have hh := h (t.nonnegativeEquation start) (by simp [equations])
      simp only [Term.nonnegativeEquation, Term.square, Term.eval,
        Int.cast_neg, Int.cast_one] at hh
      exact (nonneg_iff_exists_sub_sq_eq_zero _).mpr ⟨env start, hh⟩
  | and p q ihp ihq =>
      obtain ⟨ha, hb⟩ := (EquationSystem.holds_conjunction _ _ env).mp h
      exact ⟨ihp _ ha, ihq _ hb⟩
  | or p q ihp ihq =>
      rcases (EquationSystem.holds_disjunction_iff _ _ env).mp h with ⟨_, ha⟩ | ⟨_, hb⟩
      · exact Or.inl (ihp _ ha)
      · exact Or.inr (ihq _ hb)

/-- Every satisfying assignment extends to a solution of the equations. Original variables
below `start` are preserved; all allocated witnesses and selectors lie above that boundary. -/
theorem equations_complete (p : SignedFormula) (start : ℕ) (hp : p.arity ≤ start)
    (env : ℕ → ℝ) (h : p.Holds env) :
    ∃ env' : ℕ → ℝ, (∀ i < start, env i = env' i) ∧ (p.equations start).Holds env' := by
  induction p generalizing start env with
  | truth => exact ⟨env, fun _ _ => rfl, by simp [equations, EquationSystem.Holds]⟩
  | falsum => exact False.elim h
  | eqZero t =>
      exact ⟨env, fun _ _ => rfl, by simpa [equations, EquationSystem.Holds, Holds] using h⟩
  | neZero t =>
      obtain ⟨y, hy⟩ := (ne_zero_iff_exists_mul_eq_one _).mp h
      refine ⟨Function.update env start y, ?_, ?_⟩
      · intro i hi
        exact (Function.update_of_ne (by omega : i ≠ start) y env).symm
      · simp only [equations, EquationSystem.Holds, List.mem_singleton, forall_eq,
          Term.nonzeroEquation, Term.eval, Term.eval_update_fresh t env start y hp,
          Function.update_self, Int.cast_neg, Int.cast_one]
        linarith
  | ltZero t =>
      obtain ⟨y, hy⟩ := (lt_zero_iff_exists_mul_sq_add_one_eq_zero _).mp h
      refine ⟨Function.update env start y, ?_, ?_⟩
      · intro i hi
        exact (Function.update_of_ne (by omega : i ≠ start) y env).symm
      · simpa only [equations, EquationSystem.Holds, List.mem_singleton, forall_eq,
          Term.negativeEquation, Term.square, Term.eval, Term.eval_update_fresh t env start y hp,
          Function.update_self, Int.cast_one] using hy
  | nonneg t =>
      obtain ⟨y, hy⟩ := (nonneg_iff_exists_sub_sq_eq_zero _).mp h
      refine ⟨Function.update env start y, ?_, ?_⟩
      · intro i hi
        exact (Function.update_of_ne (by omega : i ≠ start) y env).symm
      · simpa only [equations, EquationSystem.Holds, List.mem_singleton, forall_eq,
          Term.nonnegativeEquation, Term.square, Term.eval,
          Term.eval_update_fresh t env start y hp, Function.update_self,
          Int.cast_neg, Int.cast_one] using hy
  | and p q ihp ihq =>
      have hp' : p.arity ≤ start := (Nat.le_max_left ..).trans hp
      have hq' : q.arity ≤ start := (Nat.le_max_right ..).trans hp
      obtain ⟨env₁, agree₁, ha⟩ := ihp start hp' env h.1
      have hq₁ := (q.holds_congr env env₁ (fun i hi => agree₁ i (hi.trans_le hq'))).mp h.2
      obtain ⟨env₂, agree₂, hb⟩ :=
        ihq _ (hq'.trans (equations_next_ge p start)) env₁ hq₁
      refine ⟨env₂, ?_, (EquationSystem.holds_conjunction _ _ _).mpr ⟨?_, hb⟩⟩
      · intro i hi
        exact (agree₁ i hi).trans (agree₂ i (hi.trans_le (equations_next_ge p start)))
      · intro t ht
        rw [← t.eval_congr env₁ env₂
          (fun i hi => agree₂ i (hi.trans_le (equations_scoped p start hp' t ht)))]
        exact ha t ht
  | or p q ihp ihq =>
      have hp' : p.arity ≤ start := (Nat.le_max_left ..).trans hp
      have hq' : q.arity ≤ start := (Nat.le_max_right ..).trans hp
      let boundary := (q.equations (p.equations start).next).next
      have hmid : (p.equations start).next ≤ boundary := equations_next_ge q _
      have hstart : start ≤ boundary := (equations_next_ge p start).trans hmid
      rcases h with hleft | hright
      · obtain ⟨env₁, agree₁, ha⟩ := ihp start hp' env hleft
        refine ⟨Function.update env₁ boundary 1, ?_, ?_⟩
        · intro i hi
          exact (agree₁ i hi).trans
            (Function.update_of_ne (by omega : i ≠ boundary) 1 env₁).symm
        · apply (EquationSystem.holds_disjunction_iff _ _ _).mpr
          left
          refine ⟨Function.update_self .., ?_⟩
          intro t ht
          rw [t.eval_update_fresh env₁ boundary 1
            ((equations_scoped p start hp' t ht).trans hmid)]
          exact ha t ht
      · obtain ⟨env₁, agree₁, hb⟩ :=
          ihq _ (hq'.trans (equations_next_ge p start)) env hright
        refine ⟨Function.update env₁ boundary 0, ?_, ?_⟩
        · intro i hi
          exact (agree₁ i (hi.trans_le (equations_next_ge p start))).trans
            (Function.update_of_ne (by omega : i ≠ boundary) 0 env₁).symm
        · apply (EquationSystem.holds_disjunction_iff _ _ _).mpr
          right
          refine ⟨Function.update_self .., ?_⟩
          intro t ht
          rw [t.eval_update_fresh env₁ boundary 0
            (equations_scoped q _ (hq'.trans (equations_next_ge p start)) t ht)]
          exact hb t ht

end SignedFormula

namespace Formula

/-- The equation system for an ETR instance, with all original indices reserved. -/
def equationSystem (p : Formula) : EquationSystem := (p.toSigned true).equations p.arity

/-- Arbitrary Boolean ETR formulas and their compiled equation systems are equisatisfiable. -/
theorem satisfiable_iff_equationSystem (p : Formula) :
    p.Satisfiable ↔ p.equationSystem.Satisfiable := by
  constructor
  · rintro ⟨env, h⟩
    have hp := (p.holds_toSigned true env).mpr h
    obtain ⟨env', _, heq⟩ :=
      (p.toSigned true).equations_complete p.arity (by simp) env hp
    exact ⟨env', heq⟩
  · rintro ⟨env, h⟩
    exact ⟨env, (p.holds_toSigned true env).mp ((p.toSigned true).equations_sound _ env h)⟩

end Formula
end LeanCanny.ETR
