/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaStrictWitness
public import LeanCanny.Geometry.WeakBooleanWitness
/-! # Polynomial sign conditions uniquely describe the continuous weak-circle section -/
@[expose] public section
namespace LeanCanny.Geometry.WeakCircleCanonicalFormula
open LeanCanny.ETR CircularWitness LeanCanny.Connectivity Set
open scoped Classical

def nonnegative (t : Term) : Formula := .not (.ltZero t)
def difference (a b : Term) : Term := .add a (.mul (.const (-1)) b)
def formula (t : Term) (i j : ℕ) : Formula :=
  .and (.eqZero (.var j)) (.and (nonnegative (.var i))
    (.or (.and (nonnegative t) (.eqZero (difference (.mul (.var i) (.var i)) t)))
      (.and (nonnegative (.mul (.const (-1)) t)) (.eqZero (.var i)))))

theorem holds (t : Term) (i j : ℕ) (env : ℕ → ℝ) :
    (formula t i j).Holds env ↔
      env j=0 ∧ 0≤env i ∧ (0≤t.eval env ∧ env i^2=t.eval env ∨ t.eval env≤0 ∧ env i=0) := by
  simp only [formula,nonnegative,difference,Formula.Holds,Term.eval,Int.cast_neg,Int.cast_one,
    not_lt,neg_one_mul,neg_nonneg,← sub_eq_add_neg,sub_eq_zero,pow_two]

theorem sqrt_iff (a u v : ℝ) :
    (v=0 ∧ 0≤u ∧ (0≤a ∧ u^2=a ∨ a≤0 ∧ u=0)) ↔
      u=Real.sqrt (max a 0) ∧ v=0 := by
  constructor
  · rintro ⟨HV,HU,HA | HA⟩
    · rw [max_eq_left HA.1]
      refine ⟨?_,HV⟩
      nlinarith [Real.sq_sqrt HA.1,Real.sqrt_nonneg a]
    · rw [max_eq_right HA.1,Real.sqrt_zero]
      exact ⟨HA.2,HV⟩
  · rintro ⟨rfl,rfl⟩
    refine ⟨rfl,Real.sqrt_nonneg _,?_⟩
    by_cases HA : 0≤a
    · exact Or.inl ⟨HA,by rw [max_eq_left HA,Real.sq_sqrt HA]⟩
    · have HN : a≤0 := le_of_lt (lt_of_not_ge HA)
      exact Or.inr ⟨HN,by rw [max_eq_right HN,Real.sqrt_zero]⟩

theorem holds_iff (t : Term) (i j : ℕ) (env : ℕ → ℝ) :
    (formula t i j).Holds env ↔ env i=Real.sqrt (max (t.eval env) 0) ∧ env j=0 :=
  (holds t i j env).trans (sqrt_iff _ _ _)

theorem canonical_coordinates (a : ℝ) :
    WeakBooleanWitness.canonical a 0=Real.sqrt (max a 0) ∧ WeakBooleanWitness.canonical a 1=0 := by
  simp [WeakBooleanWitness.canonical,unit]

theorem plane_iff (a : ℝ) (w : Plane) :
    (w 0=Real.sqrt (max a 0) ∧ w 1=0) ↔ w=WeakBooleanWitness.canonical a := by
  constructor
  · rintro ⟨H0,H1⟩
    ext j
    fin_cases j
    · exact H0.trans (canonical_coordinates a).1.symm
    · exact H1.trans (canonical_coordinates a).2.symm
  · rintro rfl
    exact canonical_coordinates a

theorem arity (t : Term) (i j : ℕ) : (formula t i j).arity=max t.arity (max (i+1) (j+1)) := by
  simp only [formula,nonnegative,difference,Formula.arity,Term.arity]
  omega

end LeanCanny.Geometry.WeakCircleCanonicalFormula
