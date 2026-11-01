/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.WeakCircleCanonicalFormula
/-! # A literal closed polynomial graph of the nonnegative part -/
@[expose] public section
namespace LeanCanny.Geometry.PositivePartGraph
open LeanCanny.ETR LeanCanny.Connectivity
open WeakCircleCanonicalFormula

def condition (t : Term) (i : ℕ) : Formula :=
  .and (nonnegative (.var i)) (.and (nonnegative (difference (.var i) t))
    (.eqZero (.mul (.var i) (difference (.var i) t))))

theorem scalar_iff (a h : ℝ) : (0≤h ∧ 0≤h-a ∧ h*(h-a)=0) ↔ h=max a 0 := by
  constructor
  · rintro ⟨H0,H1,HE⟩
    rcases mul_eq_zero.mp HE with H | H
    · have HA : a≤0 := by linarith
      rw [max_eq_right HA]
      exact H
    · have HH : h=a := sub_eq_zero.mp H
      rw [max_eq_left (HH ▸ H0)]
      exact HH
  · rintro rfl
    refine ⟨le_max_right _ _,sub_nonneg.mpr (le_max_left _ _),?_⟩
    by_cases H : 0≤a
    · rw [max_eq_left H]
      ring
    · rw [max_eq_right (le_of_not_ge H)]
      ring

theorem holds_iff (t : Term) (i : ℕ) (env : ℕ → ℝ) :
    (condition t i).Holds env ↔ env i=max (t.eval env) 0 := by
  simp only [condition,nonnegative,difference,Formula.Holds,Term.eval,Int.cast_neg,Int.cast_one,
    not_lt,neg_one_mul,← sub_eq_add_neg]
  exact scalar_iff _ _

theorem arity (t : Term) (i : ℕ) : (condition t i).arity=max t.arity (i+1) := by
  simp only [condition,nonnegative,difference,Formula.arity,Term.arity]
  omega

abbrev Graph {X : Type*} (f : X → ℝ) := {z : X × ℝ // z.2=max (f z.1) 0}

noncomputable def homeomorph {X : Type*} [TopologicalSpace X] (f : X → ℝ) (hf : Continuous f) : Graph f ≃ₜ X where
  toFun z := z.val.1
  invFun x := ⟨(x,max (f x) 0),rfl⟩
  left_inv z := by apply Subtype.ext; exact Prod.ext rfl z.property.symm
  right_inv _ := rfl
  continuous_toFun := continuous_fst.comp continuous_subtype_val
  continuous_invFun := (continuous_id.prodMk (hf.max continuous_const)).subtype_mk _

end LeanCanny.Geometry.PositivePartGraph
