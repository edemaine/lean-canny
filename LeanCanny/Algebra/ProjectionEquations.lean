/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PartialDerivativeDegree
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Data.Fintype.Card
import Lean.Elab.Tactic.Omega

/-! # Polynomial equations for critical linear projections of a hypersurface

Point and direction variables are separate blocks. The system consists of p
and the equations partial_i(p) - v_i * partial_base(p). A direction normalized
to v_base = 1 gives the hypersurface projection equations used by Canny.
-/

@[expose] public section

namespace LeanCanny.Algebra.ProjectionEquations
open MvPolynomial

variable {ι R : Type*} [CommRing R]

abbrev Variable (ι : Type*) := Sum ι ι

noncomputable def polynomial (p : MvPolynomial ι R) (base : ι) : Option ι → MvPolynomial (Variable ι) R
  | none => rename Sum.inl p
  | some i => rename Sum.inl (pderiv i p) - X (.inr i) * rename Sum.inl (pderiv base p)

section Evaluation
variable {S : Type*} [CommRing S]

theorem eval_level (p : MvPolynomial ι R) (base : ι) (φ : R →+* S) (x v : ι → S) :
    (polynomial p base none).eval₂ φ (Sum.elim x v) = p.eval₂ φ x := by
  rw [polynomial, eval₂_rename]
  rfl

theorem eval_partial (p : MvPolynomial ι R) (base i : ι) (φ : R →+* S) (x v : ι → S) :
    (polynomial p base (some i)).eval₂ φ (Sum.elim x v) =
      (pderiv i p).eval₂ φ x - v i * (pderiv base p).eval₂ φ x := by
  simp only [polynomial, eval₂_sub, eval₂_mul, eval₂_X, eval₂_rename, Sum.elim_inr]
  rfl

theorem equations_iff (p : MvPolynomial ι R) (base : ι) (φ : R →+* S) (x v : ι → S) :
    (∀ j, (polynomial p base j).eval₂ φ (Sum.elim x v) = 0) ↔ p.eval₂ φ x = 0 ∧
      ∀ i, (pderiv i p).eval₂ φ x - v i * (pderiv base p).eval₂ φ x = 0 := by
  constructor
  · intro h
    exact ⟨(eval_level p base φ x v).symm.trans (h none),
      fun i => (eval_partial p base i φ x v).symm.trans (h (some i))⟩
  · rintro ⟨hp, hg⟩ j
    cases j with
    | none => exact (eval_level p base φ x v).trans hp
    | some i => exact (eval_partial p base i φ x v).trans (hg i)

end Evaluation

theorem degree_le [Nontrivial R] (p : MvPolynomial ι R) (base : ι) (j : Option ι) :
    (polynomial p base j).totalDegree ≤ max p.totalDegree 1 := by
  cases j with
  | none => exact (totalDegree_rename_le _ _).trans (le_max_left _ _)
  | some i =>
    have hi := PartialDerivativeDegree.degree_le p i
    have hb := PartialDerivativeDegree.degree_le p base
    have hri := totalDegree_rename_le (Sum.inl : ι → Variable ι) (pderiv i p)
    have hrb := totalDegree_rename_le (Sum.inl : ι → Variable ι) (pderiv base p)
    have hm := totalDegree_mul (X (.inr i) : MvPolynomial (Variable ι) R) (rename Sum.inl (pderiv base p))
    have hs := totalDegree_sub (rename Sum.inl (pderiv i p))
      ((X (.inr i) : MvPolynomial (Variable ι) R) * rename Sum.inl (pderiv base p))
    simp only [totalDegree_X] at hm
    change (rename Sum.inl (pderiv i p) - (X (.inr i) : MvPolynomial (Variable ι) R) *
      rename Sum.inl (pderiv base p)).totalDegree ≤ _
    omega

abbrev Index (base : ι) := Option {i : ι // i ≠ base}

noncomputable def system (p : MvPolynomial ι R) (base : ι) (j : Index base) : MvPolynomial (Variable ι) R :=
  polynomial p base (j.map Subtype.val)

theorem system_degree_le [Nontrivial R] (p : MvPolynomial ι R) (base : ι) (j : Index base) :
    (system p base j).totalDegree ≤ max p.totalDegree 1 := degree_le p base _

theorem system_card [Fintype ι] [DecidableEq ι] (base : ι) : Fintype.card (Index base) = Fintype.card ι := by
  simp only [Index, Fintype.card_option, Fintype.card_subtype_compl, Fintype.card_unique]
  have hp : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨base⟩
  omega

end LeanCanny.Algebra.ProjectionEquations
