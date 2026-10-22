/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.CoercivePreparationControls
public import LeanCanny.ETR.CoerciveNativeSampling
public import LeanCanny.Algebra.SymbolicFixedTableFiniteSigns
public import LeanCanny.Algebra.SymbolicFixedTableCoordinateBounds

/-! # Encoded ETR as eventual sign filtering at one prepared primitive root

The original compiled equation, its source bounds, canonical coordinate
annihilants, and actual integer-prepared table are all constructed internally.
This module proves the semantic reduction. Native coefficient evaluation of
the prepared parameter and its rational-coordinate sign queries is separate.
-/

@[expose] public section
namespace LeanCanny.ETR.CoerciveSymbolicSampling
open LeanCanny.Algebra CoerciveSourceSampling CoercivePreparationControls
open Polynomial SymbolicScaledSquarefree
open scoped Classical Topology
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] RationalSubstitutionBits.compiledTerm Matrix.det Macaulay.fullMatrix

abbrev Query (bits : List Bool) := Sum (Fin (dimension bits)) Bool

noncomputable def integerQuery (bits : List Bool) : Query bits → MvPolynomial (Fin (dimension bits + 1)) ℤ
  | .inl i => CoerciveQuerySystem.gradient (CoerciveSourceSampling.polynomial bits) (degreeAllowance bits) i
  | .inr false => CoerciveQuerySystem.bound (degreeAllowance bits) (penaltyExponent bits)
  | .inr true => CoerciveQuerySystem.residual (CoerciveSourceSampling.polynomial bits) (penaltyExponent bits)

noncomputable def query (bits : List Bool) (j : Query bits) : MvPolynomial (Fin (dimension bits + 1)) Coefficient :=
  (integerQuery bits j).map (Int.castRingHom Coefficient)

def accepts (bits : List Bool) (sgn : Query bits → SignType) : Prop :=
  (∀ i, sgn (.inl i) = 0) ∧ sgn (.inr false) ≤ 0 ∧ sgn (.inr true) ≤ 0

noncomputable def allowance (bits : List Bool) : ℕ := 2 * degreeAllowance bits + 2

theorem integerQuery_degree (bits : List Bool) (j : Query bits) :
    (integerQuery bits j).totalDegree ≤ allowance bits := by
  rcases j with i | b
  · exact CoerciveQuerySystem.gradient_degree _ _ (polynomial_degree bits) i
  · cases b
    · exact CoerciveQuerySystem.bound_degree _ _
    · exact CoerciveQuerySystem.residual_degree _ _ _ (polynomial_degree bits)

theorem query_degree (bits : List Bool) (j : Query bits) (i : Fin (dimension bits + 1)) :
    (query bits j).degreeOf i ≤ allowance bits :=
  (MvPolynomial.degreeOf_le_totalDegree _ _).trans
    ((PolynomialMapDegree.degree_le _ _).trans (integerQuery_degree bits j))

theorem eval_query (bits : List Bool) (j : Query bits) (s : ℝ) (y : Fin (dimension bits + 1) → ℝ) :
    (query bits j).eval₂ (scalarEvaluation s) y = (integerQuery bits j).eval₂ (Int.castRingHom ℝ) y := by
  rw [query, MvPolynomial.eval₂_map]
  have he : (scalarEvaluation s).comp (Int.castRingHom Coefficient) = Int.castRingHom ℝ := Subsingleton.elim _ _
  rw [he]

theorem accepts_iff (bits : List Bool) (s : ℝ) (y : Fin (dimension bits + 1) → ℝ) :
    accepts bits (fun j => SignType.sign ((query bits j).eval₂ (scalarEvaluation s) y)) ↔
      CoerciveNativeSampling.Satisfies bits y := by
  simp only [accepts, eval_query, integerQuery, sign_eq_zero_iff, sign_nonpos_iff,
    CoerciveNativeSampling.Satisfies]

noncomputable def clearedQuery (bits : List Bool) (j : Query bits) : Polynomial Coefficient :=
  (family bits).signQueryWith (fun _ => allowance bits) (query bits j)

def Realizes (bits : List Bool) (s : ℝ) : Prop :=
  ∃ theta : ℝ, (family bits).parameter.eval₂ (scalarEvaluation s) theta = 0 ∧
    accepts bits (fun j => SignType.sign ((clearedQuery bits j).eval₂ (scalarEvaluation s) theta))

theorem realizes_iff (bits : List Bool) (s : ℝ) (hs : 0 < s)
    (hsmall : s ≤ InfinitesimalSign.dyadic (referenceExponent bits)) :
    (∃ x, Sample bits s x) ↔ Realizes bits s := by
  have h := (family bits).predicate_realizable_iff (fun _ => allowance bits) (query bits)
    (query_degree bits) (accepts bits) s hs hsmall
  constructor
  · intro hx
    obtain ⟨y, hy, hq⟩ := (CoerciveNativeSampling.exists_sample_iff_root_product bits s).mp hx
    exact h.mp ⟨y, hy, (accepts_iff bits s y).mpr hq⟩
  · intro hx
    obtain ⟨y, hy, hq⟩ := h.mpr hx
    exact (CoerciveNativeSampling.exists_sample_iff_root_product bits s).mpr
      ⟨y, hy, (accepts_iff bits s y).mp hq⟩

def EventuallyRealizes (bits : List Bool) : Prop :=
  ∃ delta : ℝ, 0 < delta ∧ ∀ s : ℝ, 0 < s → s < delta → Realizes bits s

/-- The final semantic target for native eventual-root sign evaluation. -/
theorem correct (bits : List Bool) : bits ∈ ETR.language ↔ EventuallyRealizes bits := by
  rw [CoerciveSourceSampling.correct]
  constructor
  · rintro ⟨delta, hd, h⟩
    refine ⟨min delta (InfinitesimalSign.dyadic (referenceExponent bits)),
      lt_min hd (InfinitesimalSign.dyadic_pos _), ?_⟩
    intro s hs hdelta
    exact (realizes_iff bits s hs (hdelta.le.trans (min_le_right _ _))).mp
      (h s hs (hdelta.trans_le (min_le_left _ _)))
  · rintro ⟨delta, hd, h⟩
    refine ⟨min delta (InfinitesimalSign.dyadic (referenceExponent bits)),
      lt_min hd (InfinitesimalSign.dyadic_pos _), ?_⟩
    intro s hs hdelta
    exact (realizes_iff bits s hs (hdelta.le.trans (min_le_right _ _))).mpr
      (h s hs (hdelta.trans_le (min_le_left _ _)))

theorem parameter_ne_zero (bits : List Bool) : (family bits).parameter ≠ 0 :=
  (family bits).parameter_ne_zero

end LeanCanny.ETR.CoerciveSymbolicSampling
