import LeanCanny.Connectivity.SquarefreeRootArcs
import LeanCanny.Connectivity.AlgebraicArcFilter
import LeanCanny.Connectivity.PolynomialGridArcs
import LeanCanny.Geometry.PolynomialCoordinateProper

/-! Boundary cases for repeated coordinate equations and anchor-fiber filtering.
Run with `lake env lean scripts/CheckAlgebraicArcs.lean`.
-/

open LeanCanny LeanCanny.Geometry LeanCanny.Connectivity Polynomial Set
open scoped Classical

-- Empty coordinate families still have an invertible spatial derivative.
example (Q : Fin 0 → Polynomial (Polynomial ℝ)) (t : ℝ) (x : Fin 0 → ℝ) :
    (fderiv ℝ (PolynomialRootFamily.value (UnivariateRootFamily.diagonal Q)) (t, x) ∘L
      ContinuousLinearMap.inr ℝ ℝ (Fin 0 → ℝ)).IsInvertible := by
  apply UnivariateRootFamily.regular_diagonal Q t x
  · intro i
    exact Fin.elim0 i
  · exact Subsingleton.elim _ _

namespace RepeatedCoordinateArcRegression
private noncomputable def p : Fin 2 → Polynomial (Polynomial ℤ) := fun _ => Polynomial.X ^ 2

private lemma zero_iff (t : ℝ) (x : Fin 2 → ℝ) :
    SquarefreeRootFamily.value p (t, x) = 0 ↔ x = 0 := by
  constructor
  · intro hx
    funext i
    have H := congrFun hx i
    rw [SquarefreeRootFamily.value_apply] at H
    simpa only [p, Polynomial.eval₂_pow, Polynomial.eval₂_X, Pi.zero_apply,
      pow_eq_zero_iff (by decide : 2 ≠ 0)] using H
  · rintro rfl
    funext i
    simp [SquarefreeRootFamily.value_apply, p]

-- Both original equations have zero spatial derivative at their common root.
example (t : ℝ) (i j : Fin 2) :
    (MvPolynomial.pderiv j (SquarefreeRootFamily.rows p i)).eval₂
      (Polynomial.evalRingHom t) (fun _ => 0) = 0 := by
  simp [SquarefreeRootFamily.rows, UnivariateRootFamily.diagonal,
    SquarefreeRootFamily.realPolynomial, p]

private lemma proper_original :
    IsProperMap (RootProjection.projection (SquarefreeRootFamily.value p)) := by
  apply RootProjection.isProperMap_of_compact_bound _ (SquarefreeRootFamily.continuous_value p)
    (K := {0}) isCompact_singleton
  intro z
  exact (zero_iff z.val.1 z.val.2).mp z.property

-- Complete two-coordinate branches retain the repeated original endpoint root.
example (havoid : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ i,
    LeanCanny.Algebra.SymbolicScaledSquarefree.scalarEvaluation t
      (LeanCanny.Algebra.SymbolicScaledSquarefree.exceptional (p i)) ≠ 0) :
    ∃ curve : RootBranches.Index (SquarefreeRootFamily.value
        (fun i => LeanCanny.Algebra.SymbolicScaledSquarefree.polynomial (p i)))
        0 1 ⟨(1 : ℝ) / 2, by norm_num⟩ → ℝ → Fin 2 → ℝ,
      ∀ j, curve j 0 = 0 ∧ curve j 1 = 0 := by
  obtain ⟨_, curve, _, _, hroot, _, _⟩ := SquarefreeRootArcs.exists_anchored_arcs p
    (fun _ => by simp [p]) 0 1 ⟨(1 : ℝ) / 2, by norm_num⟩ proper_original havoid
  exact ⟨curve, fun j => ⟨(zero_iff 0 _).mp (hroot j 0 (by norm_num)),
    (zero_iff 1 _).mp (hroot j 1 (by norm_num))⟩⟩

-- A nonzero constant equation excludes every root; its exceptional set is empty.
example (t : ℝ) (x : Fin 2 → ℝ) :
    SquarefreeRootFamily.value (fun _ : Fin 2 => (1 : Polynomial (Polynomial ℤ))) (t, x) ≠ 0 := by
  intro h
  have H := congrFun h 0
  norm_num [SquarefreeRootFamily.value_apply] at H

end RepeatedCoordinateArcRegression

namespace AlgebraicArcFilterRegression
private noncomputable def annihilator : Polynomial (Polynomial ℝ) :=
  Polynomial.X * (Polynomial.X - 1)

private lemma trailing : annihilator.trailingCoeff = -1 := by
  rw [annihilator, Polynomial.trailingCoeff_mul,
    Polynomial.trailingCoeff_eq_coeff_zero (p := (Polynomial.X - 1 : Polynomial (Polynomial ℝ))) (by simp)]
  simp [Polynomial.trailingCoeff, Polynomial.natTrailingDegree_X]

-- A continuous algebraic test taking values in {0,1} cannot switch between them.
example (f : ℝ → ℝ) (hf : Continuous f) (h : ∀ t, f t * (f t - 1) = 0) (s t : ℝ) :
    f s = 0 ↔ f t = 0 := by
  apply AlgebraicBranchZero.zero_iff annihilator id f continuous_id hf
  · intro t
    simpa [annihilator] using h t
  · intro t
    simp [trailing]

private noncomputable def original (z : ℝ × ℝ) : Fin 1 → ℝ := fun _ => z.2
private noncomputable def curve (j : Bool) (_ : ℝ) : ℝ := if j then 1 else 0

-- The grid has an extra constant-one branch, rejected at the anchor.
example : original ((1 : ℝ) / 2, curve true ((1 : ℝ) / 2)) ≠ 0 := by
  intro h
  have H := congrFun h 0
  norm_num [original, curve] at H

-- Filtering at the anchor covers exactly the original roots and keeps endpoints.
example : ∀ (j : AlgebraicArcFilter.Label original curve ((1 : ℝ) / 2)) t,
    t ∈ Icc (0 : ℝ) 1 → original (t, curve j.val t) = 0 := by
  have hc (j : Bool) : ContinuousOn (curve j) (Icc (0 : ℝ) 1) := continuous_const.continuousOn
  have hcomplete (t : Ioo (0 : ℝ) 1) (x : ℝ) (hx : original (t.val, x) = 0) :
      ∃! j, curve j t.val = x := by
    have hx0 : x = 0 := congrFun hx 0
    refine ⟨false, by simp [curve, hx0], ?_⟩
    intro j hj
    cases j
    · rfl
    · norm_num [curve, hx0] at hj
  have hrel (j : Bool) (k : Fin 1) (t : ℝ) (_ : t ∈ Ioo (0 : ℝ) 1) :
      annihilator.eval₂ (Polynomial.evalRingHom t) (original (t, curve j t) k) = 0 := by
    cases j <;> simp [annihilator, original, curve]
  exact (AlgebraicArcFilter.filtered_arcs original
    (continuous_pi (fun _ => continuous_snd)) 0 1 ⟨(1 : ℝ) / 2, by norm_num⟩ curve hc
    hcomplete (fun _ => annihilator) hrel (fun _ _ _ => by simp [trailing])).2.1

end AlgebraicArcFilterRegression

namespace ConstructedGridArcRegression
private noncomputable def p : Fin 1 → Polynomial (Polynomial ℤ) :=
  fun _ => (Polynomial.X * (Polynomial.X - Polynomial.C 1)) ^ 2
private noncomputable def q : Fin 1 → MvPolynomial (Fin 1) (Polynomial ℝ) :=
  fun _ => MvPolynomial.X 0

private lemma monic (i : Fin 1) : (p i).Monic :=
  (Polynomial.monic_X.mul (Polynomial.monic_X_sub_C 1)).pow 2

private lemma original_zero (t : ℝ) (x : Fin 1 → ℝ) :
    PolynomialGridValues.value q (t, x) = 0 ↔ x 0 = 0 := by
  simp only [PolynomialGridValues.value, q, MvPolynomial.eval₂_X,
    funext_iff, Pi.zero_apply]
  simp

-- The grid has two repeated roots, but only zero satisfies the original test.
-- Properness and the value annihilators are constructed, with no certificate inputs.
example : ∃ bad : Set ℝ, bad.Finite ∧ ∀ (a b : ℝ) (t₀ : Ioo a b),
    (∀ t ∈ Ioo a b, t ∉ bad) →
    ∃ curve : PolynomialGridArcs.Fiber q t₀.val → ℝ → Fin 1 → ℝ,
      (∀ j t, t ∈ Icc a b → curve j t 0 = 0) ∧
      ∀ t : Ioo a b, ∀ x, x 0 = 0 ↔ ∃! j, curve j t.val = x := by
  have hproper : IsProperMap (RootProjection.projection (SquarefreeRootFamily.value p)) := by
    apply PolynomialCoordinateProper.proper_of_monic
    intro i
    exact (monic i).map _
  have hcapture (t : ℝ) (x : Fin 1 → ℝ)
      (hx : PolynomialGridValues.value q (t, x) = 0) : SquarefreeRootFamily.value p (t, x) = 0 := by
    have hx0 := (original_zero t x).mp hx
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    simp only [SquarefreeRootFamily.value_apply, p, Polynomial.eval₂_pow,
      Polynomial.eval₂_mul, Polynomial.eval₂_sub, Polynomial.eval₂_X,
      Polynomial.eval₂_C, hi, hx0, zero_mul, zero_pow (by decide : 2 ≠ 0), Pi.zero_apply]
  obtain ⟨bad, hbad, h⟩ := PolynomialGridArcs.exists_anchored_arcs p
    (fun i => (monic i).ne_zero) q hproper hcapture
  refine ⟨bad, hbad, ?_⟩
  intro a b t₀ havoid
  obtain ⟨_, curve, _, _, hroot, hcomplete, _⟩ := h a b t₀ havoid
  refine ⟨curve, fun j t ht => (original_zero t _).mp (hroot j t ht), ?_⟩
  intro t x
  exact (original_zero t.val x).symm.trans (hcomplete t x)

end ConstructedGridArcRegression
