import LeanCanny.Connectivity.AffineShiftSlab

/-! A varying height with a repeated endpoint root. Run with
`lake env lean -DwarningAsError=true scripts/CheckAffineShiftArcs.lean`.
-/

open LeanCanny LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Connectivity
open MvPolynomial Set
open scoped Classical

namespace AffineShiftArcRegression
private noncomputable def square : Fin 1 → MvPolynomial (Fin 1) ℤ := fun _ => X 0 ^ 2
private noncomputable def shift : Fin 1 → Polynomial ℤ := fun _ => Polynomial.X
private def degree : Fin 1 → ℕ := fun _ => 2

private lemma bounded (i : Fin 1) : (square i).totalDegree ≤ degree i := by
  simp [square, degree]

private lemma positive (i : Fin 1) : 0 < degree i := by
  change 0 < 2
  decide

private lemma noInfinity : AffineFiniteCoordinates.NoInfinity square degree := by
  intro y hy hz
  have h := hz 0
  simp only [square, degree, WeightedHomogenization.homogenize_X_pow,
    eval₂_pow, eval₂_X, pow_eq_zero_iff (by decide : 2 ≠ 0)] at h
  funext j
  cases j with
  | none => exact hy
  | some i =>
    have hi : i = 0 := Subsingleton.elim _ _
    simpa only [hi, Pi.zero_apply] using h

-- The zero-parameter equations are exactly the original repeated equation.
example (i : Fin 1) :
    (AffineConstantParameterShift.system square shift i).map (Polynomial.evalRingHom (0 : ℤ)) =
      square i := by
  apply AffineConstantParameterShift.at_zero
  intro j
  simp [shift]

-- The shifted family is exactly x^2 = t, with no auxiliary roots asserted.
example (t : ℝ) (x : Fin 1 → ℝ) :
    PolynomialGridValues.value (AffineShiftCoordinates.rows square shift) (t, x) = 0 ↔
      x 0 ^ 2 = t := by
  rw [AffineShiftCoordinates.roots_iff]
  simp only [square, shift, eval₂_pow, eval₂_X,
    SymbolicScaledSquarefree.scalarEvaluation, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
  simp

-- Every real parameter has a nonzero complete coordinate equation.
example (i : Fin 1) (t : ℝ) :
    0 < SymbolicScaledSquarefree.scalarEvaluation t
      (AffineShiftCoordinates.coordinate square shift degree i).leadingCoeff :=
  AffineShiftCoordinates.positive_leading square shift degree positive noInfinity i t


-- Linear parameter shifts keep every coordinate-certificate coefficient bounded
-- by the fixed determinant dimension, independently of its reciprocal degree.
example (i : Fin 1) (k : ℕ) :
    ((AffineShiftCoordinates.coordinate square shift degree i).coeff k).natDegree ≤
      AffineRingCoordinates.dimension degree := by
  have h := AffineShiftCoordinates.coordinate_parameter_degree_le square shift degree 1
    (fun _ => by simp [shift]) i k
  simpa only [Nat.mul_one] using h

-- Compact parameter sets have compact coordinate-grid preimages.
example : IsProperMap (RootProjection.projection
    (SquarefreeRootFamily.value (AffineShiftCoordinates.coordinate square shift degree))) :=
  AffineShiftCoordinates.proper square shift degree positive noInfinity

-- Every retained arc satisfies x^2 = t at both endpoints as well as inside.
example : ∃ bad : Set ℝ, bad.Finite ∧ ∀ (a b : ℝ) (t₀ : Ioo a b),
    (∀ t ∈ Ioo a b, t ∉ bad) →
    ∃ curve : AffineShiftArcs.Fiber square shift t₀.val → ℝ → Fin 1 → ℝ,
      ∀ j t, t ∈ Icc a b → curve j t 0 ^ 2 = t := by
  obtain ⟨bad, hbad, h⟩ := AffineShiftArcs.exists_anchored_arcs square shift degree
    bounded positive noInfinity
  refine ⟨bad, hbad, ?_⟩
  intro a b t₀ havoid
  obtain ⟨_, curve, _, _, hroot, _, _⟩ := h a b t₀ havoid
  refine ⟨curve, ?_⟩
  intro j t ht
  simpa [square, shift, SymbolicScaledSquarefree.scalarEvaluation] using hroot j t ht 0

-- The actual exceptional factor is nonzero, not an unspecified finite set.
example : AffineShiftArcs.exceptional square shift degree ≠ 0 :=
  AffineShiftArcs.exceptional_ne_zero square shift degree positive noInfinity

example (a b : ℝ) (t₀ : Ioo a b)
    (havoid : ∀ t ∈ Ioo a b, SymbolicScaledSquarefree.scalarEvaluation t
      (AffineShiftArcs.exceptional square shift degree) ≠ 0) :
    ∃ curve : AffineShiftArcs.Fiber square shift t₀.val → ℝ → Fin 1 → ℝ,
      ∀ j t, t ∈ Icc a b → curve j t 0 ^ 2 = t := by
  obtain ⟨_, curve, _, _, hroot, _, _⟩ := AffineShiftArcs.anchored_arcs square shift degree
    bounded positive noInfinity a b t₀ havoid
  refine ⟨curve, ?_⟩
  intro j t ht
  simpa [square, shift, SymbolicScaledSquarefree.scalarEvaluation] using hroot j t ht 0

-- The original equation has a vanishing derivative at the exceptional endpoint.
example : (pderiv (0 : Fin 1) (square 0)).eval₂ (Int.castRingHom ℝ) (fun _ => 0) = 0 := by
  simp [square]

-- The singular zero fiber and every other original fiber are finite.
example (t : ℝ) : Finite (AffineShiftArcs.Fiber square shift t) :=
  (AffineShiftCoordinates.finite_fiber square shift degree bounded positive noInfinity t).to_subtype

-- The full graph theorem needs no supplied endpoint covers or finite-root oracle.
example (a b : ℝ) (t₀ : Ioo a b)
    (havoid : ∀ t ∈ Ioo a b, SymbolicScaledSquarefree.scalarEvaluation t
      (AffineShiftArcs.exceptional square shift degree) ≠ 0) :
    Finite (FiniteFiberSlab.Index (AffineShiftSlab.equation square shift)
      (AffineShiftArcs.Fiber square shift t₀.val) a b) :=
  (AffineShiftSlab.exists_graph square shift degree bounded positive noInfinity a b t₀ havoid).1

-- Empty affine systems and coordinate grids are also covered.
example : AffineFiniteCoordinates.NoInfinity (fun i : Fin 0 => i.elim0) (fun i => i.elim0) := by
  intro y hy _
  funext j
  cases j with
  | none => exact hy
  | some i => exact i.elim0

end AffineShiftArcRegression
