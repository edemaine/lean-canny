/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.AffineShiftCoordinates
public import LeanCanny.Connectivity.IntegerGridArcs

/-! # Complete original arcs while affine heights vary

An integer affine system with positive degree bounds and infinity exclusion
has complete finite anchored arcs after removing a constructed finite set of
parameter values. The constant shifts may be polynomial in that parameter.
All endpoints solve the original shifted equations. Finite roots may be
singular or repeated. No properness or value-annihilator certificate is an
additional input. Native recursive branch records and their size bounds are
not asserted here.
-/

@[expose] public section
namespace LeanCanny.Connectivity.AffineShiftArcs
open Set Geometry LeanCanny.Algebra
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

abbrev Fiber (p : Fin n → MvPolynomial (Fin n) ℤ) (c : Fin n → Polynomial ℤ) (t : ℝ) :=
  PolynomialGridArcs.Fiber (AffineShiftCoordinates.rows p c) t

/-- The actual integer factor used to partition the parameter line. -/
noncomputable def exceptional (p : Fin n → MvPolynomial (Fin n) ℤ)
    (c : Fin n → Polynomial ℤ) (d : Fin n → ℕ) : Polynomial ℤ :=
  IntegerGridArcs.exceptional (AffineShiftCoordinates.coordinate p c d)
    (AffineConstantParameterShift.system p c)

lemma exceptional_ne_zero (p : Fin n → MvPolynomial (Fin n) ℤ)
    (c : Fin n → Polynomial ℤ) (d : Fin n → ℕ)
    (hd : ∀ i, 0 < d i) (hp : AffineFiniteCoordinates.NoInfinity p d) : exceptional p c d ≠ 0 :=
  IntegerGridArcs.exceptional_ne_zero _ _ (AffineShiftCoordinates.coordinate_degree_pos p c d hd hp)

lemma finite_exceptional (p : Fin n → MvPolynomial (Fin n) ℤ)
    (c : Fin n → Polynomial ℤ) (d : Fin n → ℕ)
    (hd : ∀ i, 0 < d i) (hp : AffineFiniteCoordinates.NoInfinity p d) :
    {t : ℝ | SymbolicScaledSquarefree.scalarEvaluation t (exceptional p c d) = 0}.Finite :=
  IntegerGridArcs.finite_exceptional _ _ (AffineShiftCoordinates.coordinate_degree_pos p c d hd hp)

/-- Original row coefficients and complete coordinate coefficients bound the
explicit exceptional polynomial; no algebraicity witness is chosen here. -/
lemma exceptional_degree_le (p : Fin n → MvPolynomial (Fin n) ℤ)
    (c : Fin n → Polynomial ℤ) (d : Fin n → ℕ) (E : ℕ)
    (hc : ∀ i, (c i).natDegree ≤ E) :
    (exceptional p c d).natDegree ≤
      (∑ i, (2 * (AffineShiftCoordinates.coordinate p c d i).natDegree + 1) *
        (AffineRingCoordinates.dimension d * E + E)) +
      ∑ k, ProjectiveValueGram.dimension n (IntegerGridValueCertificate.width
        (AffineShiftCoordinates.coordinate p c d) (AffineConstantParameterShift.system p c k)) *
        (AffineRingCoordinates.dimension d * E + E) := by
  apply IntegerGridArcs.exceptional_degree_le
  · intro i k
    exact (AffineShiftCoordinates.coordinate_parameter_degree_le p c d E hc i k).trans (Nat.le_add_right _ _)
  · intro k u
    exact ((AffineConstantParameterShift.parameter_degree_le p c k u).trans (hc k)).trans
      (Nat.le_add_left _ _)

/-- Every actual root in one original fiber labels exactly one complete arc.
Original roots at exceptional endpoints remain valid without a Jacobian test. -/
theorem anchored_arcs (p : Fin n → MvPolynomial (Fin n) ℤ)
    (c : Fin n → Polynomial ℤ) (d : Fin n → ℕ)
    (hdeg : ∀ i, (p i).totalDegree ≤ d i) (hd : ∀ i, 0 < d i)
    (hp : AffineFiniteCoordinates.NoInfinity p d)
    (a b : ℝ) (t₀ : Ioo a b)
    (havoid : ∀ t ∈ Ioo a b, SymbolicScaledSquarefree.scalarEvaluation t (exceptional p c d) ≠ 0) :
      Finite (Fiber p c t₀.val) ∧
      ∃ curve : Fiber p c t₀.val → ℝ → Fin n → ℝ,
        (∀ j, curve j t₀.val = j.val) ∧
        (∀ j, ContinuousOn (curve j) (Icc a b)) ∧
        (∀ j t, t ∈ Icc a b → ∀ i, (p i).eval₂ (Int.castRingHom ℝ) (curve j t) =
          SymbolicScaledSquarefree.scalarEvaluation t (c i)) ∧
        (∀ t : Ioo a b, ∀ x,
          (∀ i, (p i).eval₂ (Int.castRingHom ℝ) x =
            SymbolicScaledSquarefree.scalarEvaluation t.val (c i)) ↔ ∃! j, curve j t.val = x) ∧
        ∀ j, FrontierCover.Accessible ((fun t => (t, curve j t)) '' Ioo a b) := by
  obtain ⟨hfinite, curve, hanchor, hcont, hroot, hcomplete, haccess⟩ := IntegerGridArcs.anchored_arcs
    (AffineShiftCoordinates.coordinate p c d) (AffineConstantParameterShift.system p c)
    (AffineShiftCoordinates.coordinate_degree_pos p c d hd hp) (AffineShiftCoordinates.proper p c d hd hp)
    (AffineShiftCoordinates.capture p c d hdeg) a b t₀ havoid
  refine ⟨hfinite, curve, hanchor, hcont, ?_, ?_, haccess⟩
  · intro j t ht
    exact (AffineShiftCoordinates.roots_iff p c t _).mp (hroot j t ht)
  · intro t x
    exact (AffineShiftCoordinates.roots_iff p c t.val x).symm.trans (hcomplete t x)

/-- Every actual root in one original fiber labels exactly one complete arc.
Original roots at exceptional endpoints remain valid without a Jacobian test. -/
theorem exists_anchored_arcs (p : Fin n → MvPolynomial (Fin n) ℤ)
    (c : Fin n → Polynomial ℤ) (d : Fin n → ℕ)
    (hdeg : ∀ i, (p i).totalDegree ≤ d i) (hd : ∀ i, 0 < d i)
    (hp : AffineFiniteCoordinates.NoInfinity p d) :
    ∃ bad : Set ℝ, bad.Finite ∧ ∀ (a b : ℝ) (t₀ : Ioo a b),
      (∀ t ∈ Ioo a b, t ∉ bad) →
      Finite (Fiber p c t₀.val) ∧
      ∃ curve : Fiber p c t₀.val → ℝ → Fin n → ℝ,
        (∀ j, curve j t₀.val = j.val) ∧
        (∀ j, ContinuousOn (curve j) (Icc a b)) ∧
        (∀ j t, t ∈ Icc a b → ∀ i, (p i).eval₂ (Int.castRingHom ℝ) (curve j t) =
          SymbolicScaledSquarefree.scalarEvaluation t (c i)) ∧
        (∀ t : Ioo a b, ∀ x,
          (∀ i, (p i).eval₂ (Int.castRingHom ℝ) x =
            SymbolicScaledSquarefree.scalarEvaluation t.val (c i)) ↔ ∃! j, curve j t.val = x) ∧
        ∀ j, FrontierCover.Accessible ((fun t => (t, curve j t)) '' Ioo a b) := by
  refine ⟨{t | SymbolicScaledSquarefree.scalarEvaluation t (exceptional p c d) = 0},
    finite_exceptional p c d hd hp, ?_⟩
  intro a b t₀ havoid
  exact anchored_arcs p c d hdeg hd hp a b t₀ havoid

end LeanCanny.Connectivity.AffineShiftArcs
