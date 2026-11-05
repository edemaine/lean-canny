/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialJointCoreReadback
public import LeanCanny.Connectivity.FormulaSignSlotCandidateRadialDescriptor
public import LeanCanny.Connectivity.FormulaSignSlotCircularPoint
/-! # Literal closed lifts and the same-center radial point in the joint source

This module binds the joint integer equations to actual geometric points.
Grid, cut avoidance, and selected component membership remain separate
receipts; a root of the core alone does not assert those conditions.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialJointGeometry
open LeanCanny.Computation LeanCanny.Connectivity LeanCanny.ETR LeanCanny.Geometry
open FormulaSignSlotRadialJointLayout FormulaSignSlotRadialJointCore
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotTiltedRadialGrid.Q
  FormulaSignSlotCenteredRadialLimits.polynomial FormulaSignSlotSource.dimension
  FormulaSignSlotMargin.initialPolynomial
  FormulaSignSlotCircularBoundedCover.root
  ClosedFormulaGateMetadata.dimension ClosedFormulaGateMetadata.count ClosedFormulaGateMetadata.atom
  ClosedFormulaGateMetadata.kind Input.field FormulaView.normalize

private theorem sum_range {α : Type*} [AddCommMonoid α] (n : ℕ) (f : ℕ → α) :
    ((List.range n).map f).sum = ∑ i : Fin n, f i.val := by
  have H : ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
    induction n with
    | zero => simp
    | succ n ih => simp [List.range_succ, Finset.sum_range_succ, ih]
  exact H.trans (Fin.sum_univ_eq_sum_range f n).symm

private theorem finite_eval (t : Term) (n : ℕ) (ht : t.arity ≤ n) (env : ℕ → ℝ) :
    (t.finitePolynomial n).eval₂ (Int.castRingHom ℝ) (fun i => env i.val) = t.eval env := by
  rw [Term.eval_finitePolynomial]
  apply Term.eval_congr
  intro i hi
  simp only [Formula.extend, dite_eq_left (hi.trans_le ht)]

private theorem sumSquares_eval (ts : List Term) (env : ℕ → ℝ) :
    (Term.sumSquares ts).eval env = (ts.map (fun t => (t.eval env)^2)).sum := by
  induction ts with
  | nil => simp [Term.sumSquares, Term.eval]
  | cons t ts ih => simp [Term.sumSquares, Term.square, Term.eval, ih, pow_two]

/-- The formal center and radius are evaluated at their literal appended slots. -/
theorem formal_eval (c : List Bool) (env : ℕ → ℝ) :
    (FormulaSignSlotRadialFormalInput.equation c).eval env =
      (FormulaSignSlotCenteredRadialLimits.polynomial c
        (fun i => env (FormulaSignSlotRadialFormalInput.spatial c + i.val))
        (env (FormulaSignSlotRadialFormalInput.spatial c + FormulaSignSlotSource.dimension c))).eval
        (fun i => env i.val) := by
  rw [FormulaSignSlotCenteredRadialLimits.polynomial]
  simp only [MvPolynomial.eval_add, MvPolynomial.eval_map, MvPolynomial.eval_sum,
    MvPolynomial.eval_pow, MvPolynomial.eval_sub, MvPolynomial.eval_X, MvPolynomial.eval_C]
  rw [finite_eval (FormulaSignSlotCenteredRadialSource.equation c)
    (FormulaSignSlotCenteredRadialGraph.N c + FormulaSignSlotCenteredRadialGraph.d c + 1)
    (FormulaSignSlotCenteredRadialSource.scope c) env]
  simp only [FormulaSignSlotRadialFormalInput.equation, Term.eval,
    FormulaSignSlotRadialFormalInput.centerSquares, SumSquares.eval_accumulate,
    FormulaSignSlotRadialFormalInput.centerTerms, sumSquares_eval, List.map_map, Function.comp_def,
    FormulaSignSlotRadialFormalInput.centerDifference, FormulaSignSlotRadialFormalInput.radiusDifference,
    FormulaSignSlotRadialFormalInput.difference, Term.square, Term.eval,
    Int.cast_zero, zero_add, Int.cast_neg, Int.cast_one, neg_one_mul, ← sub_eq_add_neg, ← pow_two]
  rw [sum_range]
  rfl

noncomputable def center (q : List Bool) (env : ℕ → ℝ) : Fin (centerCount q) → ℝ :=
  fun i => env (column 0 i.val)
noncomputable def spatialPoint (q : List Bool) (env : ℕ → ℝ) : Fin (spatialCount q) → ℝ :=
  fun i => env (column 2 i.val)
noncomputable def parameter (q : List Bool) (env : ℕ → ℝ) := env (radiusVariable q)

noncomputable def closedPoint (side : Bool) (q : List Bool) (env : ℕ → ℝ)
    (h : (equation q).eval env = 0) : FormulaSignSlotCircularBoundedCover.Source (source side q) := by
  refine ⟨fun i => env (column (if side then 1 else 0) i.val), ?_⟩
  change (CanonicalAuxiliaryCandidateCover.equation (source side q)).eval
    (Formula.extend (fun i => env (column (if side then 1 else 0) i.val))) = 0
  have HE := (CanonicalAuxiliaryCandidateCover.equation (source side q)).eval_congr
    (Formula.extend (fun i : Fin (circleCount side q) => env (column (if side then 1 else 0) i.val)))
    (fun i => env (column (if side then 1 else 0) i)) (by
      intro i hi
      have HI : i < circleCount side q := hi.trans_le (CanonicalAuxiliaryCandidateCover.equation_scope _)
      simp only [Formula.extend, dite_eq_left HI])
  apply HE.trans
  cases side
  · exact (FormulaSignSlotRadialJointCoreReadback.zero_iff q env).mp h |>.1
  · exact (FormulaSignSlotRadialJointCoreReadback.zero_iff q env).mp h |>.2.1

theorem radial_zero (q : List Bool) (env : ℕ → ℝ) (h : (equation q).eval env = 0) :
    (FormulaSignSlotTiltedRadialGrid.Q (source true q) (center q env) (parameter q env)).eval
      (spatialPoint q env) = 0 := by
  obtain ⟨_, _, HF, HC, _, _, _⟩ := (FormulaSignSlotRadialJointCoreReadback.zero_iff q env).mp h
  rw [formal_eval] at HF
  have HE : (fun i : Fin (centerCount q) => env (column 2 (spatialCount q + i.val))) = center q env := by
    funext i
    exact HC i.val i.isLt
  have HF' : (FormulaSignSlotCenteredRadialLimits.polynomial (source true q)
      (fun i : Fin (centerCount q) => env (column 2 (spatialCount q + i.val))) (parameter q env)).eval
      (fun i => env (column 2 i.val)) = 0 := HF
  have HV := congrArg (fun a => (FormulaSignSlotCenteredRadialLimits.polynomial
    (source true q) a (parameter q env)).eval (fun i => env (column 2 i.val))) HE
  unfold spatialPoint FormulaSignSlotTiltedRadialGrid.Q
  exact HV.symm.trans HF'

theorem positive_coordinate (c : List Bool) (y : FormulaSignSlotCircularBoundedCover.Source c)
    (i : Fin (FormulaSignSlotMargin.initialDimension c)) :
    (FormulaSignSlotCircularBoundedCover.positivePoint c y).val.val i =
      y.val (FormulaSignSlotCircularBoundedCover.originalIndex c (Fin.castAdd 2 i)) := by
  unfold FormulaSignSlotCircularBoundedCover.positivePoint
  rw [FormulaSignSlotCircularInterior.projection_coordinate,
    FormulaSignSlotCircularBoundedCover.projection_coordinate]

noncomputable def radialPoint (q : List Bool) (env : ℕ → ℝ) (h : (equation q).eval env = 0) :
    FormulaSignSlotTiltedRadialGrid.OldPositive (source true q) (center q env) (parameter q env) := by
  refine ⟨⟨spatialPoint q env, radial_zero q env h⟩, ?_⟩
  have HP := (FormulaSignSlotCircularBoundedCover.positivePoint (source true q)
    (closedPoint true q env h)).property
  have HC := (FormulaSignSlotRadialJointCoreReadback.zero_iff q env).mp h |>.2.2.2.2.1
  have HI := (FormulaSignSlotMarginProjection.objectiveIndex (source true q)).isLt
  have HH := HC (FormulaSignSlotMarginProjection.objectiveIndex (source true q)).val HI
  have HV := positive_coordinate (source true q) (closedPoint true q env h)
    (FormulaSignSlotMarginProjection.objectiveIndex (source true q))
  change (FormulaSignSlotCircularBoundedCover.positivePoint (source true q)
    (closedPoint true q env h)).val.val (FormulaSignSlotMarginProjection.objectiveIndex (source true q)) =
      env (column 1 (FormulaSignSlotMarginProjection.objectiveIndex (source true q)).val) at HV
  change 0 < (FormulaSignSlotCircularBoundedCover.positivePoint (source true q)
    (closedPoint true q env h)).val.val (FormulaSignSlotMarginProjection.objectiveIndex (source true q)) at HP
  have HP' := HV ▸ HP
  change 0 < env (column 2 (FormulaSignSlotMarginProjection.objectiveIndex (source true q)).val)
  rw [HH]
  exact HP'

end LeanCanny.Encoding.FormulaSignSlotRadialJointGeometry
