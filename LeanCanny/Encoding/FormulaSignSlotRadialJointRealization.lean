/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialJointGeometry
public import LeanCanny.Encoding.FormulaSignSlotRadialJointPacking
/-! # A genuine radial descriptor has a root of the literal joint integer source

The positive anchor and the two closed lifts are the actual geometric ones.
The constructor retains them exactly rather than replacing them by samples.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialJointRealization
open LeanCanny.Computation LeanCanny.Connectivity LeanCanny.ETR LeanCanny.Geometry
open FormulaSignSlotRadialJointLayout FormulaSignSlotRadialJointCore
open FormulaSignSlotRadialJointGeometry FormulaSignSlotRadialJointPacking
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] FormulaSignSlotTiltedRadialGrid.Q
  FormulaSignSlotCenteredRadialLimits.polynomial FormulaSignSlotSource.dimension
  FormulaSignSlotMargin.initialPolynomial FormulaSignSlotCircularBoundedCover.root
  ClosedFormulaGateMetadata.dimension ClosedFormulaGateMetadata.count ClosedFormulaGateMetadata.atom
  ClosedFormulaGateMetadata.kind Input.field FormulaView.normalize

noncomputable def leftCenter (q : List Bool)
    (A : FormulaSignSlotCircularBoundedCover.Source (source false q)) : Fin (centerCount q) → ℝ :=
  fun i => (FormulaSignSlotCircularBoundedCover.projectedPoint (source false q) A).val
    (Fin.cast (original_dimension_eq q).symm i)

theorem leftCenter_coordinate (q : List Bool)
    (A : FormulaSignSlotCircularBoundedCover.Source (source false q)) (i : Fin (centerCount q)) :
    leftCenter q A i = A.val ⟨i.val, by
      exact (FormulaSignSlotCircularBoundedCover.projectedIndex (source false q)
        (Fin.cast (original_dimension_eq q).symm i)).isLt⟩ := by
  exact FormulaSignSlotCircularBoundedCover.projectedPoint_coordinate _ _ _

private theorem old_spatial_coordinate (c : List Bool)
    (a : Fin (FormulaSignSlotSource.dimension c) → ℝ) (r : ℝ)
    (z : FormulaSignSlotTiltedRadialGrid.OldPositive c a r)
    (i : Fin (FormulaSignSlotMargin.initialDimension c)) :
    (FormulaSignSlotTiltedRadialGrid.originalPositive c a r z).val.val i =
      z.val.val ⟨i.val, by have H := i.isLt; dsimp only [FormulaSignSlotCenteredRadialGraph.N]; omega⟩ := rfl

private theorem formal_zero (c : List Bool) (a : Fin (FormulaSignSlotSource.dimension c) → ℝ)
    (r : ℝ) (z : FormulaSignSlotTiltedRadialGrid.OldPositive c a r) :
    (FormulaSignSlotRadialFormalInput.equation c).eval (formal c z.val.val a r) = 0 := by
  rw [formal_eval]
  have HC : (fun i : Fin (FormulaSignSlotSource.dimension c) =>
      formal c z.val.val a r (FormulaSignSlotRadialFormalInput.spatial c + i.val)) = a :=
    funext (formal_center c z.val.val a r)
  have HS : (fun i : Fin (FormulaSignSlotRadialFormalInput.spatial c) =>
      formal c z.val.val a r i.val) = z.val.val := funext (formal_spatial c z.val.val a r)
  rw [HC, formal_radius]
  have HZ : (FormulaSignSlotCenteredRadialLimits.polynomial c a r).eval z.val.val = 0 := by
    simpa only [FormulaSignSlotTiltedRadialGrid.Q, CoerciveComponentSampling.Zeros, Set.mem_ofPred_eq] using z.val.property
  have HE := congrArg (fun f : Fin (FormulaSignSlotRadialFormalInput.spatial c) → ℝ =>
    (FormulaSignSlotCenteredRadialLimits.polynomial c a r).eval f) HS
  exact HE.trans HZ

theorem exists_root (q : List Bool)
    (A : FormulaSignSlotCircularBoundedCover.Source (source false q))
    (B : FormulaSignSlotCircularBoundedCover.Source (source true q))
    (b r : ℝ) (hr : 0 < r) (hb : r < b)
    (z : FormulaSignSlotTiltedRadialGrid.OldPositive (source true q) (leftCenter q A) r)
    (hB : FormulaSignSlotCircularBoundedCover.positivePoint (source true q) B =
      FormulaSignSlotTiltedRadialGrid.originalPositive (source true q) (leftCenter q A) r z) :
    ∃ env : ℕ → ℝ, (equation q).eval env = 0 ∧
      (∀ i : Fin (circleCount false q), env (column 0 i.val) = A.val i) ∧
      (∀ i : Fin (circleCount true q), env (column 1 i.val) = B.val i) ∧
      center q env = leftCenter q A ∧ spatialPoint q env = z.val.val ∧
      parameter q env = r ∧ env boundVariable = b := by
  obtain ⟨wr, Hwr⟩ := exists_positive_witness r hr
  obtain ⟨wg, Hwg⟩ := exists_positive_witness (b-r) (sub_pos.mpr hb)
  let env := pack (Formula.extend A.val) (Formula.extend B.val)
    (formal (source true q) z.val.val (leftCenter q A) r) b wr wg
  have HA (i : Fin (circleCount false q)) : env (column 0 i.val) = A.val i := by
    have HI : i.val < (BoundedMonotoneGateSource.description ClosedFormulaGateTruth.F
      (FormulaSignSlotCircularBoundedCover.root (source false q))).dimension := i.isLt
    simp only [env, pack_zero, Formula.extend, dite_eq_left HI]
    exact congrArg A.val (Fin.ext rfl)
  have HB (i : Fin (circleCount true q)) : env (column 1 i.val) = B.val i := by
    have HI : i.val < (BoundedMonotoneGateSource.description ClosedFormulaGateTruth.F
      (FormulaSignSlotCircularBoundedCover.root (source true q))).dimension := i.isLt
    simp only [env, pack_one, Formula.extend, dite_eq_left HI]
    exact congrArg B.val (Fin.ext rfl)
  have HF (i : ℕ) : env (column 2 i) = formal (source true q) z.val.val (leftCenter q A) r i :=
    pack_two _ _ _ _ _ _ i
  have HC : center q env = leftCenter q A := by
    funext i
    exact (HA ⟨i.val, (FormulaSignSlotCircularBoundedCover.projectedIndex (source false q)
      (Fin.cast (original_dimension_eq q).symm i)).isLt⟩).trans (leftCenter_coordinate q A i).symm
  have HS : spatialPoint q env = z.val.val := by
    funext i
    exact (HF i.val).trans (formal_spatial _ _ _ _ i)
  have HR : parameter q env = r := (HF _).trans (formal_radius _ _ _ _)
  have Hbound : env boundVariable = b := pack_bound _ _ _ _ _ _
  have Hrad : env radiusWitness = wr := pack_radiusWitness _ _ _ _ _ _
  have Hgap : env gapWitness = wg := pack_gapWitness _ _ _ _ _ _
  refine ⟨env, ?_, HA, HB, HC, HS, HR, Hbound⟩
  apply (FormulaSignSlotRadialJointCoreReadback.zero_iff q env).mpr
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have HT : (fun i => env (column 0 i)) = Formula.extend A.val := funext (pack_zero _ _ _ _ _ _)
    rw [HT]
    exact A.property
  · have HT : (fun i => env (column 1 i)) = Formula.extend B.val := funext (pack_one _ _ _ _ _ _)
    rw [HT]
    exact B.property
  · have HT : (fun i => env (column 2 i)) = formal (source true q) z.val.val (leftCenter q A) r := funext HF
    rw [HT]
    exact formal_zero _ _ _ z
  · intro i hi
    exact (HF _).trans ((formal_center _ _ _ _ ⟨i,hi⟩).trans (congrFun HC ⟨i,hi⟩).symm)
  · intro i hi
    have HV := congrArg (fun y : FormulaSignSlotComponentMaxima.Positive (source true q) =>
      y.val.val ⟨i,hi⟩) hB
    rw [positive_coordinate, old_spatial_coordinate] at HV
    exact (HF _).trans ((formal_spatial _ _ _ _ ⟨i, by
      unfold FormulaSignSlotRadialFormalInput.spatial; change i < FormulaSignSlotMargin.initialDimension (source true q) at hi; dsimp only [FormulaSignSlotCenteredRadialGraph.N]; omega⟩).trans
      (HV.symm.trans (HB (FormulaSignSlotCircularBoundedCover.originalIndex _ (Fin.castAdd 2 ⟨i,hi⟩))).symm))
  · change parameter q env * env radiusWitness ^ 2 = 1
    rw [HR, Hrad]
    exact Hwr
  · rw [Hbound]
    change (b - parameter q env) * env gapWitness ^ 2 = 1
    rw [HR, Hgap]
    exact Hwg

/-- A genuine descriptor keeps its actual grid and all four cut conditions
in the concrete joint tuple. These receipts are not inferred from sampling. -/
theorem exists_root_of_descriptor (q : List Bool)
    (A : FormulaSignSlotCircularBoundedCover.Source (source false q))
    (i : Vertex (CanonicalAuxiliaryCandidateCover.width (source true q)))
    (D : FormulaSignSlotCandidateRadialDescriptor.Descriptor (source true q) i (leftCenter q A)) :
    ∃ env : ℕ → ℝ, (equation q).eval env = 0 ∧
      (∀ j : Fin (circleCount false q), env (column 0 j.val) = A.val j) ∧
      (∀ j : Fin (circleCount true q), env (column 1 j.val) = D.closedAnchor.val j) ∧
      center q env = leftCenter q A ∧ spatialPoint q env = D.anchor.val.val ∧
      parameter q env = D.parameter.val ∧ env boundVariable = D.bound ∧
      spatialPoint q env ∈ FormulaSignSlotRadialParameterGrid.grid (source true q)
        (center q env) (parameter q env) ∧
      ∀ t ∈ Set.Ioo 0 (env boundVariable), t ∉ FormulaSignSlotRadialBranchCuts.cuts
        (source true q) (center q env) := by
  have HB : FormulaSignSlotCircularBoundedCover.positivePoint (source true q) D.closedAnchor =
      FormulaSignSlotTiltedRadialGrid.originalPositive (source true q) (leftCenter q A) D.parameter.val D.anchor :=
    D.anchor_projection
  obtain ⟨env, H0, HA, HB, HC, HS, HR, Hbound⟩ := exists_root q A D.closedAnchor D.bound
    D.parameter.val D.parameter.property.1 D.parameter.property.2 D.anchor HB
  refine ⟨env, H0, HA, HB, HC, HS, HR, Hbound, ?_, ?_⟩
  · rw [HC, HS, HR]
    exact D.grid
  · rw [HC, Hbound]
    exact D.cut_free

end LeanCanny.Encoding.FormulaSignSlotRadialJointRealization
