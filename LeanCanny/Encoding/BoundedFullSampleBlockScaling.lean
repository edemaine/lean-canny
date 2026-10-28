/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedFullSampleBlockPolynomial
public import LeanCanny.Encoding.BoundedCriticalSampleBlockScaling
public import LeanCanny.Encoding.BoundedFullBlockKernel

/-! # Exact positive scaling for full-source sample blocks

At an actual parent, all cleared denominators are constant in the free
coordinates. Specialization is therefore a positive constant times the
original block of the constructed full source. Its complete critical zero
set and analytic regularity are preserved, including singular critical roots.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedFullSampleBlockScaling
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR MvPolynomial
open BoundedFullSampleBlock BoundedFullSampleBlockPolynomial
open BoundedCriticalSampleBlockSource
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedCriticalSampleLabels.parameter

noncomputable def scale (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) : ℝ :=
  ∏ i ∈ Finset.range (arity F u), (coordinate F.parent F.offset F.dim false u i).eval₂ (Int.castRingHom ℝ)
    (environment _ (BoundedCriticalSampleLabels.parameter F.parent (pairFst u) p).val 0) ^ clearing F u

theorem scale_pos (F : Inputs) (u : List Bool) (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) :
    0 < scale F u p := by
  unfold scale clearing
  apply Finset.prod_pos
  intro i _
  rw [pow_mul]
  exact pow_pos (sq_pos_of_ne_zero
    (BoundedCriticalSampleBlockEvaluation.denominator_nonzero F.parent F.offset F.dim u p 0 i)) _

theorem eval (F : Inputs) (u : List Bool) (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u))
    (y : Fin (F.dim u) → ℝ) :
    (polynomial F u).eval₂ (Int.castRingHom ℝ)
      (environment _ (BoundedCriticalSampleLabels.parameter F.parent (pairFst u) p).val y) =
        scale F u p * ((family F).source u).eval₂ (Int.castRingHom ℝ)
          (fun i => assignment p.val (F.offset u) (F.dim u) y i.val) := by
  let v := environment _ (BoundedCriticalSampleLabels.parameter F.parent (pairFst u) p).val y
  have H := IndexedMultivariateRational.eval₂_cleared (Int.castRingHom ℝ) v
    (arity F u) ((family F).terms u) (clearing F u) ((family F).coefficient u)
    (FixedWidthPolynomial.entry (sourceWidth F u))
    (coordinate F.parent F.offset F.dim true u) (coordinate F.parent F.offset F.dim false u)
    ((family F).indexed.exponent_le u)
    (fun i _ => BoundedCriticalSampleBlockEvaluation.denominator_nonzero F.parent F.offset F.dim u p y i)
  have hs : RationalSubstitution.Indexed.source (arity F u) ((family F).terms u) ((family F).coefficient u)
      (FixedWidthPolynomial.entry (sourceWidth F u)) = (family F).source u := (family F).source_eq u
  rw [hs] at H
  have hp : (∏ i ∈ Finset.range (arity F u), (coordinate F.parent F.offset F.dim false u i).eval₂
      (Int.castRingHom ℝ) v ^ clearing F u) = scale F u p := by
    unfold scale
    apply Finset.prod_congr rfl
    intro i _
    rw [BoundedCriticalSampleBlockScaling.denominator_constant F.parent F.offset F.dim u _ y 0 i]
  rw [hp] at H
  have hv : (fun i : Fin (arity F u) => (coordinate F.parent F.offset F.dim true u i.val).eval₂ (Int.castRingHom ℝ) v /
      (coordinate F.parent F.offset F.dim false u i.val).eval₂ (Int.castRingHom ℝ) v) =
        (fun i => assignment p.val (F.offset u) (F.dim u) y i.val) :=
    funext fun i => BoundedCriticalSampleBlockEvaluation.coordinate_eval F.parent F.offset F.dim u p y i.val
  rw [hv] at H
  exact H

noncomputable def original (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) : MvPolynomial (Fin (F.dim u)) ℝ :=
  CoordinateBlockSpecialization.finite (Int.castRingHom ℝ) (Formula.extend p.val) (F.offset u) (F.dim u) ((family F).source u)

theorem eval_original (F : Inputs) (u : List Bool) (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u))
    (y : Fin (F.dim u) → ℝ) : (original F u p).eval y =
      ((family F).source u).eval₂ (Int.castRingHom ℝ) (fun i => assignment p.val (F.offset u) (F.dim u) y i.val) := by
  unfold original
  rw [CoordinateBlockSpecialization.eval_finite]
  congr 1
  funext i
  simp only [assignment, InBlock]
  by_cases hi : F.offset u ≤ i.val ∧ i.val < F.offset u + F.dim u
  · simp only [dite_eq_left hi]
  · simp only [dite_eq_right hi]

noncomputable def specialized (F : Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) : MvPolynomial (Fin (F.dim u)) ℝ :=
  ParameterSpatialSpecialization.specialize (Int.castRingHom ℝ)
    (BoundedCriticalSampleLabels.parameter F.parent (pairFst u) p).val (polynomial F u)

theorem specialized_eq (F : Inputs) (u : List Bool) (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u)) :
    specialized F u p = C (scale F u p) * original F u p := by
  apply MvPolynomial.funext
  intro y
  rw [specialized, ParameterSpatialSpecialization.eval_specialize,
    ← BoundedCriticalSampleBlockCriticalGeometry.environment_eq_cons, eval, eval_mul, eval_C, eval_original]

theorem zero_iff (F : Inputs) (u : List Bool) (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u))
    (y : Fin (F.dim u) → ℝ) : (specialized F u p).eval y = 0 ↔ (original F u p).eval y = 0 := by
  rw [specialized_eq, eval_mul, eval_C]
  simp only [mul_eq_zero, ne_of_gt (scale_pos F u p), false_or]

theorem hypersurface_regular_iff (F : Inputs) (u : List Bool) (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u))
    (y : Fin (F.dim u) → ℝ) :
    Function.Surjective (fderiv ℝ (fun z => (specialized F u p).eval z) y) ↔
      Function.Surjective (fderiv ℝ (fun z => (original F u p).eval z) y) := by
  rw [specialized_eq]
  simpa only [eval₂_id] using Geometry.ScaledCriticalSystem.hypersurface_regular_iff (RingHom.id ℝ)
    (original F u p) (scale F u p) (ne_of_gt (scale_pos F u p)) y

theorem critical_zero_iff (F : Inputs) (u : List Bool) (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u))
    (b : Fin (F.dim u)) (v : Fin (F.dim u) → ℝ) (y : Fin (F.dim u) → ℝ) :
    (∀ i, (ProjectionCriticalFamily.spatialEquation (specialized F u p) b v i).eval y = 0) ↔
      ∀ i, (ProjectionCriticalFamily.spatialEquation (original F u p) b v i).eval y = 0 := by
  rw [specialized_eq]
  exact Geometry.ScaledCriticalSystem.zero_iff (RingHom.id ℝ) _ b v _ (ne_of_gt (scale_pos F u p)) y

theorem critical_regular_iff (F : Inputs) (u : List Bool) (p : BoundedFullCriticalSamples.Samples F.parent (pairFst u))
    (b : Fin (F.dim u)) (v : Fin (F.dim u) → ℝ) (y : Fin (F.dim u) → ℝ) :
    (fderiv ℝ (fun z => fun i => (ProjectionCriticalFamily.spatialEquation (specialized F u p) b v i).eval z) y).IsInvertible ↔
      (fderiv ℝ (fun z => fun i => (ProjectionCriticalFamily.spatialEquation (original F u p) b v i).eval z) y).IsInvertible := by
  rw [specialized_eq]
  simpa only [eval₂_id] using Geometry.ScaledCriticalSystem.regular_iff (RingHom.id ℝ) _ b v (scale F u p)
    (ne_of_gt (scale_pos F u p)) y

def ofKernel (P : BoundedFullWriter.Readers) (F : BoundedFullBlockKernel.Inputs) : Inputs :=
  ⟨P, F.source, F.offset, BoundedFullBlockKernel.dim F⟩

theorem ofKernel_polyTime {P : BoundedFullWriter.Readers} {F : BoundedFullBlockKernel.Inputs}
    (hP : P.PolyTime) (hS : F.source.PolyTime) (ho : BinaryFn F.offset) (hf : UnaryFn F.free) :
    (ofKernel P F).PolyTime := ⟨hP, hS, ho, hf.add (UnaryFn.const 1)⟩

theorem original_ofKernel (P : BoundedFullWriter.Readers) (F : BoundedFullBlockKernel.Inputs) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples P (pairFst u)) :
    original (ofKernel P F) u p = BoundedFullBlockKernel.slice F u (Formula.extend p.val) := rfl

def whole (P S : BoundedFullWriter.Readers) : Inputs := ⟨P, S, fun _ => 0, fun u => S.dim u + 4⟩

theorem scale_whole (P S : BoundedFullWriter.Readers) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples P (pairFst u)) : scale (whole P S) u p = 1 := by
  unfold scale
  apply Finset.prod_eq_one
  intro i hi
  have hin : InBlock ((whole P S).offset u) ((whole P S).dim u) i := by
    change 0 ≤ i ∧ i < 0 + (S.dim u + 4)
    have H := Finset.mem_range.mp hi
    exact ⟨Nat.zero_le _, by simpa only [arity, whole, Nat.zero_add] using H⟩
  simp only [coordinate, Bool.false_eq_true, ite_false, dite_eq_left hin, eval₂_one, one_pow]

theorem specialized_whole (P S : BoundedFullWriter.Readers) (u : List Bool)
    (p : BoundedFullCriticalSamples.Samples P (pairFst u)) :
    specialized (whole P S) u p = (BoundedFullCriticalSamples.polynomial S u).map (Int.castRingHom ℝ) := by
  rw [specialized_eq, scale_whole, map_one, one_mul]
  exact CoordinateBlockSpecialization.finite_all _ _ _

end LeanCanny.Encoding.BoundedFullSampleBlockScaling
