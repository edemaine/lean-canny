/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalCoarseRule
public import LeanCanny.Algebra.IntegralMixedCriticalDegree
public import LeanCanny.Algebra.ClearedAffinePolynomial
/-! # The actual coarse-slice critical-height cut uses one original degree cap

The ordinary relative critical polynomial selects the height coordinate.
An exact-degree affine clearing converts it to the represented scalar
parameter, using the same old algebra and no inverses in its definition.
-/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalCriticalHeight
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.Geometry
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineExceptionalBankSource (births width)
open FlatAffineExceptionalCoarseRule (state rule)
open IntegralMixedHistory
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def relative (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u : List Bool) (hm : births F u ≤ S) :=
  criticalPolynomial (state F C h S u (hm.trans (Nat.le_succ S))) hm (rule F h u)

noncomputable def cut (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u : List Bool) (hm : births F u ≤ S) :=
  ClearedAffinePolynomial.polynomial (criticalDegree (state F C h S u (hm.trans (Nat.le_succ S))) hm (rule F h u))
    (relative F C h S u hm) (FlatAffineExceptionalParentBank.shiftedNumerator F C h S u (hm.trans (Nat.le_succ S)) (h u))
    (FlatAffineExceptionalParentBank.denominator F C h S u (hm.trans (Nat.le_succ S)) :
      (state F C h S u (hm.trans (Nat.le_succ S))).sampler.scalarPrefix.carrier)
    ((2 * FlatAffineExceptionalParentBank.denominator F C h S u (hm.trans (Nat.le_succ S)) : ℤ) :
      (state F C h S u (hm.trans (Nat.le_succ S))).sampler.scalarPrefix.carrier)

theorem degree_le (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u : List Bool) (hm : births F u ≤ S) :
    (cut F C h S u hm).natDegree ≤ criticalDegree (state F C h S u (hm.trans (Nat.le_succ S))) hm (rule F h u) :=
  (ClearedAffinePolynomial.degree_le _ _ _ _ _).trans (IntegralMixedCriticalRoot.degree_le _ _ _)

theorem initial_cap (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u : List Bool) (hm : births F u ≤ S) :
    (cut F C h S u hm).natDegree ≤ 2 ^ width F u := (degree_le F C h S u hm).trans (criticalDegree_cap _ _ _)

theorem original_degree_cap (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u : List Bool) (hm : births F u ≤ S) :
    (cut F C h S u hm).natDegree ≤ PurePowerReductionBounds.dimension (arity F u) (FlatAffinePowerControls.degree F u) :=
  (degree_le F C h S u hm).trans (IntegralCriticalFactorCeiling.dimension_mono (by
    change F.source.dim u+3-(rule F h u).offset.val+1 ≤ F.source.dim u+4
    omega) (Nat.le_refl _))

theorem selected_nonzero (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u : List Bool) (hm : births F u ≤ S)
    (φ : (state F C h S u (hm.trans (Nat.le_succ S))).sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) :
    (cut F C h S u hm).map φ.toRingHom ≠ 0 := by
  apply ClearedAffinePolynomial.selected_nonzero φ.toRingHom _ _ _ _ _ (IntegralMixedCriticalRoot.degree_le _ _ _)
    (IntegralMixedCriticalRoot.selected_nonzero _ _ _ φ)
  · rw [map_intCast]
    exact Int.cast_ne_zero.mpr (FlatAffineExceptionalParentBank.denominator_ne_zero F C h S u _)
  · rw [map_intCast]
    exact Int.cast_ne_zero.mpr (mul_ne_zero (by decide) (FlatAffineExceptionalParentBank.denominator_ne_zero F C h S u _))

theorem finite_roots (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u : List Bool) (hm : births F u ≤ S)
    (φ : (state F C h S u (hm.trans (Nat.le_succ S))).sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) :
    {t : ℝ | (cut F C h S u hm).eval₂ φ.toRingHom t = 0}.Finite := by
  simpa only [Polynomial.IsRoot, Polynomial.eval_map] using Polynomial.finite_setOfPred_isRoot (selected_nonzero F C h S u hm φ)

end LeanCanny.Encoding.FlatAffineExceptionalCriticalHeight
