/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeLevelParameters
public import LeanCanny.ETR.TubeRegularSpatialLift
public import LeanCanny.ETR.TubeCompiledAffineLift
public import LeanCanny.Geometry.TubeCriticalSampling

/-! # Stored rational tube samples lift to compiled affine roots

The same packet realizes the geometric and compiled parameter maps. On a
common small positive level interval, every geometric projection root lifts
by its inverse base derivative, for every added linear projection. Decoding
any compiled root recovers a geometric projection root at every level.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeLevelPacket
open LeanCanny.Encoding LeanCanny.Algebra
open Geometry TubeEncoding TubeProjectionEncoding
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm CompactSource.term
attribute [local irreducible] Macaulay.matrix Matrix.det TubeCleared.uniformDegree

theorem parameters_coefficientMap_real (c : List Bool) (alpha : ℝ) :
    TubeRegularFiber.coefficientMap (pairFst c) (parameters c alpha) =
      TubePolynomial.coefficientMap (epsilon c : ℝ) (delta c : ℝ) alpha := by
  simpa only [Algebra.algebraMap_self, RingHom.id_comp, RingHom.id_apply] using
    (parameters_coefficientMap (L := ℝ) c alpha)

theorem parameters_direction_real (c : List Bool) (alpha : ℝ) :
    TubeRegularFiber.direction (pairFst c) (parameters c alpha) = fun i => (direction c i : ℝ) := by
  have hcast (q : ℚ) : algebraMap ℚ ℝ q = (q : ℝ) := by
    simpa only [Rat.cast_id] using map_ratCast (algebraMap ℚ ℝ) q
  simpa only [hcast] using (parameters_direction c alpha)

theorem projectionRootSet_iff_equations (c : List Bool) (s : Finset (PerturbedSource.Index (pairFst c)))
    (alpha : ℝ) (x : TubeSource.Coordinate (pairFst c) → ℝ) :
    x ∈ TubePolynomial.projectionRootSet (CompactSource.polynomial (pairFst c)) s
      (epsilon c : ℝ) (delta c : ℝ) alpha (fun i => (direction c i : ℝ)) ↔
      ∀ j, (TubeSource.projectionSystem (pairFst c) s j).eval₂
        (TubeRegularFiber.coefficientMap (pairFst c) (parameters c alpha))
        (Sum.elim x (TubeRegularFiber.direction (pairFst c) (parameters c alpha))) = 0 := by
  rw [parameters_coefficientMap_real, parameters_direction_real]
  constructor
  · intro h j
    exact (TubeSource.eval_integerProjection (pairFst c) s j (epsilon c : ℝ) (delta c : ℝ)
      alpha x (fun i => (direction c i : ℝ))).symm.trans (h j)
  · intro h j
    exact (TubeSource.eval_integerProjection (pairFst c) s j (epsilon c : ℝ) (delta c : ℝ)
      alpha x (fun i => (direction c i : ℝ))).trans (h j)

noncomputable def samplePoint (c : List Bool) (z : Fin (TubeParameter.spatialCount (pairFst c)) → ℝ) :
    TubeSource.Coordinate (pairFst c) → ℝ :=
  fun i => TubeCompiledAffineRoots.decodedPoint (pairFst c) z (some i)

theorem projection_root_of_compiled (active : List Bool → List Bool) (ell : ℕ → ℤ)
    (c : List Bool) (alpha : ℝ) (z : Fin (TubeParameter.spatialCount (pairFst c)) → ℝ)
    (hz : ∀ i, MvPolynomial.eval z
      (TubeCharacteristicQuotient.finiteSystem pairFst active numerator denominator (fun _ => ell) c alpha i) = 0) :
    samplePoint c z ∈ TubePolynomial.projectionRootSet (CompactSource.polynomial (pairFst c))
      (activeSet (TubeIndexed.arity (pairFst c)) (active c))
      (epsilon c : ℝ) (delta c : ℝ) alpha (fun i => (direction c i : ℝ)) := by
  apply (projectionRootSet_iff_equations c _ alpha _).mpr
  exact TubeRegularFiber.projection_roots_of_spatial (pairFst c) _ (parameters c alpha)
    (TubeCompiledAffineRoots.decodedPoint (pairFst c) z)
    (TubeCompiledAffineRoots.spatial_roots_of_compiled pairFst active numerator denominator
      (fun _ => ell) c alpha (fun i _ => denominator_eval_ne_zero c i alpha) z hz)

theorem exists_compiled_root_of_regular_projection (active : List Bool → List Bool) (ell : ℕ → ℤ)
    (c : List Bool) (alpha : ℝ) (hb : direction c (TubePolynomial.base _) = 1)
    (x : TubeSource.Coordinate (pairFst c) → ℝ)
    (hx : x ∈ TubePolynomial.projectionRootSet (CompactSource.polynomial (pairFst c))
      (activeSet (TubeIndexed.arity (pairFst c)) (active c))
      (epsilon c : ℝ) (delta c : ℝ) alpha (fun i => (direction c i : ℝ)))
    (hregular : Function.Surjective (fderiv ℝ
      (fun y => (TubeSource.polynomial (pairFst c) (activeSet (TubeIndexed.arity (pairFst c)) (active c))).eval₂
        (TubePolynomial.coefficientMap (epsilon c : ℝ) (delta c : ℝ) alpha) y) x)) :
    ∃ z : Fin (TubeParameter.spatialCount (pairFst c)) → ℝ,
      (∀ i, MvPolynomial.eval z
        (TubeCharacteristicQuotient.finiteSystem pairFst active numerator denominator (fun _ => ell) c alpha i) = 0) ∧
      samplePoint c z = x := by
  let s := activeSet (TubeIndexed.arity (pairFst c)) (active c)
  let r := TubeRegularFiber.reciprocalPoint (pairFst c) s (parameters c alpha) x
  have hbase : TubeRegularFiber.direction (pairFst c) (parameters c alpha) (TubePolynomial.base _) = 1 := by
    rw [parameters_direction_real]
    change (direction c (TubePolynomial.base _) : ℝ) = 1
    exact_mod_cast hb
  have hreg : Function.Surjective (fderiv ℝ (fun y =>
      (TubeSource.polynomial (pairFst c) s).eval₂
        (TubeRegularFiber.coefficientMap (pairFst c) (parameters c alpha)) y) x) := by
    rwa [parameters_coefficientMap_real]
  have hsp := TubeRegularFiber.spatial_roots_of_regular_projection (pairFst c) s
    (parameters c alpha) x hbase ((projectionRootSet_iff_equations c s alpha x).mp hx) hreg
  refine ⟨TubeCompiledAffineRoots.compiledPoint (pairFst c) ell r,
    TubeCompiledAffineRoots.compiled_root_of_spatial pairFst active numerator denominator
      (fun _ => ell) c alpha (fun i _ => denominator_eval_ne_zero c i alpha) r hsp, ?_⟩
  funext i
  exact congrFun (TubeCompiledAffineRoots.decodedPoint_compiledPoint (pairFst c) ell r) (some i)

theorem exists_compiled_lift_interval (c : List Bool) (hb : direction c (TubePolynomial.base _) = 1) :
    ∃ a : ℝ, 0 < a ∧ ∀ alpha : ℝ, 0 < alpha → alpha < a →
      ∀ (active : List Bool → List Bool) (ell : ℕ → ℤ) (x : TubeSource.Coordinate (pairFst c) → ℝ),
        x ∈ TubePolynomial.projectionRootSet (CompactSource.polynomial (pairFst c))
          (activeSet (TubeIndexed.arity (pairFst c)) (active c))
          (epsilon c : ℝ) (delta c : ℝ) alpha (fun i => (direction c i : ℝ)) →
        ∃ z : Fin (TubeParameter.spatialCount (pairFst c)) → ℝ,
          (∀ i, MvPolynomial.eval z
            (TubeCharacteristicQuotient.finiteSystem pairFst active numerator denominator (fun _ => ell) c alpha i) = 0) ∧
          samplePoint c z = x := by
  obtain ⟨a, ha, hr⟩ := TubeSource.exists_regular_interval (pairFst c) (epsilon c : ℝ) (delta c : ℝ)
  refine ⟨a, ha, ?_⟩
  intro alpha hp hl active ell x hx
  apply exists_compiled_root_of_regular_projection active ell c alpha hb x hx
  apply hr alpha hp hl _ x
  have h := (TubeSource.eval_integerProjection (pairFst c) _ none (epsilon c : ℝ) (delta c : ℝ)
    alpha x (fun i => (direction c i : ℝ))).symm.trans (hx none)
  exact (ProjectionEquations.eval_level (TubeSource.polynomial (pairFst c) _)
    (TubePolynomial.base _) (TubePolynomial.coefficientMap (epsilon c : ℝ) (delta c : ℝ) alpha)
    x (fun i => (direction c i : ℝ))).symm.trans h

end LeanCanny.ETR.TubeLevelPacket
