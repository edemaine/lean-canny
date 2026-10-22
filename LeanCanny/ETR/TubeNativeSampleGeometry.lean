/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeLevelCoordinates
public import LeanCanny.ETR.TubeCompiledAffineLift

/-! # Native regular assignments and actual compiled tube samples

A spatial assignment extends uniquely by the packet's direction and parameter
values. Its regular equations are precisely the compiled spatial equations.
-/

@[expose] public section
namespace LeanCanny.ETR.TubeNativeSampleGeometry
open LeanCanny.Encoding LeanCanny.Algebra
open Geometry TubeEncoding TubeProjectionEncoding TubeLevelPacket
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree
attribute [local irreducible] Macaulay.matrix Matrix.det
set_option backward.isDefEq.respectTransparency false

noncomputable def extend (c : List Bool) (alpha : ℝ)
    (x : Option (TubeSource.Coordinate (pairFst c)) → ℝ) :
    TubeRegularSource.Variable (pairFst c) → ℝ :=
  fun i => i.elim (x none) (TubeMacaulay.values _ (parameters c alpha) (fun k => x (some k)))

@[simp] theorem extend_none (c : List Bool) (alpha : ℝ)
    (x : Option (TubeSource.Coordinate (pairFst c)) → ℝ) : extend c alpha x none = x none := rfl

@[simp] theorem extend_point (c : List Bool) (alpha : ℝ)
    (x : Option (TubeSource.Coordinate (pairFst c)) → ℝ) (i : TubeSource.Coordinate (pairFst c)) :
    extend c alpha x (some (.inl (.inl i))) = x (some i) := rfl

@[simp] theorem extend_direction (c : List Bool) (alpha : ℝ)
    (x : Option (TubeSource.Coordinate (pairFst c)) → ℝ) (i : TubeSource.Coordinate (pairFst c)) :
    extend c alpha x (some (.inl (.inr i))) = parameters c alpha (MvPolynomial.X (.inl i)) := rfl

@[simp] theorem extend_parameter (c : List Bool) (alpha : ℝ)
    (x : Option (TubeSource.Coordinate (pairFst c)) → ℝ) (p : TubePolynomial.Parameter) :
    extend c alpha x (some (.inr p)) = parameters c alpha (MvPolynomial.X (.inr p)) := rfl

noncomputable def spatial (c : List Bool) (w : TubeRegularSource.Variable (pairFst c) → ℝ) :
    Option (TubeSource.Coordinate (pairFst c)) → ℝ
  | none => w none
  | some i => w (some (.inl (.inl i)))

@[simp] theorem spatial_extend (c : List Bool) (alpha : ℝ)
    (x : Option (TubeSource.Coordinate (pairFst c)) → ℝ) : spatial c (extend c alpha x) = x := by
  funext i
  cases i <;> rfl

/-- The rational pins determine every nonspecialized variable. -/
theorem eq_extend_of_pins (c : List Bool) (alpha : ℝ)
    (w : TubeRegularSource.Variable (pairFst c) → ℝ)
    (hd : ∀ i, w (some (.inl (.inr i))) = parameters c alpha (MvPolynomial.X (.inl i)))
    (hp : ∀ p, w (some (.inr p)) = parameters c alpha (MvPolynomial.X (.inr p))) :
    w = extend c alpha (spatial c w) := by
  funext i
  rcases i with _ | ((i | i) | p)
  · rfl
  · rfl
  · exact hd i
  · exact hp p

theorem regular_iff_spatial (c mask : List Bool) (alpha : ℝ)
    (x : Option (TubeSource.Coordinate (pairFst c)) → ℝ) :
    (∀ j, (TubeRegularSource.polynomial (pairFst c)
      (activeSet (TubeIndexed.arity (pairFst c)) mask) j).eval₂ (Int.castRingHom ℝ)
        (extend c alpha x) = 0) ↔
      ∀ j, (TubeRegularMacaulay.spatial (pairFst c)
        (activeSet (TubeIndexed.arity (pairFst c)) mask) j).eval₂ (parameters c alpha)
          (fun i => i.elim 1 x) = 0 := by
  constructor <;> intro h j
  · rw [TubeRegularMacaulay.spatial_eval_chart]
    exact h j
  · have H := h j
    rw [TubeRegularMacaulay.spatial_eval_chart] at H
    exact H

theorem regular_iff_compiled (c mask : List Bool) (ell : ℕ → ℤ) (alpha : ℝ)
    (x : Option (TubeSource.Coordinate (pairFst c)) → ℝ) :
    (∀ j, (TubeRegularSource.polynomial (pairFst c)
      (activeSet (TubeIndexed.arity (pairFst c)) mask) j).eval₂ (Int.castRingHom ℝ)
        (extend c alpha x) = 0) ↔
      ∀ i, MvPolynomial.eval (TubeCompiledAffineRoots.compiledPoint (pairFst c) ell x)
        (TubeCharacteristicQuotient.finiteSystem pairFst (fun _ => mask) numerator denominator
          (fun _ => ell) c alpha i) = 0 := by
  rw [regular_iff_spatial]
  exact (TubeCompiledAffineRoots.compiled_root_iff_spatial pairFst (fun _ => mask)
    numerator denominator (fun _ => ell) c alpha (fun i _ => denominator_eval_ne_zero c i alpha) x).symm

@[simp] theorem samplePoint_compiledPoint (c : List Bool) (ell : ℕ → ℤ)
    (x : Option (TubeSource.Coordinate (pairFst c)) → ℝ) :
    samplePoint c (TubeCompiledAffineRoots.compiledPoint (pairFst c) ell x) = fun i => x (some i) := by
  unfold samplePoint
  rw [TubeCompiledAffineRoots.decodedPoint_compiledPoint]

/-- Adding the projection coordinate preserves the geometric inactive signs. -/
theorem compiledSample_iff (c mask : List Bool) (ell : ℕ → ℤ) (alpha : ℝ)
    (x : Option (TubeSource.Coordinate (pairFst c)) → ℝ) :
    CompiledSample c mask ell alpha (TubeCompiledAffineRoots.compiledPoint (pairFst c) ell x) ↔
      (∀ j, (TubeRegularSource.polynomial (pairFst c)
        (activeSet (TubeIndexed.arity (pairFst c)) mask) j).eval₂ (Int.castRingHom ℝ)
          (extend c alpha x) = 0) ∧
      ∀ i, i ∉ activeSet (TubeIndexed.arity (pairFst c)) mask →
        0 < PolynomialPerturbation.parameterMap (CompactSource.polynomial (pairFst c)) (epsilon c : ℝ)
          (TubePolynomial.splitPoint (fun k => x (some k))) i := by
  unfold CompiledSample
  rw [samplePoint_compiledPoint, regular_iff_compiled]

/-- Every compiled root determines the corresponding native regular assignment. -/
theorem regular_of_compiled (c mask : List Bool) (ell : ℕ → ℤ) (alpha : ℝ)
    (z : Fin (TubeParameter.spatialCount (pairFst c)) → ℝ)
    (hz : ∀ i, MvPolynomial.eval z
      (TubeCharacteristicQuotient.finiteSystem pairFst (fun _ => mask) numerator denominator
        (fun _ => ell) c alpha i) = 0) :
    ∀ j, (TubeRegularSource.polynomial (pairFst c)
      (activeSet (TubeIndexed.arity (pairFst c)) mask) j).eval₂ (Int.castRingHom ℝ)
        (extend c alpha (TubeCompiledAffineRoots.decodedPoint (pairFst c) z)) = 0 := by
  apply (regular_iff_spatial c mask alpha _).mpr
  exact TubeCompiledAffineRoots.spatial_roots_of_compiled pairFst (fun _ => mask)
    numerator denominator (fun _ => ell) c alpha (fun i _ => denominator_eval_ne_zero c i alpha) z hz

end LeanCanny.ETR.TubeNativeSampleGeometry
