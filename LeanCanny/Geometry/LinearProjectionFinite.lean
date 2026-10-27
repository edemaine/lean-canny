/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.LinearProjectionEliminant
public import LeanCanny.Geometry.AffineCoordinateFinite
public import LeanCanny.Algebra.MacaulayFiniteFiber

/-! # Bounded linear projection equations on finite affine fibers

The augmented affine zero set is the graph of the chosen linear projection.
Finite-fiber elimination therefore annihilates every projected complex root,
including singular roots and nonseparating choices of weights.
-/

@[expose] public section

namespace LeanCanny.Geometry.LinearProjectionEliminant
open MvPolynomial Set
open LeanCanny.Algebra AffineCoordinateSystem
open LinearProjectionSystem
open AffineCoordinateEliminant (affineCoefficientMap affineChart eval_affineCoefficientMap eval_affineChart)
open scoped BigOperators
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {R K : Type*} [CommRing R] [Field K]

theorem eval_affineSystem (φ : R →+* K) (q : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (hD : ∀ j, (q j).totalDegree ≤ d j) (v : Fin n → R)
    (z : Fin (n + 1) → K) :
    (fun j => MvPolynomial.eval z (MacaulayFiniteFiber.originalSystem (rows q d v)
      (affineCoefficientMap φ) affineChart j)) =
      Fin.cons (z 0 - (∑ i, φ (v i) * z i.succ)) (fun j => (q j).eval₂ φ (fun i => z i.succ)) := by
  have he : (fun j => MvPolynomial.eval z (affineChart (K := K) j)) =
      (fun j => (layout.symm j).elim 1 (fun i => z i.succ)) := funext (eval_affineChart z)
  simp only [MacaulayFiniteFiber.originalSystem, MvPolynomial.eval_eval₂,
    eval_affineCoefficientMap, he]
  exact LinearProjectionSystem.eval_rows φ q d hD v (z 0) (fun i => z i.succ)

theorem affineSystem_finite (φ : R →+* K) (q : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (hD : ∀ j, (q j).totalDegree ≤ d j) (v : Fin n → R)
    (hfinite : {x : Fin n → K | ∀ j, (q j).eval₂ φ x = 0}.Finite) :
    (zeroLocus K (ProjectiveNullstellensatz.generated (MacaulayFiniteFiber.originalSystem
      (rows q d v) (affineCoefficientMap φ) affineChart))).Finite := by
  apply (hfinite.image (fun x : Fin n → K => (Fin.cons ((∑ i, φ (v i) * x i)) x : Fin (n + 1) → K))).subset
  intro z hz
  have hrows : ∀ j, MvPolynomial.eval z (MacaulayFiniteFiber.originalSystem
      (rows q d v) (affineCoefficientMap φ) affineChart j) = 0 := by
    simpa only [ProjectiveNullstellensatz.zeroLocus_generated, mem_ofPred_eq] using hz
  have hhead := hrows 0
  have he := eval_affineSystem φ q d hD v z
  have hp : z 0 = (∑ i, φ (v i) * z i.succ) := by
    rw [congrFun he 0] at hhead
    exact sub_eq_zero.mp hhead
  refine ⟨fun i => z i.succ, ?_, ?_⟩
  · intro j
    have hj := hrows j.succ
    rwa [congrFun he j.succ] at hj
  · change Fin.cons ((∑ i, φ (v i) * z i.succ)) (fun i => z i.succ) = z
    rw [← hp]
    exact Fin.cons_self_tail z

/-- The bounded polynomial annihilates every root of a finite affine zero
set over an algebraically closed field. No simplicity assumption is used. -/
theorem eval_eq_zero_of_finite [IsDomain R] [IsAlgClosed K] (φ : R →+* K)
    (q : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ)
    (hD : ∀ j, (q j).totalDegree ≤ d j) (hd : ∀ j, 0 < d j) (v : Fin n → R) (W : ℕ)
    (hW : Macaulay.level (degrees d) < 2 ^ W)
    (hfinite : {x : Fin n → K | ∀ j, (q j).eval₂ φ x = 0}.Finite)
    (x : Fin n → K) (hroot : ∀ j, (q j).eval₂ φ x = 0) :
    (polynomial q d v W).eval₂ φ ((∑ i, φ (v i) * x i)) = 0 := by
  let z : Fin (n + 1) → K := Fin.cons ((∑ i, φ (v i) * x i)) x
  have hz : z ∈ zeroLocus K (ProjectiveNullstellensatz.generated (MacaulayFiniteFiber.originalSystem
      (rows q d v) (affineCoefficientMap φ) affineChart)) := by
    rw [ProjectiveNullstellensatz.zeroLocus_generated]
    intro j
    have he := congrFun (eval_affineSystem φ q d hD v z) j
    rw [he]
    refine Fin.cases (by simp [z]) (fun j => ?_) j
    exact hroot j
  have hnz (a : Fin (n + 1) → K) : ∃ j, MvPolynomial.eval a (affineChart (K := K) j) ≠ 0 := by
    refine ⟨layout none, ?_⟩
    simp [affineChart]
  have he := MacaulayFiniteFiber.numerator_trailingCoeff_eval_eq_zero_of_finite_fiber
    (rows q d v) (degrees d) W
    (MacaulayUniversal.degree_lt_width _ _ (degrees_pos d hd) hW) hW
    (homogeneous q d v) (degrees_pos d hd) (affineCoefficientMap φ) affineChart hnz
    (affineSystem_finite φ q d hD v hfinite) z hz
  rw [eval_affineCoefficientMap] at he
  change Polynomial.eval₂ φ ((∑ i, φ (v i) * x i))
    (Macaulay.characteristicNumerator (rows q d v) (degrees d) W).trailingCoeff = 0 at he
  change Polynomial.eval₂ φ ((∑ i, φ (v i) * x i))
    (MacaulayLowestBounds.polynomial (rows q d v) (degrees d) W) = 0
  rw [MacaulayLowestBounds.polynomial_eq]
  exact he

end LeanCanny.Geometry.LinearProjectionEliminant
