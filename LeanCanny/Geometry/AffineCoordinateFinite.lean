/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.AffineCoordinateEliminant
public import LeanCanny.Algebra.MacaulayFiniteFiber

/-! # Bounded coordinate equations on finite singular affine fibers

The added coordinate equation identifies the augmented affine zero set with
the graph of a coordinate on the original zero set. Finiteness therefore
passes to the affine model of the homogeneous equations. Algebraic finite-fiber
saturation makes the same bounded numerator polynomial vanish at every root,
including singular roots. Projective zeros at infinity remain allowed.
-/

@[expose] public section

namespace LeanCanny.Geometry.AffineCoordinateEliminant
open MvPolynomial Set
open LeanCanny.Algebra AffineCoordinateSystem
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} {R K : Type*} [CommRing R] [Field K]

noncomputable def affineCoefficientMap (φ : R →+* K) :
    Polynomial R →+* MvPolynomial (Fin (n + 1)) K :=
  Polynomial.eval₂RingHom (MvPolynomial.C.comp φ) (MvPolynomial.X 0)

noncomputable def affineChart : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K :=
  fun j => (layout.symm j).elim 1 (fun i => MvPolynomial.X i.succ)

theorem eval_affineCoefficientMap (φ : R →+* K) (z : Fin (n + 1) → K) :
    (MvPolynomial.eval z).comp (affineCoefficientMap φ) = Polynomial.eval₂RingHom φ (z 0) := by
  ext <;> simp [affineCoefficientMap]

theorem eval_affineChart (z : Fin (n + 1) → K) (j : Fin (n + 1)) :
    MvPolynomial.eval z (affineChart (K := K) j) = (layout.symm j).elim 1 (fun i => z i.succ) := by
  cases hj : layout.symm j <;> simp [affineChart, hj]

theorem eval_affineSystem (φ : R →+* K) (q : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (hD : ∀ j, (q j).totalDegree ≤ d j) (coordinate : Fin n)
    (z : Fin (n + 1) → K) :
    (fun j => MvPolynomial.eval z (MacaulayFiniteFiber.originalSystem (rows q d coordinate)
      (affineCoefficientMap φ) affineChart j)) =
      Fin.cons (z 0 - z coordinate.succ) (fun j => (q j).eval₂ φ (fun i => z i.succ)) := by
  have he : (fun j => MvPolynomial.eval z (affineChart (K := K) j)) =
      (fun j => (layout.symm j).elim 1 (fun i => z i.succ)) := funext (eval_affineChart z)
  simp only [MacaulayFiniteFiber.originalSystem, MvPolynomial.eval_eval₂,
    eval_affineCoefficientMap, he]
  exact AffineCoordinateSystem.eval_rows φ q d hD coordinate (z 0) (fun i => z i.succ)

theorem affineSystem_finite (φ : R →+* K) (q : Fin n → MvPolynomial (Fin n) R)
    (d : Fin n → ℕ) (hD : ∀ j, (q j).totalDegree ≤ d j) (coordinate : Fin n)
    (hfinite : {x : Fin n → K | ∀ j, (q j).eval₂ φ x = 0}.Finite) :
    (zeroLocus K (ProjectiveNullstellensatz.generated (MacaulayFiniteFiber.originalSystem
      (rows q d coordinate) (affineCoefficientMap φ) affineChart))).Finite := by
  apply (hfinite.image (fun x : Fin n → K => (Fin.cons (x coordinate) x : Fin (n + 1) → K))).subset
  intro z hz
  have hrows : ∀ j, MvPolynomial.eval z (MacaulayFiniteFiber.originalSystem
      (rows q d coordinate) (affineCoefficientMap φ) affineChart j) = 0 := by
    simpa only [ProjectiveNullstellensatz.zeroLocus_generated, mem_ofPred_eq] using hz
  have hhead := hrows 0
  have he := eval_affineSystem φ q d hD coordinate z
  have hp : z 0 = z coordinate.succ := by
    rw [congrFun he 0] at hhead
    exact sub_eq_zero.mp hhead
  refine ⟨fun i => z i.succ, ?_, ?_⟩
  · intro j
    have hj := hrows j.succ
    rwa [congrFun he j.succ] at hj
  · change Fin.cons (z coordinate.succ) (fun i => z i.succ) = z
    rw [← hp]
    exact Fin.cons_self_tail z

/-- The bounded polynomial annihilates every root of a finite affine zero
set over an algebraically closed field. No simplicity assumption is used. -/
theorem eval_eq_zero_of_finite [IsDomain R] [IsAlgClosed K] (φ : R →+* K)
    (q : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ)
    (hD : ∀ j, (q j).totalDegree ≤ d j) (hd : ∀ j, 0 < d j) (coordinate : Fin n) (W : ℕ)
    (hW : Macaulay.level (degrees d) < 2 ^ W)
    (hfinite : {x : Fin n → K | ∀ j, (q j).eval₂ φ x = 0}.Finite)
    (x : Fin n → K) (hroot : ∀ j, (q j).eval₂ φ x = 0) :
    (polynomial q d coordinate W).eval₂ φ (x coordinate) = 0 := by
  let z : Fin (n + 1) → K := Fin.cons (x coordinate) x
  have hz : z ∈ zeroLocus K (ProjectiveNullstellensatz.generated (MacaulayFiniteFiber.originalSystem
      (rows q d coordinate) (affineCoefficientMap φ) affineChart)) := by
    rw [ProjectiveNullstellensatz.zeroLocus_generated]
    intro j
    have he := congrFun (eval_affineSystem φ q d hD coordinate z) j
    rw [he]
    refine Fin.cases (by simp [z]) (fun j => ?_) j
    exact hroot j
  have hnz (a : Fin (n + 1) → K) : ∃ j, MvPolynomial.eval a (affineChart (K := K) j) ≠ 0 := by
    refine ⟨layout none, ?_⟩
    simp [affineChart]
  have he := MacaulayFiniteFiber.numerator_trailingCoeff_eval_eq_zero_of_finite_fiber
    (rows q d coordinate) (degrees d) W
    (MacaulayUniversal.degree_lt_width _ _ (degrees_pos d hd) hW) hW
    (homogeneous q d coordinate) (degrees_pos d hd) (affineCoefficientMap φ) affineChart hnz
    (affineSystem_finite φ q d hD coordinate hfinite) z hz
  rw [eval_affineCoefficientMap] at he
  change Polynomial.eval₂ φ (x coordinate)
    (Macaulay.characteristicNumerator (rows q d coordinate) (degrees d) W).trailingCoeff = 0 at he
  change Polynomial.eval₂ φ (x coordinate)
    (MacaulayLowestBounds.polynomial (rows q d coordinate) (degrees d) W) = 0
  rw [MacaulayLowestBounds.polynomial_eq]
  exact he

/-- Real roots inherit the algebraic conclusion from a finite zero set over
an algebraically closed extension. Singular real roots are included. -/
theorem eval_eq_zero_of_finite_extension [IsDomain R]
    {L : Type*} [Field L] [IsAlgClosed L] [Algebra ℝ L] (φ : R →+* ℝ)
    (q : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ)
    (hD : ∀ j, (q j).totalDegree ≤ d j) (hd : ∀ j, 0 < d j) (coordinate : Fin n) (W : ℕ)
    (hW : Macaulay.level (degrees d) < 2 ^ W)
    (hfinite : {x : Fin n → L | ∀ j, (q j).eval₂ ((algebraMap ℝ L).comp φ) x = 0}.Finite)
    (x : Fin n → ℝ) (hroot : ∀ j, (q j).eval₂ φ x = 0) :
    (polynomial q d coordinate W).eval₂ φ (x coordinate) = 0 := by
  let ψ := (algebraMap ℝ L).comp φ
  let y : Fin n → L := (algebraMap ℝ L) ∘ x
  have hy (j : Fin n) : (q j).eval₂ ψ y = 0 := by
    change (q j).eval₂ ((algebraMap ℝ L).comp φ) ((algebraMap ℝ L) ∘ x) = 0
    rw [← MvPolynomial.eval₂_comp_left, hroot j, map_zero]
  have he := eval_eq_zero_of_finite ψ q d hD hd coordinate W hW hfinite y hy
  have hmap : (algebraMap ℝ L).comp (Polynomial.eval₂RingHom φ (x coordinate)) =
      Polynomial.eval₂RingHom ψ (algebraMap ℝ L (x coordinate)) := by
    ext <;> simp [ψ]
  apply (algebraMap ℝ L).injective
  rw [map_zero]
  change ((algebraMap ℝ L).comp (Polynomial.eval₂RingHom φ (x coordinate)))
    (polynomial q d coordinate W) = 0
  rw [hmap]
  exact he

end LeanCanny.Geometry.AffineCoordinateEliminant
