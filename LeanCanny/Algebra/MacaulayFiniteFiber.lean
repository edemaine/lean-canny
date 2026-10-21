/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FiniteFiberLowestCoefficient
public import LeanCanny.Algebra.MacaulayProjectiveRoots
/-! # Lowest quotient coefficients vanish on finite affine systems

Represent coefficient parameters and projective coordinates by polynomials
in as many affine unknowns as there are homogeneous equations. If the
unshifted affine system has finitely many roots over an algebraically closed
field, the lowest characteristic quotient coefficient vanishes at every
root. The proof uses radical saturation and covers singular roots, with no
Jacobian or analytic root-family hypothesis. Solutions at infinity may form
infinite components because finiteness is required only in this affine model.
-/

@[expose] public section

namespace LeanCanny.Algebra.MacaulayFiniteFiber

open MvPolynomial
open scoped Classical
variable {n : ℕ} {R K : Type*} [CommRing R] [Field K] [IsAlgClosed K]

noncomputable def originalSystem (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R)
    (φ : R →+* MvPolynomial (Fin (n + 1)) K) (x : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K) :
    Fin (n + 1) → MvPolynomial (Fin (n + 1)) K := fun i => MvPolynomial.eval₂ φ x (p i)

noncomputable def shiftedSystem (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R) (d : Fin (n + 1) → ℕ)
    (φ : R →+* MvPolynomial (Fin (n + 1)) K) (x : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K) :
    Fin (n + 1) → MvPolynomial (Fin (n + 1 + 1)) K := fun i =>
  FiniteFiberLowestCoefficient.encode (Polynomial.C (originalSystem p φ x i) - Polynomial.X * Polynomial.C (x i ^ d i))

omit [IsAlgClosed K] in
theorem eval_shiftedSystem (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R) (d : Fin (n + 1) → ℕ)
    (φ : R →+* MvPolynomial (Fin (n + 1)) K) (x : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (s : K) (z : Fin (n + 1) → K) (i : Fin (n + 1)) :
    MvPolynomial.eval (Fin.cons s z) (shiftedSystem p d φ x i) =
      MvPolynomial.eval₂ ((MvPolynomial.eval z).comp φ) (fun j => MvPolynomial.eval z (x j)) (p i) -
        s * MvPolynomial.eval z (x i) ^ d i := by
  rw [shiftedSystem, FiniteFiberLowestCoefficient.eval_encode]
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_C, Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_pow,
    originalSystem, MvPolynomial.eval_eval₂, map_pow]

theorem trailingCoeff_eval_eq_zero_of_finite_fiber
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R) (d : Fin (n + 1) → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (hW : Macaulay.level d < 2 ^ W)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i)
    (φ : R →+* MvPolynomial (Fin (n + 1)) K) (x : Fin (n + 1) → MvPolynomial (Fin (n + 1)) K)
    (hnz : ∀ z : Fin (n + 1) → K, ∃ j, MvPolynomial.eval z (x j) ≠ 0)
    (hfinite : (zeroLocus K (ProjectiveNullstellensatz.generated (originalSystem p φ x))).Finite)
    (z : Fin (n + 1) → K) (hz : z ∈ zeroLocus K (ProjectiveNullstellensatz.generated (originalSystem p φ x))) :
    ((MvPolynomial.eval z).comp φ) (Macaulay.characteristicQuotient p d W).trailingCoeff = 0 := by
  let Q := Macaulay.characteristicQuotient p d W
  let q := Q.map φ
  have hk : ∀ j < Q.natTrailingDegree, q.coeff j = 0 := by
    intro j hj
    rw [Polynomial.coeff_map, Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hj, map_zero]
  have hS : {z : Fin (n + 1) → K | ∀ i, MvPolynomial.eval (Fin.cons 0 z) (shiftedSystem p d φ x i) = 0} =
      zeroLocus K (ProjectiveNullstellensatz.generated (originalSystem p φ x)) := by
    rw [ProjectiveNullstellensatz.zeroLocus_generated]
    ext a
    simp only [Set.mem_ofPred_eq, eval_shiftedSystem, zero_mul, sub_zero, originalSystem, MvPolynomial.eval_eval₂]
  have hf := FiniteFiberLowestCoefficient.finite_fiber_of_finite_zero_set (shiftedSystem p d φ x) (hS.symm ▸ hfinite)
  have hvanish : ∀ a ∈ zeroLocus K (ProjectiveNullstellensatz.generated (shiftedSystem p d φ x)),
      MvPolynomial.eval a (FiniteFiberLowestCoefficient.encode q) = 0 := by
    intro a ha
    let s := a 0
    let t : Fin (n + 1) → K := fun j => a j.succ
    have hc : Fin.cons s t = a := Fin.cons_self_tail a
    have hr (i : Fin (n + 1)) : MvPolynomial.eval₂ ((MvPolynomial.eval t).comp φ)
        (fun j => MvPolynomial.eval t (x j)) (p i) = s * MvPolynomial.eval t (x i) ^ d i := by
      have he := ha (shiftedSystem p d φ x i) (Ideal.subset_span (Set.mem_range_self i))
      change MvPolynomial.eval a (shiftedSystem p d φ x i) = 0 at he
      rw [← hc, eval_shiftedSystem] at he
      exact sub_eq_zero.mp he
    have he := MacaulayUniversal.eval_map_characteristicQuotient_eq_zero_of_common_root
      ((MvPolynomial.eval t).comp φ) d W hdegree hW p hp hd s (fun j => MvPolynomial.eval t (x j)) hr (hnz t)
    rw [Polynomial.eval_map] at he
    rw [← hc, FiniteFiberLowestCoefficient.eval_encode, Polynomial.eval₂_map]
    exact he
  have hz' : Fin.cons 0 z ∈ zeroLocus K (ProjectiveNullstellensatz.generated (shiftedSystem p d φ x)) := by
    rw [ProjectiveNullstellensatz.zeroLocus_generated]
    change z ∈ {a : Fin (n + 1) → K | ∀ i, MvPolynomial.eval (Fin.cons 0 a) (shiftedSystem p d φ x i) = 0}
    rw [hS]
    exact hz
  have he := FiniteFiberLowestCoefficient.coefficient_vanishes_of_finite_fiber
    (shiftedSystem p d φ x) q Q.natTrailingDegree hk hf hvanish z hz'
  simpa only [q, Q, Polynomial.coeff_map, Polynomial.trailingCoeff, RingHom.comp_apply] using he

end LeanCanny.Algebra.MacaulayFiniteFiber
