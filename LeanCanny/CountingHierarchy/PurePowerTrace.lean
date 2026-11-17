/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.PurePowerKernel
public import LeanCanny.CountingHierarchy.PurePowerBasis
public import LeanCanny.CountingHierarchy.PurePowerResidueExpansion
public import LeanCanny.CountingHierarchy.ReproducingTrace

/-! # Multiplication traces as finite polynomial residues -/

public section

namespace LeanCanny.CountingHierarchy.PurePowerResidue

open MvPolynomial Module
open scoped Classical BigOperators

set_option backward.isDefEq.respectTransparency false

variable {S : Type*} [CommRing S] {n ell : ℕ}

theorem eval_map_projection (r : Fin n → MvPolynomial (Fin n) S)
    (q : MvPolynomial (Fin n) S) :
    eval (fun i => projection ell r (X i))
      (q.map (algebraMap S (QuotientAlgebra ell r))) = projection ell r q := by
  rw [eval_map]
  have hh : eval₂Hom (algebraMap S (QuotientAlgebra ell r))
      (fun i => projection ell r (X i)) = (projection ell r).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      rw [eval₂Hom_C]
      exact ((projection ell r).commutes a).symm
    · intro i
      rw [eval₂Hom_X']
      rfl
  exact congrArg (fun f : MvPolynomial (Fin n) S →+* QuotientAlgebra ell r => f q) hh

/-- The Jacobian polynomial of the actual pure-power relations. -/
@[expose] noncomputable def jacobian (ell : ℕ)
    (r : Fin n → MvPolynomial (Fin n) S) : MvPolynomial (Fin n) S :=
  Matrix.det (fun i j => pderiv j (X i ^ ell - r i))

/-- The Scheja--Storch trace identity, proved over an arbitrary
 commutative coefficient ring using a finite coefficient functional. -/
theorem trace_eq_residue (d : ℕ) (hd : 1 ≤ d)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree ≤ d)
    (v : MvPolynomial (Fin n) S) :
    Algebra.trace S (QuotientAlgebra (d + 1) r) (projection (d + 1) r v) =
      residue (d + 1) r (v * jacobian (d + 1) r) := by
  let A := QuotientAlgebra (d + 1) r
  let φ : S →+* A := algebraMap S A
  let π := projection (d + 1) r
  let x : Fin n → A := fun i => π (X i)
  let r' : Fin n → MvPolynomial (Fin n) A := fun i => (r i).map φ
  have hell : 1 ≤ d + 1 := by omega
  have hrS (i : Fin n) : (r i).totalDegree < d + 1 := by have := hr i; omega
  have hrA (i : Fin n) : (r' i).totalDegree ≤ d := (map_degree_le φ (r i)).trans (hr i)
  have heval (q : MvPolynomial (Fin n) S) : eval x (q.map φ) = π q :=
    eval_map_projection r q
  have hx (i : Fin n) : eval x (r' i) = x i ^ (d + 1) := by
    rw [heval]
    exact (projection_X_pow (d + 1) r i).symm
  obtain ⟨K, hk, hdiag⟩ := purePower_reproducing_kernel x d hd r' hrA hx
  let L := quotientFunctional hell r hrS
  let m : (Fin n →₀ ℕ) → A := fun e => π (monomial e 1)
  let c : (Fin n →₀ ℕ) → A := fun e => K.coeff e
  have hrep (z : A) : ∑ e ∈ K.support, L (m e * z) • c e = z := by
    obtain ⟨q, rfl⟩ := projection_surjective (d + 1) r z
    have hsum := (residue_kernel_expansion φ hell r hrS K q).symm.trans (hk (q.map φ))
    rw [heval] at hsum
    have hterm (e : Fin n →₀ ℕ) :
        L (m e * π q) • c e = K.coeff e * φ (residue (d + 1) r (monomial e 1 * q)) := by
      change quotientFunctional hell r hrS
        (projection (d + 1) r (monomial e 1) * projection (d + 1) r q) • K.coeff e = _
      rw [← map_mul, quotientFunctional_projection]
      exact (Algebra.smul_def (residue (d + 1) r (monomial e 1 * q))
        (K.coeff e)).trans (mul_comm _ _)
    rw [Finset.sum_congr rfl (fun e _ => hterm e)]
    exact hsum
  have hJac : Matrix.det (fun i j => eval x (pderiv j (X i ^ (d + 1) - r' i))) =
      π (jacobian (d + 1) r) := by
    rw [jacobian, π.map_det]
    congr 1
    ext i j
    have heq : X i ^ (d + 1) - r' i = (X i ^ (d + 1) - r i).map φ := by
      simp only [map_sub, map_pow, map_X, r']
    rw [heq, pderiv_map, heval]
    rfl
  have heuler : (∑ e ∈ K.support, c e * m e) = π (jacobian (d + 1) r) := by
    calc
      _ = eval x K := by
        conv_rhs => rw [K.as_sum]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro e _
        have hm := heval (monomial e 1)
        simp only [map_monomial, map_one] at hm
        rw [show m e = eval x (monomial e 1) from hm.symm]
        simp only [c, eval_monomial, one_mul]
      _ = _ := hdiag.trans hJac
  calc
    _ = L (π v * ∑ e ∈ K.support, c e * m e) :=
      trace_eq_of_reproducing (normalBasis hell r hrS) L K.support c m hrep (π v)
    _ = _ := by rw [heuler, ← map_mul, quotientFunctional_projection]

end LeanCanny.CountingHierarchy.PurePowerResidue
