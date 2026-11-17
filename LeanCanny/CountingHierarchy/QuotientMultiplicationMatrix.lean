/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.PurePowerTrace

/-! # The actual normal-basis multiplication matrix -/

public section

namespace LeanCanny.CountingHierarchy.PurePowerResidue

open MvPolynomial
open scoped Classical

variable {S : Type*} [CommRing S] {n ell : ℕ}

/-- Multiplication in the proved normal-monomial basis, as an algebra hom.
 This matrix is a mathematical specification, never an input to an evaluator. -/
@[expose] noncomputable def multiplicationMatrix (hell : 1 ≤ ell)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree < ell) :
    MvPolynomial (Fin n) S →ₐ[S] Matrix (NormalIndex n ell) (NormalIndex n ell) S :=
  (Algebra.leftMulMatrix (normalBasis hell r hr)).comp (projection ell r)

/-- Equal presentations have equal characteristic polynomials; relation
 degree proofs do not affect the chosen normal basis. -/
theorem multiplicationMatrix_charpoly_congr (hell : 1 ≤ ell)
    (r r' : Fin n → MvPolynomial (Fin n) S)
    (hr : ∀ i, (r i).totalDegree < ell) (hr' : ∀ i, (r' i).totalDegree < ell)
    (v v' : MvPolynomial (Fin n) S) (heq : r = r') (hv : v = v') :
    (multiplicationMatrix hell r hr v).charpoly =
      (multiplicationMatrix hell r' hr' v').charpoly := by
  subst r'
  subst v'
  rfl

theorem multiplicationMatrix_trace_pow (d : ℕ) (hd : 1 ≤ d)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree ≤ d)
    (v : MvPolynomial (Fin n) S) (k : ℕ) :
    ((multiplicationMatrix (by omega : 1 ≤ d + 1) r
      (fun i => (hr i).trans_lt (Nat.lt_succ_self d)) v) ^ k).trace =
        residue (d + 1) r (v ^ k * jacobian (d + 1) r) := by
  rw [← map_pow]
  change (Algebra.leftMulMatrix (normalBasis _ r _) (projection (d + 1) r (v ^ k))).trace = _
  rw [← Algebra.trace_eq_matrix_trace]
  exact trace_eq_residue d hd r hr (v ^ k)

end LeanCanny.CountingHierarchy.PurePowerResidue
