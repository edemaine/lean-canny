/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PaddedIntegralParameterFinMatrix

/-! # Reading literal scalar equations from their creating companions

The last block column of the actual padded companion determines every lower
coefficient of the monic scalar equation. Column zero in the old basis reads
the canonical integer coefficient, including singular and padded branches.
-/

@[expose] public section
namespace LeanCanny.Algebra.PaddedIntegralParameterExtension
open IntegralCoordinateBasis FixedWidthPolynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {A : Type*} [CommRing A] [Nontrivial A] {m B : ℕ}

def lastDigit (B : ℕ) : Fin (2 ^ B) := ⟨2 ^ B - 1, by have := Nat.two_pow_pos B; omega⟩

theorem pairIndex_value (r : Fin (count m B)) (i : Fin (2 ^ B)) :
    (pairIndex m B (r,i)).val = i.val + 2 ^ B * r.val := rfl

theorem equation_coefficient_companion (b : IntegralCoordinateBasis A m (2 ^ B))
    (p : Polynomial A) (d : ℕ) (r : Fin (count m B)) (i : Fin (2 ^ B)) :
    ((equation b p d).coeff i.val).coeff (vector m B r) =
      -Algebra.leftMulMatrix (coordinateBasis b p d).finBasis (AdjoinRoot.root _)
        (pairIndex m B (r, i)) (pairIndex m B (zeroFin m B, lastDigit B)) := by
  rw [equation, polynomial_coefficient, coefficient_finMatrix]
  change _ = -Algebra.leftMulMatrix (b.step _ _ _).finBasis _ _ _
  rw [finBasis_root_matrix]
  have H : ¬(lastDigit B).val + 1 < 2 ^ B := by
    dsimp only [lastDigit]
    have := Nat.two_pow_pos B
    omega
  rw [ite_eq_right H, neg_neg]

theorem equation_coefficient_top (b : IntegralCoordinateBasis A m (2 ^ B))
    (p : Polynomial A) (d : ℕ) :
    (equation b p d).coeff (2 ^ B) = 1 := by
  have H := equation_monic b p d (Nat.two_pow_pos B)
  calc
    (equation b p d).coeff (2 ^ B) = (equation b p d).coeff (equation b p d).natDegree :=
      congrArg (fun k => (equation b p d).coeff k) H.2.symm
    _ = 1 := by rw [Polynomial.coeff_natDegree, H.1.leadingCoeff]

theorem equation_coefficient_above (b : IntegralCoordinateBasis A m (2 ^ B))
    (p : Polynomial A) (d k : ℕ) (hk : 2 ^ B < k) :
    (equation b p d).coeff k = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  rw [(equation_monic b p d (Nat.two_pow_pos B)).2]
  exact hk

omit [Nontrivial A] in
theorem equation_coefficient_outside (b : IntegralCoordinateBasis A m (2 ^ B))
    (p : Polynomial A) (d k : ℕ) (v : Fin m →₀ ℕ)
    (hv : ∃ j, 2 ^ B ≤ v j) : ((equation b p d).coeff k).coeff v = 0 := by
  rw [equation, polynomial_coefficient]
  apply MvPolynomial.notMem_support_iff.mp
  intro HS
  obtain ⟨j, hj⟩ := hv
  exact Nat.not_lt_of_ge hj (b.representative_support _ v HS j)

end LeanCanny.Algebra.PaddedIntegralParameterExtension
