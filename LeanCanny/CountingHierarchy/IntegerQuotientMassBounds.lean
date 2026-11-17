/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.QuotientMassBounds
public import LeanCanny.CountingHierarchy.QuotientCharacteristicRingSpecialization
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! # Log-mass bounds for integer quotient characteristic polynomials and norms -/

public section

namespace LeanCanny.CountingHierarchy

open Polynomial MvPolynomial PurePowerResidue LeanCanny.Algebra
open scoped BigOperators Classical

@[simp] theorem nestedMass_map_C (p : Polynomial ℤ) :
    NestedMass.mass (p.map Polynomial.C) = coefficientMass p := by
  simp only [NestedMass.mass, Polynomial.sum_def, Polynomial.support_map_of_injective _
    Polynomial.C_injective, Polynomial.coeff_map, coefficientMass_C]
  rfl

@[expose] def quotientCharMassExponent (n d Ω bv br : ℕ) : ℕ :=
  let D := (d + 1) ^ n
  traceMassExponent n (D * Ω + n * d) D bv br
    (n.size * n + n * ((d + 1).size + br + 1)) * D + (D + 1).size

/-- The integer budget follows by embedding constants in the parameter ring.
No normal-form matrix entries or determinant expansion are assumed small. -/
theorem multiplicationMatrix_charpoly_mass_le {n : ℕ} (d : ℕ) (hd : 1 ≤ d)
    (r : Fin n → MvPolynomial (Fin n) ℤ) (hr : ∀ i, (r i).totalDegree ≤ d)
    (v : MvPolynomial (Fin n) ℤ) (Ω bv br : ℕ)
    (hvdeg : v.totalDegree ≤ Ω) (hv : MvMass.mass v ≤ 2 ^ bv)
    (hM : ∀ i, MvMass.mass (r i) ≤ 2 ^ br) :
    coefficientMass ((multiplicationMatrix (by omega : 1 ≤ d + 1) r
      (fun i => (hr i).trans_lt (Nat.lt_succ_self d)) v).charpoly) ≤
        2 ^ quotientCharMassExponent n d Ω bv br := by
  have hm := multiplicationMatrix_charpoly_map_charZero
    (Polynomial.C : ℤ →+* Polynomial ℤ) d hd r hr v
  have hb := multiplicationMatrix_charpoly_nestedMass_le d hd
    (fun i => (r i).map Polynomial.C)
    (fun i => (map_degree_le Polynomial.C _).trans (hr i))
    (v.map Polynomial.C) Ω bv br ((map_degree_le Polynomial.C v).trans hvdeg)
    (by simpa only [ParameterMass.map_C] using hv)
    (fun i => by simpa only [ParameterMass.map_C] using hM i)
  rw [← hm, nestedMass_map_C] at hb
  exact hb

lemma determinant_natAbs_le_charpoly_mass {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℤ) : M.det.natAbs ≤ coefficientMass M.charpoly := by
  rw [Matrix.det_eq_sign_charpoly_coeff]
  simpa only [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_one,
    one_pow, one_mul] using coeff_natAbs_le_coefficientMass M.charpoly 0

/-- The actual integer quotient norm has the same short logarithmic budget. -/
theorem multiplicationMatrix_det_natAbs_le {n : ℕ} (d : ℕ) (hd : 1 ≤ d)
    (r : Fin n → MvPolynomial (Fin n) ℤ) (hr : ∀ i, (r i).totalDegree ≤ d)
    (v : MvPolynomial (Fin n) ℤ) (Ω bv br : ℕ)
    (hvdeg : v.totalDegree ≤ Ω) (hv : MvMass.mass v ≤ 2 ^ bv)
    (hM : ∀ i, MvMass.mass (r i) ≤ 2 ^ br) :
    (multiplicationMatrix (by omega : 1 ≤ d + 1) r
      (fun i => (hr i).trans_lt (Nat.lt_succ_self d)) v).det.natAbs ≤
        2 ^ quotientCharMassExponent n d Ω bv br :=
  (determinant_natAbs_le_charpoly_mass _).trans
    (multiplicationMatrix_charpoly_mass_le d hd r hr v Ω bv br hvdeg hv hM)

end LeanCanny.CountingHierarchy
