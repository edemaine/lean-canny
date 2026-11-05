/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.ScaledPolynomialQuotient
/-! # The exact top coefficient of the division-free Cramer quotient

Replacing the final column preserves upper triangularity. This reads only
the dividend's top coefficient and a power of the divisor's leading slot.
-/
@[expose] public section
namespace LeanCanny.Algebra.ScaledPolynomialQuotient
open Polynomial Matrix
open scoped Classical BigOperators
variable {R : Type*} [CommRing R]

theorem top_coefficient (p g : Polynomial R) (d L : ℕ) (hp : p.natDegree ≤ d) :
    (quotient p g d L).coeff L = p.coeff d ^ L * g.coeff (d + L) := by
  let A := (matrix p d L).updateCol (Fin.last L) (input g d L)
  have HU : A.IsUpperTriangular := by
    intro i j hji
    have HJI : j.val < i.val := hji
    have HN : j ≠ Fin.last L := by
      intro HE
      have HI := i.isLt
      have HJ := congrArg Fin.val HE
      simp only [Fin.val_last] at HJ
      omega
    rw [show A i j = _ from selected_entry p g d L (Fin.last L) i j,
      ite_eq_right HN, ite_eq_left (by omega)]
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (hp.trans_lt (by omega))
  have HC (i : Fin L) : A i.castSucc i.castSucc = p.coeff d := by
    have HN : i.castSucc ≠ Fin.last L := by
      intro HE
      have HI := i.isLt
      have HJ := congrArg Fin.val HE
      simp only [Fin.val_castSucc, Fin.val_last] at HJ
      omega
    rw [show A i.castSucc i.castSucc = _ from selected_entry p g d L (Fin.last L) i.castSucc i.castSucc,
      ite_eq_right HN, ite_eq_left (by simp only [Fin.val_castSucc]; omega), Nat.add_sub_cancel]
  have HL : A (Fin.last L) (Fin.last L) = g.coeff (d + L) := by
    rw [show A (Fin.last L) (Fin.last L) = _ from selected_entry p g d L (Fin.last L) (Fin.last L) (Fin.last L),
      ite_eq_left rfl]
    rfl
  have HD : A.det = p.coeff d ^ L * g.coeff (d + L) := by
    rw [Matrix.det_of_isUpperTriangular HU, Fin.prod_univ_castSucc]
    simp only [HC, HL, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [quotient_coeff, dite_eq_left (Nat.lt_succ_self L)]
  exact HD

end LeanCanny.Algebra.ScaledPolynomialQuotient
