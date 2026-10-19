/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.Subresultant
public import LeanCanny.Algebra.IntegerModular

/-!
# Degree and magnitude bounds for subresultant coefficients

The minor has `m-k` columns from `g` and `n-k` columns from `f`. The existing
column-wise determinant estimates therefore apply with these reduced counts.
For polynomial coefficient rings they bound each parameter coefficient without
constructing a subresultant polynomial or any coefficient vector.
-/

@[expose] public section

namespace LeanCanny.Algebra.Subresultant
open Polynomial

def budget (m n k bf bg : ℕ) : ℕ :=
  ((m - k) + (n - k)).size * ((m - k) + (n - k)) + (m - k) * bg + (n - k) * bf + 1

theorem minor_natDegree_le {R : Type*} [CommRing R] (f g : Polynomial (Polynomial R))
    (m n k r Df Dg : ℕ) (hf : ∀ i, (f.coeff i).natDegree ≤ Df) (hg : ∀ i, (g.coeff i).natDegree ≤ Dg) :
    (minor f g m n k r).det.natDegree ≤ (m - k) * Dg + (n - k) * Df := by
  have hcol : ∀ i j : Fin ((m - k) + (n - k)),
      (minor f g m n k r i j).natDegree ≤ j.addCases (fun _ => Dg) (fun _ => Df) := by
    intro i j
    induction j using Fin.addCases <;> simp only [minor, Matrix.of_apply, Fin.addCases_left, Fin.addCases_right, band]
    · split_ifs
      · exact hg _
      · simp
    · split_ifs
      · exact hf _
      · simp
  have h := det_natDegree_le (minor f g m n k r) (fun j => j.addCases (fun _ => Dg) (fun _ => Df)) hcol
  simpa only [Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right, Fin.sum_const, smul_eq_mul] using h

theorem minor_det_size_le (f g : Polynomial ℤ) (m n k r bf bg : ℕ)
    (hf : ∀ i, (f.coeff i).natAbs ≤ 2 ^ bf) (hg : ∀ i, (g.coeff i).natAbs ≤ 2 ^ bg) :
    (minor f g m n k r).det.natAbs.size ≤ budget m n k bf bg := by
  have hcol : ∀ i j : Fin ((m - k) + (n - k)),
      (minor f g m n k r i j).natAbs ≤ 2 ^ j.addCases (fun _ => bg) (fun _ => bf) := by
    intro i j
    induction j using Fin.addCases <;> simp only [minor, Matrix.of_apply, Fin.addCases_left, Fin.addCases_right, band]
    · split_ifs
      · exact hg _
      · exact Nat.zero_le _
    · split_ifs
      · exact hf _
      · exact Nat.zero_le _
  have h := IntegerModular.det_natAbs_size_le (minor f g m n k r)
    (fun j => j.addCases (fun _ => bg) (fun _ => bf)) hcol
  simpa only [budget, Fintype.card_fin, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right,
    Fin.sum_const, smul_eq_mul, Nat.add_assoc] using h

theorem minor_det_coeff_size_le (f g : Polynomial (Polynomial ℤ)) (m n k r bf bg d : ℕ)
    (hf : ∀ i, coefficientMass (f.coeff i) ≤ 2 ^ bf) (hg : ∀ i, coefficientMass (g.coeff i) ≤ 2 ^ bg) :
    ((minor f g m n k r).det.coeff d).natAbs.size ≤ budget m n k bf bg := by
  have hcol : ∀ i j : Fin ((m - k) + (n - k)),
      coefficientMass (minor f g m n k r i j) ≤ 2 ^ j.addCases (fun _ => bg) (fun _ => bf) := by
    intro i j
    induction j using Fin.addCases <;> simp only [minor, Matrix.of_apply, Fin.addCases_left, Fin.addCases_right, band]
    · split_ifs
      · exact hg _
      · simp
    · split_ifs
      · exact hf _
      · simp
  have h := det_coeff_size_le (minor f g m n k r) (fun j => j.addCases (fun _ => bg) (fun _ => bf)) hcol d
  simpa only [budget, Fintype.card_fin, Fin.sum_univ_add, Fin.addCases_left, Fin.addCases_right,
    Fin.sum_const, smul_eq_mul, Nat.add_assoc] using h

theorem coeff_size_le (f g : Polynomial ℤ) (m n k r bf bg : ℕ)
    (hf : ∀ i, (f.coeff i).natAbs ≤ 2 ^ bf) (hg : ∀ i, (g.coeff i).natAbs ≤ 2 ^ bg) :
    ((polynomial f g m n k).coeff r).natAbs.size ≤ budget m n k bf bg := by
  rw [coeff]
  split_ifs
  · exact minor_det_size_le f g m n k r bf bg hf hg
  · exact Nat.zero_le _

theorem coeff_coeff_size_le (f g : Polynomial (Polynomial ℤ)) (m n k r bf bg d : ℕ)
    (hf : ∀ i, coefficientMass (f.coeff i) ≤ 2 ^ bf) (hg : ∀ i, coefficientMass (g.coeff i) ≤ 2 ^ bg) :
    (((polynomial f g m n k).coeff r).coeff d).natAbs.size ≤ budget m n k bf bg := by
  rw [coeff]
  split_ifs
  · exact minor_det_coeff_size_le f g m n k r bf bg d hf hg
  · exact Nat.zero_le _

end LeanCanny.Algebra.Subresultant
