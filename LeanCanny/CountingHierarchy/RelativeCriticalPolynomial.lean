/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.SplitPolynomialEvaluation
public import LeanCanny.CountingHierarchy.ParameterCoefficientMap
public import LeanCanny.CountingHierarchy.MultivariateQuotientDegree
public import LeanCanny.CountingHierarchy.MultivariateQuotientMass
public import LeanCanny.CountingHierarchy.SeparatedPotentialDegree

/-! # Critical-value polynomials retaining an entire parameter block -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open MvPolynomial PurePowerResidue
open scoped BigOperators Classical

variable {n : ℕ} {κ : Type*}

/-- `none` is the growing penalty parameter; `some i` is an original parameter. -/
noncomputable def relativeSource (F : MvPolynomial (Fin n ⊕ κ) ℤ) :
    MvPolynomial (Fin n) (MvPolynomial (Option κ) ℤ) :=
  (splitIntegerPolynomial F).map (MvPolynomial.rename some).toRingHom

noncomputable def relativeLower (d : ℕ) (F : MvPolynomial (Fin n ⊕ κ) ℤ) (i : Fin n) :=
  criticalLower (d + 1) (fun _ => 0) (MvPolynomial.X none) (relativeSource F) i

noncomputable def relativeObjective (d : ℕ) (F : MvPolynomial (Fin n ⊕ κ) ℤ) :=
  deformedPolynomial (d + 1) (fun _ => 0) (MvPolynomial.X none) (relativeSource F)

theorem relativeSource_mainDegree (F : MvPolynomial (Fin n ⊕ κ) ℤ) :
    (relativeSource F).totalDegree ≤ F.totalDegree :=
  (map_degree_le _ _).trans (splitIntegerPolynomial_mainDegree_le F)

theorem relativeSource_parameterDegree (F : MvPolynomial (Fin n ⊕ κ) ℤ) :
    HasMultivariateParameterDegree (relativeSource F) F.totalDegree :=
  (splitIntegerPolynomial_parameterDegree_le F).map_rename some

theorem relativeSource_mass_le (F : MvPolynomial (Fin n ⊕ κ) ℤ) :
    MultivariateParameterMass.mass (relativeSource F) ≤ LeanCanny.Algebra.MvMass.mass F :=
  (MultivariateParameterMass.map_rename_le _ some).trans (splitIntegerPolynomial_mass_le F)

theorem relativeLower_mainDegree (d : ℕ) (F : MvPolynomial (Fin n ⊕ κ) ℤ)
    (hF : F.totalDegree ≤ d + 1) (i : Fin n) : (relativeLower d F i).totalDegree < d + 1 :=
  criticalLower_degree (d + 1) (by omega) _ _ _ ((relativeSource_mainDegree F).trans hF) i

theorem relativeObjective_mainDegree (d : ℕ) (F : MvPolynomial (Fin n ⊕ κ) ℤ)
    (hF : F.totalDegree ≤ d + 1) : (relativeObjective d F).totalDegree ≤ d + 2 := by
  rw [relativeObjective, deformedPolynomial]
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le (potentialPolynomial_totalDegree_le _ _) _
  exact (MvPolynomial.totalDegree_mul _ _).trans (by
    simp only [MvPolynomial.totalDegree_C, Nat.zero_add]
    exact (relativeSource_mainDegree F).trans (hF.trans (by omega)))

theorem relativeLower_parameterDegree (d H : ℕ) (F : MvPolynomial (Fin n ⊕ κ) ℤ)
    (hH : F.totalDegree ≤ H) (i : Fin n) : HasMultivariateParameterDegree (relativeLower d F i) (H + 1) := by
  have hc : HasMultivariateParameterDegree
      (MvPolynomial.C (0 : MvPolynomial (Option κ) ℤ) : MvPolynomial (Fin n) (MvPolynomial (Option κ) ℤ)) 0 :=
    HasMultivariateParameterDegree.C _ (by simp)
  have hu : HasMultivariateParameterDegree
      (MvPolynomial.C (MvPolynomial.X none : MvPolynomial (Option κ) ℤ) : MvPolynomial (Fin n) (MvPolynomial (Option κ) ℤ)) 1 :=
    HasMultivariateParameterDegree.C _ (by simp)
  have hsource := (relativeSource_parameterDegree F).mono hH
  have h := hc.sub (hu.mul (hsource.pderiv i))
  simpa only [relativeLower, criticalLower, zero_pow (by omega : d + 1 ≠ 0), Nat.add_comm 1 H,
    Nat.max_eq_right (Nat.zero_le (H + 1))] using h

theorem relativeObjective_parameterDegree (d H : ℕ) (F : MvPolynomial (Fin n ⊕ κ) ℤ)
    (hH : F.totalDegree ≤ H) : HasMultivariateParameterDegree (relativeObjective d F) (H + 1) := by
  have hp : HasMultivariateParameterDegree
      (potentialPolynomial (d + 1) (fun _ : Fin n => (0 : MvPolynomial (Option κ) ℤ))) 0 := by
    have h := HasMultivariateParameterDegree.map_C (τ := Option κ)
      (potentialPolynomial (d + 1) (fun _ : Fin n => (0 : ℤ)))
    rw [potentialPolynomial_map] at h
    simpa only [map_zero] using h
  have hu : HasMultivariateParameterDegree
      (MvPolynomial.C (((d + 2 : ℕ) : MvPolynomial (Option κ) ℤ) * MvPolynomial.X none) :
        MvPolynomial (Fin n) (MvPolynomial (Option κ) ℤ)) 1 := by
    apply HasMultivariateParameterDegree.C
    apply (MvPolynomial.totalDegree_mul _ _).trans
    simp only [← MvPolynomial.C_eq_natCast, MvPolynomial.totalDegree_C, MvPolynomial.totalDegree_X, Nat.zero_add, le_refl]
  have h := hp.add (hu.mul ((relativeSource_parameterDegree F).mono hH))
  simpa only [relativeObjective, deformedPolynomial, Nat.add_comm 1 H,
    Nat.max_eq_right (Nat.zero_le (H + 1))] using h

noncomputable def relativeCharacteristic (d : ℕ) (F : MvPolynomial (Fin n ⊕ κ) ℤ)
    (hF : F.totalDegree ≤ d + 1) : Polynomial (MvPolynomial (Option κ) ℤ) :=
  (multiplicationMatrix (by omega : 1 ≤ d + 1) (relativeLower d F)
    (relativeLower_mainDegree d F hF) (relativeObjective d F)).charpoly

theorem relativeCharacteristic_monic (d : ℕ) (F : MvPolynomial (Fin n ⊕ κ) ℤ)
    (hF : F.totalDegree ≤ d + 1) : (relativeCharacteristic d F hF).Monic := Matrix.charpoly_monic _

theorem relativeCharacteristic_natDegree (d : ℕ) (F : MvPolynomial (Fin n ⊕ κ) ℤ)
    (hF : F.totalDegree ≤ d + 1) : (relativeCharacteristic d F hF).natDegree = (d + 1) ^ n := by
  rw [relativeCharacteristic, Matrix.charpoly_natDegree_eq_dim, card_normalIndex]

end LeanCanny.CountingHierarchy
