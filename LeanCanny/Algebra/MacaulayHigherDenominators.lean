/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MacaulayUniversalQuotient

/-! # The complementary relation factors omit the last coefficient group

The diagonal relation blocks agree with extraneous submatrices, so they
use no last input polynomial. The higher relation factor therefore omits
that coefficient group and specializes to one at coordinate powers.
Permuting the last input gives another normalized family with no common
nonunit divisor.
-/

@[expose] public section

namespace LeanCanny.Algebra.Macaulay
open scoped Classical Matrix BigOperators
variable {n : ℕ} {R S : Type*} [CommRing R] [CommRing S]

theorem relationDoubleBlock_eq_off_last (p q : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ)
    (hW : level d < 2 ^ W) (last : Fin n) (hlast : ∀ j, j ≤ last)
    (hpq : ∀ i, i ≠ last → p i = q i) (i k : Fin n) :
    relationDoubleBlock p d W hW i k = relationDoubleBlock q d W hW i k := by
  funext a b
  change relationMinor p d W hW a.val.val b.val.val = relationMinor q d W hW a.val.val b.val.val
  have hi := a.val.property.trans b.val.property.symm
  rw [relationMinor_same_component p d W hW _ _ hi, relationMinor_same_component q d W hW _ _ hi,
    extraneousMinor_eq_off_last p q d W last hlast hpq]

theorem higherRelationFactor_eq_off_last (p q : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ)
    (hW : level d < 2 ^ W) (last : Fin n) (hlast : ∀ j, j ≤ last)
    (hpq : ∀ i, i ≠ last → p i = q i) : higherRelationFactor p d W hW = higherRelationFactor q d W hW := by
  unfold higherRelationFactor
  simp only [relationDoubleBlock_eq_off_last p q d W hW last hlast hpq]

theorem higherRelationFactor_map (φ : R →+* S) (p : Fin n → MvPolynomial (Fin n) R) (d : Fin n → ℕ) (W : ℕ)
    (hW : level d < 2 ^ W) : φ (higherRelationFactor p d W hW) = higherRelationFactor (fun i => (p i).map φ) d W hW := by
  unfold higherRelationFactor
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro k _
  have hm : (relationDoubleBlock p d W hW i k).map φ = relationDoubleBlock (fun i => (p i).map φ) d W hW i k := by
    funext a b
    exact congrFun (congrFun (relationMinor_map φ p d W hW) a.val.val) b.val.val
  rw [← hm]
  exact φ.map_det _

theorem higherRelationFactor_powers (d : Fin n → ℕ) (W : ℕ) (hW : level d < 2 ^ W) :
    higherRelationFactor (powers (R := R) d) d W hW = 1 := by
  have he := relationMinor_det_eq_extraneous_mul (powers (R := R) d) d W hW
  rw [relationMinor_powers, Matrix.det_one, ← eligibilityMinor_det_two, eligibilityMinor_powers, Matrix.det_one, one_mul] at he
  exact he.symm

end LeanCanny.Algebra.Macaulay

namespace LeanCanny.Algebra.MacaulayUniversal
open scoped Classical Matrix
variable {n : ℕ} {R : Type*} [CommRing R]

noncomputable def higherDenominator (d : Fin n → ℕ) (W : ℕ) (π : Equiv.Perm (Fin n))
    (hW : Macaulay.level (d ∘ π) < 2 ^ W) : CoefficientRing n R :=
  Macaulay.higherRelationFactor (system (R := R) d W π) (d ∘ π) W hW

theorem higherDenominator_eraseGroup (d : Fin n → ℕ) (W : ℕ) (π : Equiv.Perm (Fin n))
    (hW : Macaulay.level (d ∘ π) < 2 ^ W) (last : Fin n) (hlast : ∀ j, j ≤ last) :
    eraseGroup (R := R) (π last) (higherDenominator d W π hW) = higherDenominator d W π hW := by
  rw [higherDenominator, Macaulay.higherRelationFactor_map]
  apply Macaulay.higherRelationFactor_eq_off_last _ _ _ _ hW last hlast
  intro i hi
  exact system_map_eraseGroup d W π i (π last) (π.injective.ne hi)

theorem higherDenominator_omits_last (d : Fin n → ℕ) (W : ℕ) (π : Equiv.Perm (Fin n))
    (hW : Macaulay.level (d ∘ π) < 2 ^ W) (last : Fin n) (hlast : ∀ j, j ≤ last) (v : CoefficientIndex n)
    (hv : v ∈ (higherDenominator (R := R) d W π hW).vars) : v.1 ≠ π last := by
  rw [← higherDenominator_eraseGroup d W π hW last hlast] at hv
  exact mem_vars_eraseGroup _ _ _ hv

theorem higherDenominator_power_specialization (d : Fin n → ℕ) (W : ℕ) (hdegree : ∀ i, d i < 2 ^ W)
    (π : Equiv.Perm (Fin n)) (hW : Macaulay.level (d ∘ π) < 2 ^ W) :
    MvPolynomial.eval (powerPoint (R := R) d) (higherDenominator d W π hW) = 1 := by
  rw [higherDenominator, Macaulay.higherRelationFactor_map]
  have hs : (fun i => (system (R := R) d W π i).map (MvPolynomial.eval (powerPoint d))) = Macaulay.powers (R := R) (d ∘ π) :=
    funext (system_power_specialization d W hdegree π)
  rw [hs, Macaulay.higherRelationFactor_powers]

noncomputable def higherDenominatorFamily (d : Fin (n + 1) → ℕ) (W : ℕ)
    (hW : Macaulay.level d < 2 ^ W) (i : Fin (n + 1)) : CoefficientRing (n + 1) R :=
  higherDenominator d W (orderingFor i) (by rwa [level_comp_perm])

theorem higherDenominatorFamily_omits (d : Fin (n + 1) → ℕ) (W : ℕ) (hW : Macaulay.level d < 2 ^ W)
    (i : Fin (n + 1)) (v : CoefficientIndex (n + 1)) (hv : v ∈ (higherDenominatorFamily (R := R) d W hW i).vars) : v.1 ≠ i := by
  have he := higherDenominator_omits_last d W (orderingFor i) (by rwa [level_comp_perm]) (Fin.last n) Fin.le_last v hv
  simpa only [orderingFor, Equiv.swap_apply_left] using he

theorem higherDenominatorFamily_power_specialization (d : Fin (n + 1) → ℕ) (W : ℕ)
    (hdegree : ∀ i, d i < 2 ^ W) (hW : Macaulay.level d < 2 ^ W) (i : Fin (n + 1)) :
    MvPolynomial.eval (powerPoint (R := R) d) (higherDenominatorFamily d W hW i) = 1 :=
  higherDenominator_power_specialization d W hdegree (orderingFor i) (by rwa [level_comp_perm])

end LeanCanny.Algebra.MacaulayUniversal
