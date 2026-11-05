/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.CoefficientBankUnivariateQuery
/-! # Actual bank cofactors at total natural indices -/
@[expose] public section
namespace LeanCanny.Algebra.CoefficientHeightBank
open scoped Classical BigOperators
variable {R S A B : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing B] {m : ℕ}

noncomputable def totalCofactor (x : CoefficientHeightBank R A m) (i : ℕ) : R :=
  ∏ j : Fin m, if j.val = i then 1 else x.denominator j

theorem totalCofactor_fin (x : CoefficientHeightBank R A m) (i : Fin m) :
    x.totalCofactor i.val = x.cofactor i :=
  (CoefficientBankUnivariateQuery.cofactor_ite x i).symm

theorem Specializes.totalCofactor [Algebra R A] [Algebra S B] {φ : R →+* S} {ψ : A →+* B}
    {x : CoefficientHeightBank R A m} {y : CoefficientHeightBank S B m}
    (H : Specializes φ ψ x y) (i : ℕ) : φ (x.totalCofactor i) = y.totalCofactor i := by
  simp only [CoefficientHeightBank.totalCofactor, map_prod]
  apply Finset.prod_congr rfl
  intro j _
  split_ifs
  · exact map_one φ
  · exact H.denominator j

end LeanCanny.Algebra.CoefficientHeightBank
