/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PrimitiveResultant

/-!
# Factorization and normalization of the primitive-coordinate resultant

For split separable inputs, the determinant polynomial is a nonzero scalar
multiple of the nodal polynomial on all projected pairs of roots. Its scalar is
explicit in the input leading coefficients. Dividing by it produces a monic
polynomial of degree exactly `degree p₁ * degree p₂` over the original field.
-/

@[expose] public section

namespace LeanCanny.Algebra
open Polynomial

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem prod_rootsFinset {M : Type*} [CommMonoid M] (p : Polynomial K) (hsep : p.Separable)
    (f : L → M) :
    (∏ x ∈ rootsFinset (L := L) p, f x) = ((p.map (algebraMap K L)).roots.map f).prod := by
  classical
  have hn := Polynomial.nodup_roots (hsep.map (f := algebraMap K L))
  rw [rootsFinset, ← Multiset.toFinset_eq hn, Finset.prod_mk]

theorem aeval_eq_leadingCoeff_mul_prod_rootsFinset (p : Polynomial K) (hsep : p.Separable)
    (hsplit : (p.map (algebraMap K L)).Splits) (θ : L) :
    Polynomial.aeval θ p = algebraMap K L p.leadingCoeff * ∏ a ∈ rootsFinset p, (θ - a) := by
  rw [← Polynomial.eval_map_algebraMap, hsplit.eval_eq_prod_roots, Polynomial.leadingCoeff_map,
    prod_rootsFinset p hsep]

theorem projectionResultant_eval_prod_rootsFinset (p₁ p₂ : Polynomial K) (c : ℕ) (θ : L)
    (h₂ : p₂.Separable) (hs₂ : (p₂.map (algebraMap K L)).Splits) :
    Polynomial.aeval θ (projectionResultant p₁ p₂ c) =
      (algebraMap K L p₂.leadingCoeff) ^ p₁.natDegree *
        ∏ b ∈ rootsFinset p₂, Polynomial.aeval (θ - (c : L) * b) p₁ := by
  rw [projectionResultant_eval_prod p₁ p₂ c θ hs₂, prod_rootsFinset p₂ h₂]

noncomputable def resultantScale (p₁ p₂ : Polynomial K) : K :=
  p₂.leadingCoeff ^ p₁.natDegree * p₁.leadingCoeff ^ p₂.natDegree

theorem resultantScale_ne_zero (p₁ p₂ : Polynomial K) (h₁ : p₁ ≠ 0) (h₂ : p₂ ≠ 0) :
    resultantScale p₁ p₂ ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ (mt Polynomial.leadingCoeff_eq_zero.mp h₂))
    (pow_ne_zero _ (mt Polynomial.leadingCoeff_eq_zero.mp h₁))

section Infinite
variable [Infinite L]

/-- Exact factorization of the Sylvester determinant, including its scalar. -/
theorem projectionResultant_map_eq (p₁ p₂ : Polynomial K) (c : ℕ)
    (h₁ : p₁.Separable) (h₂ : p₂.Separable)
    (hs₁ : (p₁.map (algebraMap K L)).Splits) (hs₂ : (p₂.map (algebraMap K L)).Splits) :
    (projectionResultant p₁ p₂ c).map (algebraMap K L) =
      C (algebraMap K L (resultantScale p₁ p₂)) * Lagrange.nodal (rootPairs p₁ p₂) (shear c) := by
  classical
  apply Polynomial.funext
  intro θ
  rw [Polynomial.eval_map_algebraMap, projectionResultant_eval_prod_rootsFinset p₁ p₂ c θ h₂ hs₂]
  simp_rw [aeval_eq_leadingCoeff_mul_prod_rootsFinset p₁ h₁ hs₁]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_const, rootsFinset_card p₂ h₂ hs₂]
  rw [Polynomial.eval_mul, Polynomial.eval_C, Lagrange.eval_nodal, rootPairs, Finset.prod_product_right]
  simp only [resultantScale, map_mul, map_pow]
  rw [mul_assoc]
  congr 1
  congr 1
  apply Finset.prod_congr rfl
  intro b _
  apply Finset.prod_congr rfl
  intro a _
  simp only [shear]
  ring

theorem projectionResultant_natDegree (p₁ p₂ : Polynomial K) (c : ℕ)
    (h₁ : p₁.Separable) (h₂ : p₂.Separable)
    (hs₁ : (p₁.map (algebraMap K L)).Splits) (hs₂ : (p₂.map (algebraMap K L)).Splits) :
    (projectionResultant p₁ p₂ c).natDegree = p₁.natDegree * p₂.natDegree := by
  have hscale : algebraMap K L (resultantScale p₁ p₂) ≠ 0 := by
    simpa only [map_zero] using (algebraMap K L).injective.ne (resultantScale_ne_zero p₁ p₂ h₁.ne_zero h₂.ne_zero)
  rw [← Polynomial.natDegree_map (algebraMap K L), projectionResultant_map_eq p₁ p₂ c h₁ h₂ hs₁ hs₂,
    Polynomial.natDegree_C_mul hscale, Lagrange.natDegree_nodal, rootPairs_card p₁ p₂ h₁ h₂ hs₁ hs₂]

theorem projectionResultant_leadingCoeff (p₁ p₂ : Polynomial K) (c : ℕ)
    (h₁ : p₁.Separable) (h₂ : p₂.Separable)
    (hs₁ : (p₁.map (algebraMap K L)).Splits) (hs₂ : (p₂.map (algebraMap K L)).Splits) :
    (projectionResultant p₁ p₂ c).leadingCoeff = resultantScale p₁ p₂ := by
  apply (algebraMap K L).injective
  rw [← Polynomial.leadingCoeff_map, projectionResultant_map_eq p₁ p₂ c h₁ h₂ hs₁ hs₂,
    Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
    (show (Lagrange.nodal (rootPairs (L := L) p₁ p₂) (shear c)).Monic from Lagrange.nodal_monic).leadingCoeff,
    mul_one]

end Infinite

/-- A monic version of the report's parameter polynomial, obtained by scalar normalization. -/
noncomputable def primitiveResultant (p₁ p₂ : Polynomial K) (c : ℕ) : Polynomial K :=
  C (resultantScale p₁ p₂)⁻¹ * projectionResultant p₁ p₂ c

section Infinite
variable [Infinite L]

theorem primitiveResultant_map_eq (p₁ p₂ : Polynomial K) (c : ℕ)
    (h₁ : p₁.Separable) (h₂ : p₂.Separable)
    (hs₁ : (p₁.map (algebraMap K L)).Splits) (hs₂ : (p₂.map (algebraMap K L)).Splits) :
    (primitiveResultant p₁ p₂ c).map (algebraMap K L) = Lagrange.nodal (rootPairs p₁ p₂) (shear c) := by
  have hscale : algebraMap K L (resultantScale p₁ p₂) ≠ 0 := by
    simpa only [map_zero] using (algebraMap K L).injective.ne (resultantScale_ne_zero p₁ p₂ h₁.ne_zero h₂.ne_zero)
  rw [primitiveResultant, Polynomial.map_mul, Polynomial.map_C,
    projectionResultant_map_eq p₁ p₂ c h₁ h₂ hs₁ hs₂, map_inv₀,
    ← mul_assoc, ← map_mul, inv_mul_cancel₀ hscale, map_one, one_mul]

theorem primitiveResultant_monic (p₁ p₂ : Polynomial K) (c : ℕ)
    (h₁ : p₁.Separable) (h₂ : p₂.Separable)
    (hs₁ : (p₁.map (algebraMap K L)).Splits) (hs₂ : (p₂.map (algebraMap K L)).Splits) :
    (primitiveResultant p₁ p₂ c).Monic := by
  apply Polynomial.monic_of_injective (algebraMap K L).injective
  rw [primitiveResultant_map_eq p₁ p₂ c h₁ h₂ hs₁ hs₂]
  exact Lagrange.nodal_monic

theorem primitiveResultant_natDegree (p₁ p₂ : Polynomial K) (c : ℕ)
    (h₁ : p₁.Separable) (h₂ : p₂.Separable)
    (hs₁ : (p₁.map (algebraMap K L)).Splits) (hs₂ : (p₂.map (algebraMap K L)).Splits) :
    (primitiveResultant p₁ p₂ c).natDegree = p₁.natDegree * p₂.natDegree := by
  rw [← Polynomial.natDegree_map (algebraMap K L), primitiveResultant_map_eq p₁ p₂ c h₁ h₂ hs₁ hs₂,
    Lagrange.natDegree_nodal, rootPairs_card p₁ p₂ h₁ h₂ hs₁ hs₂]

theorem primitiveResultant_separable (p₁ p₂ : Polynomial K) (c : ℕ)
    (h₁ : p₁.Separable) (h₂ : p₂.Separable)
    (hs₁ : (p₁.map (algebraMap K L)).Splits) (hs₂ : (p₂.map (algebraMap K L)).Splits)
    (hinj : Set.InjOn (shear c) (rootPairs (L := L) p₁ p₂ : Set (L × L))) :
    (primitiveResultant p₁ p₂ c).Separable := by
  apply (Polynomial.separable_map (algebraMap K L)).mp
  rw [primitiveResultant_map_eq p₁ p₂ c h₁ h₂ hs₁ hs₂, Lagrange.nodal]
  exact Polynomial.separable_prod_X_sub_C_iff'.mpr hinj

end Infinite
end LeanCanny.Algebra
