/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ResultantFactorization
public import Mathlib.Algebra.CharZero.Infinite

/-!
# Primitive-coordinate representations with a specified resultant polynomial

The parameter polynomial is the normalized Sylvester determinant, rather than
an existentially chosen polynomial. A bounded common separating direction makes
it separable. The coordinate polynomials still come from Galois descent; symbolic
subresultant recovery and machine-level computation bounds remain open.
-/

@[expose] public section

namespace LeanCanny.Algebra
open Polynomial

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem cannyResultant_roots (p₁ p₂ : Polynomial K) (c : ℕ) (θ : L)
    (h₂ : p₂ ≠ 0) (hs₂ : (p₂.map (algebraMap K L)).Splits) :
    Polynomial.aeval θ (cannyResultant p₁ p₂ c) = 0 ↔
      ∃ a b : L, Polynomial.aeval a p₁ = 0 ∧ Polynomial.aeval b p₂ = 0 ∧ θ = a + (c : L) * b := by
  have hsign : algebraMap K L ((-1 : K) ^ (p₁.natDegree * p₂.natDegree)) ≠ 0 := by simp
  rw [cannyResultant_eq_sign_mul, map_mul, Polynomial.aeval_C]
  simp only [mul_eq_zero, hsign, false_or]
  exact projectionResultant_roots p₁ p₂ c θ h₂ hs₂

section Infinite
variable [Infinite L]

theorem cannyResultant_natDegree (p₁ p₂ : Polynomial K) (c : ℕ)
    (h₁ : p₁.Separable) (h₂ : p₂.Separable)
    (hs₁ : (p₁.map (algebraMap K L)).Splits) (hs₂ : (p₂.map (algebraMap K L)).Splits) :
    (cannyResultant p₁ p₂ c).natDegree = p₁.natDegree * p₂.natDegree := by
  rw [cannyResultant_eq_sign_mul, Polynomial.natDegree_C_mul (by simp),
    projectionResultant_natDegree p₁ p₂ c h₁ h₂ hs₁ hs₂]

theorem primitiveResultant_roots (p₁ p₂ : Polynomial K) (c : ℕ) (θ : L)
    (h₁ : p₁.Separable) (h₂ : p₂.Separable)
    (hs₁ : (p₁.map (algebraMap K L)).Splits) (hs₂ : (p₂.map (algebraMap K L)).Splits) :
    Polynomial.aeval θ (primitiveResultant p₁ p₂ c) = 0 ↔
      ∃ a b : L, Polynomial.aeval a p₁ = 0 ∧ Polynomial.aeval b p₂ = 0 ∧ θ = a + (c : L) * b := by
  classical
  rw [← Polynomial.eval_map_algebraMap, primitiveResultant_map_eq p₁ p₂ c h₁ h₂ hs₁ hs₂,
    Lagrange.eval_nodal, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨p, hp, hθ⟩
    obtain ⟨ha, hb⟩ := (mem_rootPairs p₁ p₂ h₁.ne_zero h₂.ne_zero p).mp hp
    exact ⟨p.1, p.2, ha, hb, sub_eq_zero.mp hθ⟩
  · rintro ⟨a, b, ha, hb, hθ⟩
    exact ⟨(a, b), (mem_rootPairs p₁ p₂ h₁.ne_zero h₂.ne_zero _).mpr ⟨ha, hb⟩,
      sub_eq_zero.mpr hθ⟩

end Infinite

section FiniteGalois
variable [FiniteDimensional K L] [IsGalois K L] [CharZero L]

/-- The parameter polynomial in the bounded primitive-coordinate representation
is the explicit normalized resultant of the input polynomials. -/
theorem exists_bounded_resultant_coordinates (p₁ p₂ : Polynomial K)
    (h₁ : p₁.Separable) (h₂ : p₂.Separable)
    (hs₁ : (p₁.map (algebraMap K L)).Splits) (hs₂ : (p₂.map (algebraMap K L)).Splits) :
    ∃ (c : ℕ) (r₁ r₂ : Polynomial K),
      c ≤ (p₁.natDegree * p₂.natDegree) ^ 2 ∧
      Set.InjOn (shear c) (rootPairs (L := L) p₁ p₂ : Set (L × L)) ∧
      (primitiveResultant p₁ p₂ c).Monic ∧ (primitiveResultant p₁ p₂ c).Separable ∧
      (primitiveResultant p₁ p₂ c).natDegree = p₁.natDegree * p₂.natDegree ∧
      r₁.degree < (p₁.natDegree * p₂.natDegree : WithBot ℕ) ∧
      r₂.degree < (p₁.natDegree * p₂.natDegree : WithBot ℕ) ∧
      (∀ θ : L, Polynomial.aeval θ (primitiveResultant p₁ p₂ c) = 0 ↔ ∃ a b : L,
        Polynomial.aeval a p₁ = 0 ∧ Polynomial.aeval b p₂ = 0 ∧ θ = a + (c : L) * b) ∧
      ∀ a b : L, Polynomial.aeval a p₁ = 0 → Polynomial.aeval b p₂ = 0 →
        Polynomial.aeval (a + (c : L) * b) r₁ = a ∧ Polynomial.aeval (a + (c : L) * b) r₂ = b := by
  classical
  obtain ⟨c, _, r₁, r₂, hc, hinj, _, _, _, hdeg₁, hdeg₂, _, hcoords⟩ :=
    exists_univariate_coordinates_over_base (K := K) (L := L) (rootPairs (L := L) p₁ p₂)
      (rootPairs_stable p₁ p₂ h₁.ne_zero h₂.ne_zero)
  have hcard := rootPairs_card p₁ p₂ h₁ h₂ hs₁ hs₂
  rw [hcard] at hc hdeg₁ hdeg₂
  refine ⟨c, r₁, r₂, hc, hinj, primitiveResultant_monic p₁ p₂ c h₁ h₂ hs₁ hs₂,
    primitiveResultant_separable p₁ p₂ c h₁ h₂ hs₁ hs₂ hinj,
    primitiveResultant_natDegree p₁ p₂ c h₁ h₂ hs₁ hs₂, hdeg₁, hdeg₂,
    (fun θ => primitiveResultant_roots p₁ p₂ c θ h₁ h₂ hs₁ hs₂), ?_⟩
  intro a b ha hb
  exact hcoords (a, b) ((mem_rootPairs p₁ p₂ h₁.ne_zero h₂.ne_zero _).mpr ⟨ha, hb⟩)

end FiniteGalois

/-- Square-free inputs supply their common finite Galois splitting field. -/
theorem exists_bounded_resultant_coordinates_of_squarefree [CharZero K]
    (p₁ p₂ : Polynomial K) (h₁ : Squarefree p₁) (h₂ : Squarefree p₂) :
    let L := (p₁ * p₂).SplittingField
    ∃ (c : ℕ) (r₁ r₂ : Polynomial K),
      c ≤ (p₁.natDegree * p₂.natDegree) ^ 2 ∧
      Set.InjOn (shear c) (rootPairs (L := L) p₁ p₂ : Set (L × L)) ∧
      (primitiveResultant p₁ p₂ c).Monic ∧ (primitiveResultant p₁ p₂ c).Separable ∧
      (primitiveResultant p₁ p₂ c).natDegree = p₁.natDegree * p₂.natDegree ∧
      r₁.degree < (p₁.natDegree * p₂.natDegree : WithBot ℕ) ∧
      r₂.degree < (p₁.natDegree * p₂.natDegree : WithBot ℕ) ∧
      (∀ θ : L, Polynomial.aeval θ (primitiveResultant p₁ p₂ c) = 0 ↔ ∃ a b : L,
        Polynomial.aeval a p₁ = 0 ∧ Polynomial.aeval b p₂ = 0 ∧ θ = a + (c : L) * b) ∧
      ∀ a b : L, Polynomial.aeval a p₁ = 0 → Polynomial.aeval b p₂ = 0 →
        Polynomial.aeval (a + (c : L) * b) r₁ = a ∧ Polynomial.aeval (a + (c : L) * b) r₂ = b := by
  let L := (p₁ * p₂).SplittingField
  let : IsGalois K L := { to_isSeparable := inferInstance, to_normal := inferInstance }
  have hsep₁ : p₁.Separable := PerfectField.separable_iff_squarefree.mpr h₁
  have hsep₂ : p₂.Separable := PerfectField.separable_iff_squarefree.mpr h₂
  have hs : ((p₁ * p₂).map (algebraMap K L)).Splits := Polynomial.SplittingField.splits (p₁ * p₂)
  rw [Polynomial.map_mul] at hs
  have hs' := (Polynomial.splits_mul (Polynomial.map_ne_zero hsep₁.ne_zero)
    (Polynomial.map_ne_zero hsep₂.ne_zero)).mp hs
  exact exists_bounded_resultant_coordinates p₁ p₂ hsep₁ hsep₂ hs'.1 hs'.2

end LeanCanny.Algebra
