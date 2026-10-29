/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.AffineHeightPolynomial
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-! # A linear exceptional factor for independent new affine heights -/

@[expose] public section
namespace LeanCanny.Algebra.AffineDirectionAvoidance
open MvPolynomial
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} {n : ℕ} [Field K]

theorem exists_annihilator (s : Finset (Fin n)) (hs : s.card < n) (A : Fin n → Fin n → K) :
    ∃ γ : Fin n → K, γ ≠ 0 ∧ ∀ j ∈ s, ∑ i, γ i * A j i = 0 := by
  let M : Matrix s (Fin n) K := fun j i => A j.val i
  let f := M.mulVecLin
  have hker : f.ker ≠ ⊥ := by
    intro he
    have H := LinearMap.finrank_le_finrank_of_injective (f := f) (LinearMap.ker_eq_bot.mp he)
    simp only [Module.finrank_fintype_fun_eq_card, Fintype.card_coe, Fintype.card_fin] at H
    omega
  obtain ⟨γ, hγ, hn⟩ := f.ker.ne_bot_iff.mp hker
  refine ⟨γ, hn, fun j hj => ?_⟩
  change f γ = 0 at hγ
  have H := congrFun hγ ⟨j, hj⟩
  change (∑ i, A j i * γ i) = 0 at H
  exact (Finset.sum_congr rfl (fun i _ => mul_comm (γ i) (A j i))).trans H

noncomputable def polynomial (γ : Fin n → K) : MvPolynomial (Fin n) K :=
  AffineHeightPolynomial.polynomial γ id

theorem coefficient (γ : Fin n → K) (i : Fin n) : (polynomial γ).coeff (Finsupp.single i 1) = γ i := by
  simp [polynomial, AffineHeightPolynomial.polynomial, coeff_C_mul, coeff_X,
    Finsupp.single_left_inj (show (1 : ℕ) ≠ 0 by decide)]

theorem ne_zero (γ : Fin n → K) (hγ : γ ≠ 0) : polynomial γ ≠ 0 := by
  intro he
  apply hγ
  funext i
  have H := congrArg (fun q : MvPolynomial (Fin n) K => q.coeff (Finsupp.single i 1)) he
  rw [coefficient] at H
  simpa using H

theorem eval {L : Type*} [CommRing L] (φ : K →+* L) (γ : Fin n → K) (v : Fin n → L) :
    (polynomial γ).eval₂ φ v = ∑ i, φ (γ i) * v i :=
  AffineHeightPolynomial.eval φ γ id v

theorem not_in_span {L : Type*} [Field L] [Algebra K L] (s : Finset (Fin n))
    (A : Fin n → Fin n → K) (γ : Fin n → K)
    (hγ : ∀ j ∈ s, ∑ i, γ i * A j i = 0) (v : Fin n → L)
    (hv : (polynomial γ).eval₂ (algebraMap K L) v ≠ 0) :
    ¬ ∃ c : s → L, ∀ i, v i = ∑ j : s, c j * algebraMap K L (A j.val i) := by
  rintro ⟨c, hc⟩
  apply hv
  rw [eval]
  simp_rw [hc, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j _
  have H := congrArg (algebraMap K L) (hγ j.val j.property)
  simp only [map_sum, map_mul, map_zero] at H
  calc
    (∑ i, algebraMap K L (γ i) * (c j * algebraMap K L (A j.val i))) =
        c j * ∑ i, algebraMap K L (γ i) * algebraMap K L (A j.val i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = 0 := by rw [H, mul_zero]

end LeanCanny.Algebra.AffineDirectionAvoidance
