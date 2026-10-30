/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.FlatAffineSingularCriticalRoot

/-! # Zero objective multipliers identify singular affine-slice points

This uses regularity of the slice constraints, independently of regularity of
the larger critical system. With independent height normals, the zero-
multiplier critical roots project exactly onto the slice's singular locus.
-/

@[expose] public section
namespace LeanCanny.Geometry.FlatAffineSingularCriticalRoot
open LeanCanny.Algebra MvPolynomial
open FlatAffineCriticalStage FlatAffineCriticalExtremum
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
variable {ι R : Type*} {n : ℕ} [CommRing R]

theorem singular_of_zero_multiplier (phi : R →+* ℝ) (p : MvPolynomial (Fin n) R) (s : Finset (Fin n))
    (a : Fin (n + 1) → Fin n → R) (b : Fin n → MvPolynomial ι R) (x : ι → ℝ)
    (z : Fin n → ℝ) (mu : Fin (n + 1) → ℝ)
    (hroot : ∀ i, (row p s a b i).eval₂ phi (Sum.elim x (Sum.elim z mu)) = 0) (hmu : mu 0 = 0) :
    ¬Function.Surjective (derivative phi p s a z) := by
  intro hsurj
  obtain ⟨d, hd⟩ := hsurj (Pi.single none 1)
  have HP : (∑ i, (pderiv i p).eval₂ phi z * d i) = 1 := by
    have H := congrFun hd none
    simpa only [derivative, ContinuousLinearMap.pi_apply, constraint, PolynomialCalculus.derivative_apply,
      Pi.single_eq_same] using H
  have HA (j : s) : (∑ i, phi (a j.val.succ i) * d i) = 0 := by
    have H := congrFun hd (some j)
    simpa only [derivative, ContinuousLinearMap.pi_apply, constraint, PolynomialCalculus.derivative_apply,
      height_partial, Pi.single_eq_of_ne (show (some j : Option s) ≠ none by simp)] using H
  have HR := (roots_iff phi p s a b _).mp hroot
  have HZ : Sum.elim x (Sum.elim z mu) ∘ ambient = z := by
    funext i
    rfl
  have HG (i : Fin n) : (pderiv i p).eval₂ phi z = ∑ j, phi (a j i) * mu j := by
    simpa only [HZ, Function.comp_apply, multiplier, Sum.elim_inr] using HR.2.2.1 i
  have HU (j : Fin n) (hj : j ∉ s) : mu j.succ = 0 := by
    simpa only [multiplier, Sum.elim_inr] using HR.2.2.2 j hj
  have HE : (∑ i, (pderiv i p).eval₂ phi z * d i) = ∑ j, mu j * ∑ i, phi (a j i) * d i := by
    simp_rw [HG, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have HZERO : (∑ j, mu j * ∑ i, phi (a j i) * d i) = 0 := by
    rw [Fin.sum_univ_succ, hmu, zero_mul, zero_add]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : j ∈ s
    · rw [HA ⟨j, hj⟩, mul_zero]
    · rw [HU j hj, zero_mul]
  rw [HE, HZERO] at HP
  exact zero_ne_one HP

theorem regular_multiplier_ne_zero (phi : R →+* ℝ) (p : MvPolynomial (Fin n) R) (s : Finset (Fin n))
    (a : Fin (n + 1) → Fin n → R) (b : Fin n → MvPolynomial ι R) (x : ι → ℝ)
    (z : Fin n → ℝ) (mu : Fin (n + 1) → ℝ)
    (hroot : ∀ i, (row p s a b i).eval₂ phi (Sum.elim x (Sum.elim z mu)) = 0)
    (hregular : Function.Surjective (derivative phi p s a z)) : mu 0 ≠ 0 :=
  fun hmu => singular_of_zero_multiplier phi p s a b x z mu hroot hmu hregular

theorem singular_iff_zero_multiplier (phi : R →+* ℝ) (p : MvPolynomial (Fin n) R) (s : Finset (Fin n))
    (a : Fin (n + 1) → Fin n → R) (b : Fin n → MvPolynomial ι R) (x : ι → ℝ) (z : Fin n → ℝ)
    (hp : p.eval₂ phi z = 0) (hl : ∀ j ∈ s, ∑ i, phi (a j.succ i) * z i = (b j).eval₂ phi x)
    (hheights : ∀ c : s → ℝ, (∀ i, ∑ j : s, c j * phi (a j.val.succ i) = 0) → ∀ j, c j = 0) :
    ¬Function.Surjective (derivative phi p s a z) ↔
      ∃ mu : Fin (n + 1) → ℝ, mu 0 = 0 ∧ ∀ i, (row p s a b i).eval₂ phi (Sum.elim x (Sum.elim z mu)) = 0 :=
  ⟨exists_stage_root_of_singular phi p s a b x z hp hl hheights,
    fun ⟨mu, hmu, hroot⟩ => singular_of_zero_multiplier phi p s a b x z mu hroot hmu⟩

end LeanCanny.Geometry.FlatAffineSingularCriticalRoot
