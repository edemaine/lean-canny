/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CanonicalIntegralSamplerEvaluation

/-! # Extending the same real parent by every selected scalar root

An odd root of the new normalized scalar coordinate adjoins a full prefix
root with literally unchanged old coordinates. Applying the construction
to a selected root uses the actual canonical padded equation, so degree
drops and nonunit selected leading coefficients require no division.
-/

@[expose] public section
namespace LeanCanny.Algebra.UniformIntegralPrefix
open MvPolynomial UniformIntegralPowerSchedule
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {S N m : ℕ}

theorem real_extend (P : Prefix S N m) (hm : m ≤ S) (hN : 0 < N)
    (p : Polynomial P.carrier) (d : ℕ) (z : Fin m → ℝ)
    (hz : ∀ i, (P.rows i).eval₂ (Int.castRingHom ℝ) z = 0)
    (φ : P.carrier →ₐ[ℤ] ℝ) (hφ : ∀ i, φ (P.basis.generator i) = z i ^ weights S N m i)
    (t : ℝ) (ht : (PaddedIntegralParameterExtension.equation P.basis p d).eval₂
      (MvPolynomial.aeval (fun i => φ (P.basis.generator i))).toRingHom t = 0) :
    ∃ y : Fin (m + 1) → ℝ,
      (∀ j, ((step P hm hN p d).rows j).eval₂ (Int.castRingHom ℝ) y = 0) ∧
      (∀ i, y i.succ = z i) ∧ y 0 ^ birth S N m = t := by
  obtain ⟨u, hu⟩ := FlatAffinePowerTower.real_pow_surjective (birth S N m) (birth_odd S N m) t
  change u ^ birth S N m = t at hu
  refine ⟨Fin.cons u z, ?_, (fun _ => rfl), hu⟩
  intro j
  change (UniformIntegralPrefixRows.rows S P.rows P.basis p d j).eval₂ (Int.castRingHom ℝ) (Fin.cons u z) = 0
  refine Fin.cases ?_ (fun i => ?_) j
  · rw [UniformIntegralPrefixRows.rows, Fin.cons_zero, eval₂_rename, MonicParameterRows.eval_row,
      FixedDegreeIntegralNormalization.eq_of_monic _ N
        (PaddedIntegralParameterExtension.equation_monic P.basis p d hN).1
        (PaddedIntegralParameterExtension.equation_monic P.basis p d hN).2]
    have HC : MvPolynomial.eval₂Hom (Int.castRingHom ℝ)
        (fun i => (Fin.cons u z : Fin (m + 1) → ℝ) (UniformIntegralPrefixRows.layout m (Sum.inl i)) ^ weights S N m i) =
        (MvPolynomial.aeval (fun i => φ (P.basis.generator i))).toRingHom := by
      change MvPolynomial.eval₂Hom (algebraMap ℤ ℝ) (fun i => z i ^ weights S N m i) =
        MvPolynomial.eval₂Hom (algebraMap ℤ ℝ) (fun i => φ (P.basis.generator i))
      congr 1
      exact funext (fun i => (hφ i).symm)
    change (PaddedIntegralParameterExtension.equation P.basis p d).eval₂
      (MvPolynomial.eval₂Hom (Int.castRingHom ℝ)
        (fun i => (Fin.cons u z : Fin (m + 1) → ℝ) (UniformIntegralPrefixRows.layout m (Sum.inl i)) ^ weights S N m i))
      (u ^ birth S N m) = 0
    rw [HC, hu]
    exact ht
  · rw [UniformIntegralPrefixRows.rows, Fin.cons_succ, eval₂_rename]
    exact hz i

theorem real_extend_selected (P : Prefix S N m) (hm : m ≤ S) (hN : 0 < N)
    (p : Polynomial P.carrier) (d : ℕ) (hdN : d ≤ N) (z : Fin m → ℝ)
    (hz : ∀ i, (P.rows i).eval₂ (Int.castRingHom ℝ) z = 0)
    (φ : P.carrier →ₐ[ℤ] ℝ) (hφ : ∀ i, φ (P.basis.generator i) = z i ^ weights S N m i)
    (x : ℝ) (hd : (p.map φ.toRingHom).natDegree = d) (hpos : 1 ≤ d) (hx : p.eval₂ φ.toRingHom x = 0) :
    ∃ y : Fin (m + 1) → ℝ,
      (∀ j, ((step P hm hN p d).rows j).eval₂ (Int.castRingHom ℝ) y = 0) ∧
      (∀ i, y i.succ = z i) ∧ y 0 ^ birth S N m = φ (p.coeff d) * x :=
  real_extend P hm hN p d z hz φ hφ (φ (p.coeff d) * x)
    (PaddedIntegralParameterExtension.equation_root P.basis p d hdN φ x hd hpos hx)

end LeanCanny.Algebra.UniformIntegralPrefix
