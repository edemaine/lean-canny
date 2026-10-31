/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralHistoryEvaluation

/-! # Exact real scalar extension of the complete parent history

Every selected real scalar root extends the same full parent tuple. All
ancestral physical and multiplier coordinates remain literally unchanged.
Every algebra evaluation interpreting the extension recovers the selected
height from its canonical numerator and nonzero integer denominator.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralHistorySampler
open MvPolynomial UniformIntegralPowerSchedule
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {S N m : ℕ} {ι : Type} [Fintype ι]

theorem scalarStep_real_extend (F : Sampler S N m ι) (hm : m ≤ S) (hN : 0 < N)
    (p : Polynomial F.scalarPrefix.carrier) (d : ℕ) (z : ι → ℝ)
    (hz : ∀ i, (F.rows i).eval₂ (Int.castRingHom ℝ) z = 0)
    (φ : F.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (hφ : ∀ i, φ (F.scalarPrefix.basis.generator i) = z (F.scalar i) ^ weights S N m i)
    (t : ℝ) (ht : (PaddedIntegralParameterExtension.equation F.scalarPrefix.basis p d).eval₂
      (MvPolynomial.aeval (fun i => φ (F.scalarPrefix.basis.generator i))).toRingHom t = 0) :
    ∃ y : (ι ⊕ Unit) → ℝ,
      (∀ j, ((scalarStep F hm hN p d).rows j).eval₂ (Int.castRingHom ℝ) y = 0) ∧
      (∀ i, y (Sum.inl i) = z i) ∧ y (Sum.inr ()) ^ birth S N m = t := by
  obtain ⟨u, hu⟩ := FlatAffinePowerTower.real_pow_surjective (birth S N m) (birth_odd S N m) t
  change u ^ birth S N m = t at hu
  let y : (ι ⊕ Unit) → ℝ := Sum.elim z (fun _ => u)
  refine ⟨y, ?_, (fun _ => rfl), hu⟩
  apply (CanonicalIntegralScalarAppend.roots_iff S F.rows F.scalar F.scalarPrefix.basis p d y).mpr
  refine ⟨hz, ?_⟩
  rw [MonicParameterRows.eval_row,
    FixedDegreeIntegralNormalization.eq_of_monic _ N
      (PaddedIntegralParameterExtension.equation_monic F.scalarPrefix.basis p d hN).1
      (PaddedIntegralParameterExtension.equation_monic F.scalarPrefix.basis p d hN).2]
  have HC : MvPolynomial.eval₂Hom (Int.castRingHom ℝ)
      (fun i => (y ∘ CanonicalIntegralScalarAppend.layout F.scalar) (Sum.inl i) ^ weights S N m i) =
      (MvPolynomial.aeval (fun i => φ (F.scalarPrefix.basis.generator i))).toRingHom := by
    change MvPolynomial.eval₂Hom (algebraMap ℤ ℝ) (fun i => z (F.scalar i) ^ weights S N m i) =
      MvPolynomial.eval₂Hom (algebraMap ℤ ℝ) (fun i => φ (F.scalarPrefix.basis.generator i))
    congr 1
    exact funext (fun i => (hφ i).symm)
  rw [HC]
  change (PaddedIntegralParameterExtension.equation F.scalarPrefix.basis p d).eval₂
    (MvPolynomial.aeval (fun i => φ (F.scalarPrefix.basis.generator i))).toRingHom (u ^ birth S N m) = 0
  rw [hu]
  exact ht

theorem scalarStep_real_extend_recover (F : Sampler S N m ι) (hm : m ≤ S) (hN : 0 < N)
    (p : Polynomial F.scalarPrefix.carrier) (d : ℕ) (hdN : d ≤ N) (z : ι → ℝ)
    (hz : ∀ i, (F.rows i).eval₂ (Int.castRingHom ℝ) z = 0)
    (φ : F.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (hφ : ∀ i, φ (F.scalarPrefix.basis.generator i) = z (F.scalar i) ^ weights S N m i)
    (x : ℝ) (hd : (p.map φ.toRingHom).natDegree = d) (hpos : 1 ≤ d) (hx : p.eval₂ φ.toRingHom x = 0) :
    ∃ y : (ι ⊕ Unit) → ℝ,
      (∀ j, ((scalarStep F hm hN p d).rows j).eval₂ (Int.castRingHom ℝ) y = 0) ∧
      (∀ i, y (Sum.inl i) = z i) ∧
      ∀ ψ : (scalarStep F hm hN p d).scalarPrefix.carrier →ₐ[ℤ] ℝ,
        (∀ i, ψ ((scalarStep F hm hN p d).scalarPrefix.basis.generator i) =
          y ((scalarStep F hm hN p d).scalar i) ^ weights S N (m + 1) i) →
        ψ (PaddedIntegralParameterExtension.numerator F.scalarPrefix.basis p d) /
          ((PaddedIntegralParameterExtension.denominator F.scalarPrefix.basis p d : ℤ) : ℝ) = x := by
  obtain ⟨y, hy, htail, hhead⟩ := scalarStep_real_extend F hm hN p d z hz φ hφ (φ (p.coeff d) * x)
    (PaddedIntegralParameterExtension.equation_root F.scalarPrefix.basis p d hdN φ x hd hpos hx)
  refine ⟨y, hy, htail, ?_⟩
  intro ψ hψ
  let χ := PaddedIntegralParameterExtension.evaluate p d N hdN φ x hd hpos hx
  have HE : ψ = χ := by
    apply (PaddedIntegralParameterExtension.coordinateBasis F.scalarPrefix.basis p d).algHom_ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · have HI := hψ 0
      change ψ (AdjoinRoot.root _) = y (Sum.inr ()) ^ weights S N (m + 1) 0 at HI
      change ψ (AdjoinRoot.root _) = χ (AdjoinRoot.root _)
      rw [head, hhead] at HI
      rw [HI]
      exact (PaddedIntegralParameterExtension.evaluate_root p d N hdN φ x hd hpos hx).symm
    · have HI := hψ j.succ
      change ψ (AdjoinRoot.of _ (F.scalarPrefix.basis.generator j)) =
        y (Sum.inl (F.scalar j)) ^ weights S N (m + 1) j.succ at HI
      change ψ (AdjoinRoot.of _ (F.scalarPrefix.basis.generator j)) = χ (AdjoinRoot.of _ (F.scalarPrefix.basis.generator j))
      rw [old, htail (F.scalar j)] at HI
      rw [HI, ← hφ j]
      exact (PaddedIntegralParameterExtension.evaluate_of p d N hdN φ x hd hpos hx _).symm
  rw [HE]
  exact PaddedIntegralParameterExtension.recover F.scalarPrefix.basis p d hdN φ x hd hpos hx

end LeanCanny.Algebra.IntegralHistorySampler
