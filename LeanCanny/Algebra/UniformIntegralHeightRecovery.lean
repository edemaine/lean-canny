/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.UniformIntegralPrefixRealExtension

/-! # Recovering a selected height at the same extended parent root

Every selected real root extends the parent prefix without changing any
old coordinate. Every evaluation interpreting that extended root recovers
the original height from its canonical integral numerator and fixed
nonzero integer denominator. The normalized coordinate need not itself
equal the height, and the selected leading coefficient need not be a unit.
-/

@[expose] public section
namespace LeanCanny.Algebra.UniformIntegralPrefix
open UniformIntegralPowerSchedule
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {S N m : ℕ}

theorem real_extend_recover (P : Prefix S N m) (hm : m ≤ S) (hN : 0 < N)
    (p : Polynomial P.carrier) (d : ℕ) (hdN : d ≤ N) (z : Fin m → ℝ)
    (hz : ∀ i, (P.rows i).eval₂ (Int.castRingHom ℝ) z = 0)
    (φ : P.carrier →ₐ[ℤ] ℝ) (hφ : ∀ i, φ (P.basis.generator i) = z i ^ weights S N m i)
    (x : ℝ) (hd : (p.map φ.toRingHom).natDegree = d) (hpos : 1 ≤ d) (hx : p.eval₂ φ.toRingHom x = 0) :
    ∃ y : Fin (m + 1) → ℝ,
      (∀ j, ((step P hm hN p d).rows j).eval₂ (Int.castRingHom ℝ) y = 0) ∧
      (∀ i, y i.succ = z i) ∧
      ∀ ψ : (step P hm hN p d).carrier →ₐ[ℤ] ℝ,
        (∀ i, ψ ((step P hm hN p d).basis.generator i) = y i ^ weights S N (m + 1) i) →
        ψ (PaddedIntegralParameterExtension.numerator P.basis p d) /
          ((PaddedIntegralParameterExtension.denominator P.basis p d : ℤ) : ℝ) = x := by
  obtain ⟨y, hy, htail, hhead⟩ := real_extend_selected P hm hN p d hdN z hz φ hφ x hd hpos hx
  refine ⟨y, hy, htail, ?_⟩
  intro ψ hψ
  let χ := PaddedIntegralParameterExtension.evaluate p d N hdN φ x hd hpos hx
  have HE : ψ = χ := by
    apply (PaddedIntegralParameterExtension.coordinateBasis P.basis p d).algHom_ext
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · have HI := hψ 0
      change ψ (AdjoinRoot.root _) = y 0 ^ weights S N (m + 1) 0 at HI
      change ψ (AdjoinRoot.root _) = χ (AdjoinRoot.root _)
      rw [head, hhead] at HI
      rw [HI]
      exact (PaddedIntegralParameterExtension.evaluate_root p d N hdN φ x hd hpos hx).symm
    · have HI := hψ j.succ
      change ψ (AdjoinRoot.of _ (P.basis.generator j)) = y j.succ ^ weights S N (m + 1) j.succ at HI
      change ψ (AdjoinRoot.of _ (P.basis.generator j)) = χ (AdjoinRoot.of _ (P.basis.generator j))
      rw [old, htail j] at HI
      rw [HI, ← hφ j]
      exact (PaddedIntegralParameterExtension.evaluate_of p d N hdN φ x hd hpos hx _).symm
  rw [HE]
  exact PaddedIntegralParameterExtension.recover P.basis p d hdN φ x hd hpos hx

end LeanCanny.Algebra.UniformIntegralPrefix
