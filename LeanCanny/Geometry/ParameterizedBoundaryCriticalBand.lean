/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.ParameterizedBoundaryRadiusHead
/-! # Compact norm bands beyond the original radius bound have no small-residual critical points

Only the squared norms are placed in a compact interval. The multiplier
sequence may diverge. The constructed integer finite-limit head excludes
every possible limiting value in the band.
-/
@[expose] public section
namespace LeanCanny.Geometry.ParameterizedBoundaryCriticalBand
open LeanCanny.Algebra MvPolynomial Filter Set
open scoped Classical Topology
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem exists_interval (q : MvPolynomial (Fin n) ℤ) (D b : ℕ)
    (hD : q.totalDegree ≤ D) (hq : MvMass.mass q ≤ 2^b) (a c : ℝ)
    (ha : (2 : ℝ)^ParameterizedBoundaryRadiusHead.radiusExponent n D b ≤ a) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ e : ℝ, 0 < e → e < delta →
      ∀ (x : Fin n → ℝ) (lambda : ℝ), (q.eval₂ (Int.castRingHom ℝ) x)^2 = e →
        (∀ i, 2*x i + lambda*(2*q.eval₂ (Int.castRingHom ℝ) x*
          (pderiv i q).eval₂ (Int.castRingHom ℝ) x) = 0) →
          (∑ i, x i^2) ∉ Icc a c := by
  by_contra H
  push Not at H
  have HE (k : ℕ) : ∃ (e : ℝ) (x : Fin n → ℝ) (lambda : ℝ),
      0 < e ∧ e < 1/((k : ℝ)+1) ∧ (q.eval₂ (Int.castRingHom ℝ) x)^2 = e ∧
        (∀ i, 2*x i + lambda*(2*q.eval₂ (Int.castRingHom ℝ) x*
          (pderiv i q).eval₂ (Int.castRingHom ℝ) x) = 0) ∧ (∑ i, x i^2) ∈ Icc a c := by
    obtain ⟨e,he0,he1,x,lambda,hroot,hcritical,hnorm⟩ := H (1/((k : ℝ)+1)) (by positivity)
    exact ⟨e,x,lambda,he0,he1,hroot,hcritical,hnorm⟩
  choose epsilon x lambda hpos hsmall heq hcritical hnorm using HE
  have HZero : Tendsto epsilon atTop (𝓝 0) :=
    squeeze_zero (fun k => (hpos k).le) (fun k => (hsmall k).le) tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨t,ht,sigma,hSigma,hlim⟩ := isCompact_Icc.tendsto_subseq hnorm
  have HRoot := ParameterizedBoundaryRadiusHead.critical_limit_root q D b hD hq
    (epsilon ∘ sigma) (fun k => x (sigma k)) (lambda ∘ sigma) t (fun k => hpos (sigma k))
    (HZero.comp hSigma.tendsto_atTop) hlim
    (Eventually.of_forall (fun k => heq (sigma k)))
    (Eventually.of_forall (fun k => hcritical (sigma k)))
  have HBound := ParameterizedBoundaryRadiusHead.root_bound q D b hD hq t HRoot
  have HL : (2 : ℝ)^ParameterizedBoundaryRadiusHead.radiusExponent n D b ≤ t := ha.trans ht.1
  linarith [le_abs_self t]

end LeanCanny.Geometry.ParameterizedBoundaryCriticalBand
