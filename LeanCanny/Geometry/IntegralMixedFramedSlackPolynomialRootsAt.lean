/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFramedSlackPolynomialRoots

/-! # Slack roots need only the numeric controls at the actual saved key -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFramedSlackPolynomialRootsAt
open LeanCanny.Algebra LeanCanny.Encoding IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedSlackMatrixBits
open IntegralMixedFramedClearedMatrixBits (family rank)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (key : List Bool)

theorem sphere_congr (N R N' R' : List Bool→ℕ) (hn : N key=N' key) (hr : R key=R' key) :
    sphere P D H N R key=sphere P D H N' R' key := by
  simp only [sphere,sphereCoefficient,IntegralMixedFramedClearedPowerSumBits.matrixSum,hn,hr]

theorem regular_congr (N d R L K N' d' R' L' K' : List Bool→ℕ)
    (hn : N key=N' key) (hd : d key=d' key) (hr : R key=R' key)
    (hl : L key=L' key) (hk : K key=K' key) :
    regular P D H N d R L K key=regular P D H N' d' R' L' K' key := by
  simp only [regular,regularCoefficient,IntegralMixedFramedClearedPowerSumBits.matrixSum,hn,hd,hl,hk,
    sphere_congr P D H key N R N' R' hn hr]

variable (N R : List Bool→ℕ) (m r : ℕ)
  (hn : N key=m) (hr : R key=r)
  (φ : ((family P D H).state key).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
  (q : MvPolynomial (Fin m) ℤ) (a : BoundedZeroSource.Bounded q r)
  (ha : ∀i : Fin m,φ (elementAt P D H key (m-i.val))=(commonAt P D H key : ℝ)*a.val i)
include hn hr ha

theorem sphere_root :
    (Polynomial.expand ℤ 2 (ScaledGradedReductionAnnihilator.polynomial (sphere P D H N R key)
      (commonAt P D H key^2) 1)).eval₂ (Int.castRingHom ℝ) (BoundedRegularSource.sphereSlack q r a)=0 := by
  rw [sphere_congr P D H key N R (fun _=>m) (fun _=>r) hn hr]
  exact IntegralMixedFramedSlackPolynomialRoots.sphere_root P D H (fun _=>m) (fun _=>r) key φ q a ha

theorem regular_root (E b : ℕ) (d L K : List Bool→ℕ) (hd : d key=BoundedZeroSource.powerDegree E)
    (hl : L key=BoundedRegularSource.regularizationExponent m E b r)
    (hk : K key=BoundedZeroSource.penaltyExponent m E r) :
    (Polynomial.expand ℤ (d key) (ScaledGradedReductionAnnihilator.polynomial (regular P D H N d R L K key)
      ((2 : ℤ)^L key*commonAt P D H key^d key) 1)).eval₂ (Int.castRingHom ℝ)
        (BoundedRegularSource.regularSlack q E b r a).re=0 := by
  rw [regular_congr P D H key N d R L K (fun _=>m) (fun _=>BoundedZeroSource.powerDegree E)
    (fun _=>r) (fun _=>BoundedRegularSource.regularizationExponent m E b r)
    (fun _=>BoundedZeroSource.penaltyExponent m E r) hn hd hr hl hk,hd,hl]
  exact IntegralMixedFramedSlackPolynomialRoots.regular_root P D H (fun _=>m) (fun _=>r) key φ q a ha E b
    (fun _=>BoundedZeroSource.powerDegree E) (fun _=>BoundedRegularSource.regularizationExponent m E b r)
    (fun _=>BoundedZeroSource.penaltyExponent m E r) rfl rfl rfl

end LeanCanny.Geometry.IntegralMixedFramedSlackPolynomialRootsAt
