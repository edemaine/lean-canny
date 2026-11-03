/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCriticalGuardSpace
public import LeanCanny.Algebra.IntegralMixedFramedCriticalGuardBounds
public import LeanCanny.Geometry.IntegralMixedFullBankPoint
/-! # The native correlation polynomial reads the same full bank point

It compares the actual retained quotient to the powered physical coordinate
of its creating critical block. The equality is valid for negative and
nonunit denominators. No annihilator-root equivalence is substituted.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFramedCriticalGuard
open LeanCanny.Algebra LeanCanny.Encoding IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family commands)
open IntegralMixedFramedCriticalGuardBits
open IntegralMixedHeaderTablesBits (Tables)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (T : Tables) (hr : IntegralMixedFramedHeaderBits.Represents P D H T)
  (key : List Bool→List Bool) (stage : List Bool→ℕ) (q : List Bool)

noncomputable def fullEquiv : (family P D H).physical (key q)≃Fin (count P T key q) :=
  (IntegralMixedFramedPhysicalIndex.enumerate (commands P D (key q))).trans
    (finCongr (count_actual P D H T hr key q).symm)

noncomputable def actualPoint (ha : Active P T key stage q) (z : Fin (count P T key q)→ℝ) : ℝ :=
  IntegralMixedFullBankPoint.indexedPoint ((family P D H).state (key q)) (fullEquiv P D H T hr key q) z
    ⟨age P key stage q,age_lt P D H T key stage q ha⟩

theorem denominator_ne_zero (ha : Active P T key stage q) : denominator P D H key stage q≠0 := by
  unfold denominator atKey
  rw [dite_eq_left (age_lt P D H T key stage q ha)]
  exact ((family P D H).state (key q)).denominator_ne_zero _

include hr in
theorem actualPoint_eq (ha : Active P T key stage q) (z : Fin (count P T key q)→ℝ) :
    actualPoint P D H T hr key stage q ha z=
      z ⟨scalar P T key stage q,scalar_lt P D H T hr key stage q ha⟩^scalarPower P key stage q /
        (denominator P D H key stage q:ℝ) := by
  let i : Fin (commands P D (key q)).length:=⟨age P key stage q,age_lt P D H T key stage q ha⟩
  have HC:=IntegralMixedFramedPhysicalIndex.scalarColumn_actual P D H T hr (key q) i
  have Hcol : fullEquiv P D H T hr key q (((family P D H).state (key q)).sampler.scalar i)=
      ⟨scalar P T key stage q,scalar_lt P D H T hr key stage q ha⟩ := by
    apply Fin.ext
    exact HC.symm
  have HP : UniformIntegralPowerSchedule.weights ((family P D H).cap (key q))
      (2^(family P D H).width (key q)) ((family P D H).birth (key q)) i=scalarPower P key stage q := by
    unfold UniformIntegralPowerSchedule.weights scalarPower
    congr 1
    change (family P D H).birth (key q)-1-age P key stage q=stage q
    rw [IntegralMixedFramedHistoryFamilyBits.family_birth]
    have HA:=ha.1
    dsimp only [i,age]
    omega
  have HD : denominator P D H key stage q=((family P D H).state (key q)).bank.denominator i := by
    unfold denominator atKey
    rw [dite_eq_left (age_lt P D H T key stage q ha)]
  unfold actualPoint IntegralMixedFullBankPoint.indexedPoint IntegralMixedFullBankPoint.point
    IntegralMixedCanonicalBankPoint.point
  change z (fullEquiv P D H T hr key q (((family P D H).state (key q)).sampler.scalar i))^_ / _=_
  rw [Hcol,HP,HD]

include hr in
theorem polynomial_eval (ha : Active P T key stage q) (z : Fin (count P T key q)→ℝ) :
    (polynomial P D H T key stage q).eval₂ (Int.castRingHom ℝ) z=
      z ⟨scalar P T key stage q,scalar_lt P D H T hr key stage q ha⟩^scalarPower P key stage q -
        (denominator P D H key stage q:ℝ)*
          z ⟨physical P T key stage q,physical_lt P D H T hr key stage q ha⟩^physicalPower P key stage q := by
  unfold polynomial rawPolynomial FixedWidthMonomialBits.polynomial
  rw [ite_eq_left ha,dite_eq_left (scalar_lt P D H T hr key stage q ha),
    dite_eq_left (physical_lt P D H T hr key stage q ha)]
  rw [←MvPolynomial.X_pow_eq_monomial,←MvPolynomial.C_mul_X_pow_eq_monomial]
  simp only [MvPolynomial.eval₂_sub,MvPolynomial.eval₂_pow,MvPolynomial.eval₂_X,MvPolynomial.eval₂_mul,MvPolynomial.eval₂_C]
  rfl

include hr in
theorem zero_iff_actualPoint (ha : Active P T key stage q) (z : Fin (count P T key q)→ℝ) :
    (polynomial P D H T key stage q).eval₂ (Int.castRingHom ℝ) z=0 ↔
      actualPoint P D H T hr key stage q ha z=
        z ⟨physical P T key stage q,physical_lt P D H T hr key stage q ha⟩^physicalPower P key stage q := by
  rw [polynomial_eval P D H T hr key stage q ha z,actualPoint_eq P D H T hr key stage q ha z,sub_eq_zero]
  have HD : (denominator P D H key stage q:ℝ)≠0 := Int.cast_ne_zero.mpr (denominator_ne_zero P D H T key stage q ha)
  constructor
  · intro HE
    apply (div_eq_iff HD).mpr
    exact HE.trans (mul_comm _ _)
  · intro HE
    exact ((div_eq_iff HD).mp HE).trans (mul_comm _ _)
end LeanCanny.Geometry.IntegralMixedFramedCriticalGuard
