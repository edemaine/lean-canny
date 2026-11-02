/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedBankUnivariateSource
public import LeanCanny.Geometry.IntegralMixedFramedBankTermSign

/-! # Implicit univariate tests observe the same actual bank point

Only one raw joint tuple is used. Common-denominator clearing is by an even
power, so the native integer test has the sign of the requested polynomial
at that tuple's actual retained-bank coordinate.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFramedBankUnivariateSign
open LeanCanny.Algebra LeanCanny.Encoding IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedBankSnapshotBits (atKey)
open scoped Classical

theorem ratio (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool→List Bool) (index : List Bool→ℕ) (q : List Bool)
    (z : Fin (atKey P D H (key q)).count→ℝ) (hi : index q<(atKey P D H (key q)).count) :
    ((atKey P D H (key q)).cofactor (index q) : ℝ)*
        z ⟨index q,hi⟩^IntegralMixedFramedBankUnivariateSource.power P D H key index q/
        ((atKey P D H (key q)).common : ℝ)=
      IntegralMixedCanonicalBankPoint.point (IntegralMixedFramedBankTermSign.state P D H (key q)) z ⟨index q,hi⟩ := by
  let j : Fin (atKey P D H (key q)).count:=⟨index q,hi⟩
  apply (div_eq_div_iff
    (Int.cast_ne_zero.mpr (IntegralMixedFramedBankTermSign.common_ne_zero P D H (key q)))
    (IntegralMixedCanonicalBankPoint.denominator_ne_zero _ j)).mpr
  rw [IntegralMixedFramedBankTermSign.snapshot_split (atKey P D H (key q)) j,Int.cast_mul]
  change ((atKey P D H (key q)).cofactor (index q) : ℝ)*
    z j^IntegralMixedFramedBankUnivariateSource.power P D H key index q*
    ((atKey P D H (key q)).denominator j : ℝ)=
    z j^IntegralMixedFramedBankUnivariateSource.power P D H key index q*
    (((atKey P D H (key q)).denominator j : ℝ)*((atKey P D H (key q)).cofactor (index q) : ℝ))
  ring

theorem sign (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (key : List Bool→List Bool) (index : List Bool→ℕ) (Q : IntegerPolynomialRootQueriesBits.Source) (q : List Bool)
    (z : Fin (atKey P D H (key q)).count→ℝ) (hi : index q<(atKey P D H (key q)).count) :
    SignType.sign (((IntegralMixedFramedBankUnivariateSource.source P D H L F C hs key index Q).polynomial q).eval₂
      (Int.castRingHom ℝ) (z ⟨index q,hi⟩))=
      SignType.sign ((Q.polynomial q).eval₂ (Int.castRingHom ℝ)
        (IntegralMixedCanonicalBankPoint.point (IntegralMixedFramedBankTermSign.state P D H (key q)) z ⟨index q,hi⟩)) := by
  rw [IntegralMixedFramedBankUnivariateSource.source,
    IntegerPolynomialRationalPointSource.sign _ _ _ _ _ (IntegralMixedFramedBankTermSign.common_ne_zero P D H (key q))]
  exact congrArg (fun x : ℝ=>SignType.sign ((Q.polynomial q).eval₂ (Int.castRingHom ℝ) x))
    (ratio P D H key index q z hi)

end LeanCanny.Geometry.IntegralMixedFramedBankUnivariateSign
