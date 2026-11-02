/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedBankOrderTerm
public import LeanCanny.Geometry.IntegralMixedFramedBankTermSign
/-! # Positive common-square clearing compares retained quotients exactly

The polynomial is Q times the difference of two Q-cleared coordinates.
It evaluates to Q² times their actual quotient difference on the same joint
tuple. Integer denominators may be negative and need not be modular units.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFramedBankOrder
open LeanCanny.Algebra LeanCanny.Encoding IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedBankSnapshotBits (atKey)
open IntegralMixedFramedBankOrderBits (count chronological)
open IntegralMixedFramedBankTermSign (point state)
open scoped Classical

theorem point_chronological (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool→List Bool) (index : List Bool→ℕ) (c : List Bool)
    (hi : index c<count P D H key c) (z : Fin (atKey P D H (key c)).count→ℝ) :
    point P D H (key c) z (chronological P D H key index c)=
      IntegralMixedCanonicalBankPoint.point (state P D H (key c)) z ⟨index c,hi⟩ := by
  unfold point
  have HC : chronological P D H key index c<(atKey P D H (key c)).count :=
    IntegralMixedFramedBankOrderBits.chronological_lt P D H key index c (by omega)
  rw [dite_eq_left HC]
  exact congrArg (IntegralMixedCanonicalBankPoint.point (state P D H (key c)) z)
    (Fin.ext (IntegralMixedFramedBankOrderBits.chronological_reverse P D H key index c hi))

theorem term_eval (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool→List Bool) (left right : List Bool→ℕ) (c : List Bool)
    (hl : left c<count P D H key c) (hr : right c<count P D H key c)
    (z : Fin (atKey P D H (key c)).count→ℝ) :
    (IntegralMixedFramedBankOrderBits.term P D H key left right c).eval (point P D H (key c) z)=
      IntegralMixedCanonicalBankPoint.point (state P D H (key c)) z ⟨left c,hl⟩-
      IntegralMixedCanonicalBankPoint.point (state P D H (key c)) z ⟨right c,hr⟩ := by
  simp only [IntegralMixedFramedBankOrderBits.term,ETR.Term.eval,Int.cast_neg,Int.cast_one,neg_one_mul,←sub_eq_add_neg]
  rw [point_chronological P D H key left c hl z,point_chronological P D H key right c hr z]

noncomputable def polynomial (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool→List Bool) (left right : List Bool→ℕ) (c : List Bool) :
    MvPolynomial (Fin (atKey P D H (key c)).count) ℤ :=
  MvPolynomial.C (atKey P D H (key c)).common*
    (IntegralMixedFramedBankTermBits.numeratorPolynomial P D H (key c) (chronological P D H key left c)-
     IntegralMixedFramedBankTermBits.numeratorPolynomial P D H (key c) (chronological P D H key right c))

private theorem numerator_eval (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (z : Fin (atKey P D H key).count→ℝ) (i : ℕ) :
    (IntegralMixedFramedBankTermBits.numeratorPolynomial P D H key i).eval₂ (Int.castRingHom ℝ) z=
      ((atKey P D H key).common:ℝ)*point P D H key z i := by
  have HR:=IntegralMixedFramedBankTermSign.ratio P D H key z i
  rw [IntegralMixedFramedBankTermBits.denominatorPolynomial,MvPolynomial.eval₂_C] at HR
  exact ((div_eq_iff (Int.cast_ne_zero.mpr (IntegralMixedFramedBankTermSign.common_ne_zero P D H key))).mp HR).trans (mul_comm _ _)

theorem polynomial_eval (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool→List Bool) (left right : List Bool→ℕ) (c : List Bool)
    (hl : left c<count P D H key c) (hr : right c<count P D H key c)
    (z : Fin (atKey P D H (key c)).count→ℝ) :
    (polynomial P D H key left right c).eval₂ (Int.castRingHom ℝ) z=
      ((atKey P D H (key c)).common:ℝ)^2*
        (IntegralMixedCanonicalBankPoint.point (state P D H (key c)) z ⟨left c,hl⟩-
         IntegralMixedCanonicalBankPoint.point (state P D H (key c)) z ⟨right c,hr⟩) := by
  rw [polynomial,MvPolynomial.eval₂_mul,MvPolynomial.eval₂_C,MvPolynomial.eval₂_sub,numerator_eval,numerator_eval,
    point_chronological P D H key left c hl z,point_chronological P D H key right c hr z]
  change ((atKey P D H (key c)).common:ℝ)*
    (((atKey P D H (key c)).common:ℝ)*_ - ((atKey P D H (key c)).common:ℝ)*_)=_
  ring

theorem polynomial_sign (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool→List Bool) (left right : List Bool→ℕ) (c : List Bool)
    (hl : left c<count P D H key c) (hr : right c<count P D H key c)
    (z : Fin (atKey P D H (key c)).count→ℝ) :
    SignType.sign ((polynomial P D H key left right c).eval₂ (Int.castRingHom ℝ) z)=
      SignType.sign (IntegralMixedCanonicalBankPoint.point (state P D H (key c)) z ⟨left c,hl⟩-
        IntegralMixedCanonicalBankPoint.point (state P D H (key c)) z ⟨right c,hr⟩) := by
  rw [polynomial_eval P D H key left right c hl hr z,sign_mul,
    sign_pos (sq_pos_of_ne_zero (Int.cast_ne_zero.mpr (IntegralMixedFramedBankTermSign.common_ne_zero P D H (key c)))),one_mul]

theorem word_syntax (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool→List Bool) (hroot : ∀ c,pairFst (key c)=c) (left right : List Bool→ℕ) (c : List Bool) :
    (IntegralMixedFramedBankTermBits.source (IntegralMixedFramedBankOrderBits.word P D H key left right)).syntax (key c)=
      IntegralMixedFramedBankOrderBits.term P D H key left right c := by
  unfold IntegralMixedFramedBankTermBits.source IntegralMixedFramedBankTermBits.wordAt
    ETR.RationalSubstitutionBits.Source.syntax ETR.RationalSubstitutionBits.Source.ofTerm
  dsimp only
  rw [hroot,IntegralMixedFramedBankOrderBits.word,ETR.TermView.term_toBits]

end LeanCanny.Geometry.IntegralMixedFramedBankOrder
