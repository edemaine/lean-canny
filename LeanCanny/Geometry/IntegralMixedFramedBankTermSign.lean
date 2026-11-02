/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedBankTermPolynomial
public import LeanCanny.Geometry.IntegralMixedCanonicalBankPoint
/-! # The original equation is evaluated at one actual joint bank point

Logical variable i is chronological birth i, hence newest-first retained
index m-1-i. Missing coordinates are zero. Every denominator is an actual
nonzero stored integer, so even clearing powers preserve the original sign.
No choice of interpreting hom or independent coordinate roots is supplied.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFramedBankTermSign
open LeanCanny.Algebra LeanCanny.Encoding IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedBankSnapshotBits (Snapshot atKey)
open IntegralMixedFramedBankTermBits (source size polynomial numeratorPolynomial denominatorPolynomial reverseIndex)
open scoped Classical

noncomputable abbrev state (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) :=
  (IntegralMixedFramedHistoryFamilyBits.family P D H).state key

noncomputable def point (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (z : Fin (atKey P D H key).count → ℝ) (i : ℕ) : ℝ :=
  if hi : i<(atKey P D H key).count then
    IntegralMixedCanonicalBankPoint.point (state P D H key) z
      ⟨reverseIndex P D H key i,IntegralMixedFramedBankTermBits.reverse_lt P D H key i hi⟩ else 0

theorem common_ne_zero (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) :
    (atKey P D H key).common≠0 := IntegralMixedHistory.commonDenominator_ne_zero (state P D H key)

theorem snapshot_split (s : Snapshot) (i : Fin s.count) : s.common=s.denominator i*s.cofactor i.val := by
  have HH := CommonIntegerDenominator.denominator_split Finset.univ s.denominator i (Finset.mem_univ _)
  have HC := IntegralMixedFramedBankProductBits.masked_product s.denominator i
  exact HH.trans (congrArg (fun v : ℤ => s.denominator i*v) HC.symm)

theorem ratio (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (z : Fin (atKey P D H key).count → ℝ) (i : ℕ) :
    (numeratorPolynomial P D H key i).eval₂ (Int.castRingHom ℝ) z/
      (denominatorPolynomial P D H key i).eval₂ (Int.castRingHom ℝ) z=point P D H key z i := by
  unfold numeratorPolynomial denominatorPolynomial point
  by_cases hi : i<(atKey P D H key).count
  · rw [dite_eq_left hi,dite_eq_left hi,MvPolynomial.eval₂_mul,MvPolynomial.eval₂_C,
      MvPolynomial.eval₂_pow,MvPolynomial.eval₂_X,MvPolynomial.eval₂_C]
    let j : Fin (atKey P D H key).count := ⟨reverseIndex P D H key i,IntegralMixedFramedBankTermBits.reverse_lt P D H key i hi⟩
    have HW : UniformIntegralPowerSchedule.weights (P.cap (pairFst key)+1) (2^P.width (pairFst key))
        (atKey P D H key).count j=
        UniformIntegralPowerSchedule.birth (P.cap (pairFst key)+1) (2^P.width (pairFst key)) i := by
      unfold UniformIntegralPowerSchedule.weights
      rw [IntegralMixedFramedBankTermBits.reverse_reverse P D H key i hi]
    change (((atKey P D H key).cofactor j.val : ℝ)*
      z j^UniformIntegralPowerSchedule.birth (P.cap (pairFst key)+1) (2^P.width (pairFst key)) i)/
        ((atKey P D H key).common : ℝ)=
      z j^UniformIntegralPowerSchedule.weights (P.cap (pairFst key)+1) (2^P.width (pairFst key)) (atKey P D H key).count j/
        ((atKey P D H key).denominator j : ℝ)
    rw [HW]
    apply (div_eq_div_iff (Int.cast_ne_zero.mpr (common_ne_zero P D H key))
      (Int.cast_ne_zero.mpr ((state P D H key).denominator_ne_zero j))).mpr
    rw [snapshot_split,Int.cast_mul]
    ring
  · rw [dite_eq_right hi,dite_eq_right hi,MvPolynomial.eval₂_zero]
    exact zero_div _

theorem denominator_ne_zero (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (z : Fin (atKey P D H key).count → ℝ) (i : ℕ) :
    (denominatorPolynomial P D H key i).eval₂ (Int.castRingHom ℝ) z≠0 := by
  rw [denominatorPolynomial,MvPolynomial.eval₂_C]
  exact Int.cast_ne_zero.mpr (common_ne_zero P D H key)

theorem sign (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (word : List Bool → List Bool) (key : List Bool) (z : Fin (atKey P D H key).count → ℝ) :
    SignType.sign ((polynomial P D H word key).eval₂ (Int.castRingHom ℝ) z)=
      SignType.sign (((source word).syntax key).eval (point P D H key z)) := by
  have HE := MvIndexedRationalClearing.sign (size word key) ((source word).syntax key).monomialCount
    (size word key) ((source word).syntax key).monomialCoefficient ((source word).syntax key).monomialExponent
    (numeratorPolynomial P D H key) (denominatorPolynomial P D H key) z
    (fun r _ i _ => IntegralMixedFramedBankTermBits.exponent_le word key r i)
    (fun i _ => denominator_ne_zero P D H key z i)
  let v : ℕ → ℝ := fun i => (numeratorPolynomial P D H key i).eval₂ (Int.castRingHom ℝ) z/
    (denominatorPolynomial P D H key i).eval₂ (Int.castRingHom ℝ) z
  have HS : ((source word).syntax key).arity≤size word key :=
    ((source word).scope key).trans_eq (IntegralMixedFramedBankTermBits.arity_eq_size word key)
  rw [((source word).syntax key).eval₂_indexed_source v (size word key) HS] at HE
  exact HE.trans (congrArg (fun f : ℕ → ℝ => SignType.sign (((source word).syntax key).eval f))
    (funext fun i => ratio P D H key z i))

end LeanCanny.Geometry.IntegralMixedFramedBankTermSign
