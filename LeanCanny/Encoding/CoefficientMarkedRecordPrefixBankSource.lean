/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordBankSource
/-! # Literal characteristic sources at every actual saved canonical prefix -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordPrefixBankSource
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory Polynomial
open IntegralMixedAuxiliaryMarkedRecordPlan (parameters plan data)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem heq_fin_apply {m k : ℕ} {A : Type} (f : Fin m → A) (g : Fin k → A)
    (h : HEq f g) (hm : m = k) (i : Fin m) : f i = g (Fin.cast hm i) := by
  cases hm
  exact congrFun (eq_of_heq h) i

private theorem polynomial_at_key (P : IntegralCriticalHistoryTask.Parameters)
    (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (c key : List Bool) (hk : IntegralMixedFramedCoordinateCharacteristicBits.key c = key)
    (ha : IntegralMixedFramedCoordinateCharacteristicBits.Active P c)
    (i : Fin ((IntegralMixedFramedHistoryFamilyBits.family P D H).birth key))
    (hi : i.val = IntegralMixedFramedCoordinateCharacteristicBits.index c) :
    IntegralMixedFramedCoordinateCharacteristicBits.polynomial P D H c =
      IntegralMixedBankCoordinatePolynomial.polynomial ((IntegralMixedFramedHistoryFamilyBits.family P D H).state key) i := by
  cases hk
  have HI : IntegralMixedFramedCoordinateCharacteristicBits.index c <
      IntegralMixedFramedCoordinateCharacteristicBits.count P D H c := by rw [← hi]; exact i.isLt
  have HA := IntegralMixedFramedCoordinateCharacteristicBits.polynomial_actual P D H c ha HI
  have HE : i = ⟨IntegralMixedFramedCoordinateCharacteristicBits.index c, HI⟩ := Fin.ext hi
  rw [← HE] at HA
  exact HA

def packet (n : List Bool → ℕ) (ctx : List Bool) (k : ℕ) (aux : List Bool) (i : ℕ) :=
  pair (CoefficientMarkedRecordRowLayout.key (n := n) ctx k aux) (BinaryNatCode.encode i)

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

private theorem packet_active (ctx : List Bool) (k : ℕ)
    (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx) (aux : List Bool) (i : ℕ) :
    IntegralMixedFramedCoordinateCharacteristicBits.Active (parameters hn ht ha) (packet n ctx k aux i) := by
  unfold IntegralMixedFramedCoordinateCharacteristicBits.Active
  simp only [IntegralMixedFramedCoordinateCharacteristicBits.key, packet, pairFst_pair]
  unfold CoefficientMarkedRecordRowLayout.key
  rw [CoefficientMarkedPreludeActual.indices_length]
  have HC := CoefficientMarkedRecordActual.birth_room hn ht ha ctx k hk
  rw [CoefficientMarkedPreludeActual.indices_length] at HC
  rw [IntegralMixedFramedHistoryFamilyBits.keyAt_prefix _ _ _ _ HC,
    IntegralMixedFramedHistoryFamilyBits.keyAt_root]
  have HR := IntegralMixedAuxiliaryMarkedRecordPlan.room hn ht ha ctx
  change IntegralMixedCausalRecordPlanBits.count ctx +
    (IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx + 8) + 2 ≤
      (parameters hn ht ha).cap ctx + 1 at HR
  omega

attribute [local irreducible] CoefficientMarkedRecordNative.run CoefficientMarkedRecordPrefix.build
  IntegralMixedSourceIntegerRecordAppend.plan IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedFramedCoordinateCharacteristicBits.polynomial

/-- The source is installed at this exact prefix and AUX; no complete word is supplied. -/
theorem specializes (ctx : List Bool) (R : List Bool → ℕ) (k : ℕ)
    (hk : k ≤ IntegralMixedCausalRecordPlanBits.count ctx) (aux : List Bool)
    (hR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ R ctx)
    (i : Fin ((CoefficientMarkedPreludeActual.indices n ctx).length + (CoefficientMarkedRecordActual.codes ctx k).length)) :
    (CoefficientMarkedRecordBankPolynomial.polynomial hn ht ha ctx k i).map (evalRingHom ((2 : ℤ) ^ R ctx)) =
      IntegralMixedFramedCoordinateCharacteristicBits.polynomial
        (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R) (packet n ctx k aux i.val) := by
  have HF := CoefficientMarkedRecordBankActual.specializes_family hn ht ha ctx R k hk aux hR
  have HM := CoefficientMarkedRecordRows.family_birth hn ht ha ctx R k hk aux
  have HV := heq_fin_apply _ _ HF HM i
  have HI : i.val < (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.actualFamily hn ht ha R).birth
      (CoefficientMarkedRecordRowLayout.key (n := n) ctx k aux) := by rw [← HM]; exact i.isLt
  have HE : Fin.cast HM i = ⟨i.val, HI⟩ := Fin.ext rfl
  rw [HE] at HV
  have HA := polynomial_at_key (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R)
    (packet n ctx k aux i.val) (CoefficientMarkedRecordRowLayout.key (n := n) ctx k aux)
    (by simp only [IntegralMixedFramedCoordinateCharacteristicBits.key, packet, pairFst_pair])
    (packet_active hn ht ha ctx k hk aux i.val) ⟨i.val, HI⟩
    (by simp only [packet, IntegralMixedFramedCoordinateCharacteristicBits.index, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits])
  exact HV.trans HA.symm

end LeanCanny.Encoding.CoefficientMarkedRecordPrefixBankSource
