/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordBankActual
public import LeanCanny.Encoding.IntegralMixedPhysicalFieldEqualityPlanning
public import LeanCanny.Algebra.IntegralMixedFramedCoordinateCharacteristicActual
/-! # The literal full-bank characteristic has a constructed parameter source -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordBankSource
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory Polynomial
open IntegralMixedAuxiliaryMarkedRecordPlan (parameters plan data fullCount)
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
      IntegralMixedFramedCoordinateCharacteristicBits.count P D H c := by
    rw [← hi]
    exact i.isLt
  have HA := IntegralMixedFramedCoordinateCharacteristicBits.polynomial_actual P D H c ha HI
  have HE : i = ⟨IntegralMixedFramedCoordinateCharacteristicBits.index c, HI⟩ := Fin.ext hi
  rw [← HE] at HA
  exact HA

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

abbrev count (ctx : List Bool) := IntegralMixedCausalRecordPlanBits.count ctx

def packet (ctx : List Bool) (i : ℕ) : List Bool :=
  pair (CoefficientMarkedRecordRowLayout.key (n := n) ctx (count ctx) []) (BinaryNatCode.encode i)

theorem birth_eq (ctx : List Bool) :
    (CoefficientMarkedPreludeActual.indices n ctx).length + (CoefficientMarkedRecordActual.codes ctx (count ctx)).length =
      fullCount n ctx := by
  rw [CoefficientMarkedPreludeActual.indices_length, CoefficientMarkedRecordActual.codes_length]
  rfl

noncomputable def polynomial (ctx : List Bool) (i : Fin (fullCount n ctx)) : Polynomial ℤ[X] :=
  CoefficientMarkedRecordBankPolynomial.polynomial hn ht ha ctx (count ctx) (Fin.cast (birth_eq ctx).symm i)

theorem packet_key (ctx : List Bool) (i : ℕ) :
    IntegralMixedFramedCoordinateCharacteristicBits.key (packet (n := n) ctx i) =
      IntegralMixedFramedHistoryFamilyBits.keyAt ctx (fullCount n ctx) [] := by
  simp only [packet, IntegralMixedFramedCoordinateCharacteristicBits.key, pairFst_pair,
    CoefficientMarkedRecordRowLayout.key, CoefficientMarkedPreludeActual.indices_length]
  rfl

theorem packet_index (ctx : List Bool) (i : ℕ) :
    IntegralMixedFramedCoordinateCharacteristicBits.index (packet (n := n) ctx i) = i := by
  simp only [packet, IntegralMixedFramedCoordinateCharacteristicBits.index, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]

attribute [local irreducible] CoefficientMarkedRecordNative.run CoefficientMarkedRecordPrefix.build
  IntegralMixedSourceIntegerRecordAppend.plan IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedFramedCoordinateCharacteristicBits.polynomial

private theorem count_room (ctx : List Bool) : fullCount n ctx ≤ (parameters hn ht ha).cap ctx + 1 := by
  have H := CoefficientMarkedRecordActual.birth_room hn ht ha ctx (count ctx) le_rfl
  rw [CoefficientMarkedPreludeActual.indices_length] at H
  exact H

private theorem source_count (ctx : List Bool) (R : List Bool → ℕ) (i : ℕ) :
    IntegralMixedFramedCoordinateCharacteristicBits.count (parameters hn ht ha) (plan hn ht ha R)
      (data hn ht ha R) (packet (n := n) ctx i) = fullCount n ctx := by
  rw [IntegralMixedFramedCoordinateCharacteristicBits.count_eq, packet_key]
  exact IntegralMixedFramedHistoryFamilyBits.keyAt_prefix _ ctx _ [] (count_room hn ht ha ctx)

private theorem source_active (ctx : List Bool) (i : ℕ) :
    IntegralMixedFramedCoordinateCharacteristicBits.Active (parameters hn ht ha) (packet (n := n) ctx i) := by
  unfold IntegralMixedFramedCoordinateCharacteristicBits.Active
  rw [packet_key, IntegralMixedFramedHistoryFamilyBits.keyAt_prefix _ ctx _ [] (count_room hn ht ha ctx),
    IntegralMixedFramedHistoryFamilyBits.keyAt_root]
  have H := IntegralMixedAuxiliaryMarkedRecordPlan.room hn ht ha ctx
  change count ctx + (IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx + 8) + 2 ≤
    (parameters hn ht ha).cap ctx + 1 at H
  unfold fullCount
  dsimp only [count] at H
  omega

/-- The actual characteristic source is obtained by specializing the constructed polynomial. -/
theorem specializes (ctx : List Bool) (R : List Bool → ℕ)
    (hR : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ R ctx)
    (i : Fin (fullCount n ctx)) :
    (polynomial hn ht ha ctx i).map (evalRingHom ((2 : ℤ) ^ R ctx)) =
      IntegralMixedFramedCoordinateCharacteristicBits.polynomial
        (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R) (packet (n := n) ctx i.val) := by
  have HF := CoefficientMarkedRecordBankActual.specializes_family hn ht ha ctx R (count ctx) le_rfl [] hR
  have HM := CoefficientMarkedRecordRows.family_birth hn ht ha ctx R (count ctx) le_rfl []
  have HV := heq_fin_apply _ _ HF HM (Fin.cast (birth_eq ctx).symm i)
  have HI' : i.val < (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.actualFamily hn ht ha R).birth
      (CoefficientMarkedRecordRowLayout.key (n := n) ctx (count ctx) []) := by
    rw [← HM, birth_eq]
    exact i.isLt
  have HE : Fin.cast HM (Fin.cast (birth_eq ctx).symm i) =
      ⟨i.val, HI'⟩ := by
    apply Fin.ext
    rfl
  rw [HE] at HV
  have HA := polynomial_at_key (parameters hn ht ha) (plan hn ht ha R) (data hn ht ha R)
    (packet (n := n) ctx i.val) (CoefficientMarkedRecordRowLayout.key (n := n) ctx (count ctx) [])
    (by simp only [IntegralMixedFramedCoordinateCharacteristicBits.key, packet, pairFst_pair])
    (source_active hn ht ha ctx i.val) ⟨i.val, HI'⟩ (packet_index ctx i.val).symm
  exact HV.trans HA.symm

end LeanCanny.Encoding.CoefficientMarkedRecordBankSource
