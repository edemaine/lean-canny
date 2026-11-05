/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordChoicePhysicalSpatial
public import LeanCanny.Encoding.CoefficientMarkedRecordRawCutMetadata
public import LeanCanny.Algebra.IntegralMixedCutCoefficientPolynomialKey
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalSelectorPullback
/-! # Actual full-factor probes use persistent physical scalar columns -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordTraceProbePhysical
open LeanCanny.Algebra LeanCanny.Computation Polynomial
open IntegralMixedFramedHistoryFamilyBits IntegralMixedFramedPhysicalLayoutCongruence
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def polynomial (P : IntegralCriticalHistoryTask.Parameters) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) (requested tau : ℕ) : MvPolynomial ℕ ℤ :=
  MvPolynomial.rename Fin.val (MvPolynomial.rename (IntegralFramedPhysicalSquare.sampler P D H key).scalar
    (IntegralMixedCutCoefficientPolynomialKey.polynomial (family P D H) (P.cap (pairFst key)+1) key tau requested))

private theorem native_eq (P : IntegralCriticalHistoryTask.Parameters) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) (requested tau : ℕ) :
    CoefficientMarkedRecordChoicePhysical.native (layout (commands P D key)) ((family P D H).state key)
      ((family P D H).birth_bound key) (CoefficientMarkedRecordCutSelection.familySelection (family P D H) key)
      requested tau = polynomial P D H key requested tau := by
  unfold CoefficientMarkedRecordChoicePhysical.native CoefficientMarkedRecordChoicePhysical.query
    CoefficientMarkedRecordChoiceFactor.nativeFactors CoefficientMarkedRecordCutSelection.familySelection
  rw [IntegralCoordinateBasis.polynomial_coefficient]
  unfold polynomial IntegralMixedCutCoefficientPolynomialKey.polynomial
  rw [MvPolynomial.rename_rename]
  rfl

theorem polynomial_planned (P : IntegralCriticalHistoryTask.Parameters) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (L F C : List Bool → ℕ)
    (key : List Bool) (requested tau : ℕ) :
    polynomial (IntegralMixedFramedNormalizationBits.planned P L F C)
      (IntegralMixedFramedNormalizationBits.plannedPlan P D L F C)
      (IntegralMixedFramedNormalizationBits.plannedData P D H L F C) key requested tau =
      polynomial P D H key requested tau := by
  dsimp only [polynomial, IntegralMixedCutCoefficientPolynomialKey.polynomial,
    IntegralFramedPhysicalSquare.sampler, IntegralMixedFramedHistoryFamilyBits.family]
  rw [IntegralMixedFramedCutPlanning.selection P D H L F C key]
  rfl

/-- An old scalar digit has the SAME natural physical column at every later
prefix, with its chronological scalar age shifted by exactly the suffix. -/
theorem scalar_suffix (P : IntegralCriticalHistoryTask.Parameters) (T : IntegralMixedHeaderTablesBits.Tables)
    (older terminal : List Bool) (hr : pairFst older = pairFst terminal)
    (hf : prefixLength P older ≤ prefixLength P terminal) (i : ℕ) (hi : i < prefixLength P older) :
    IntegralMixedFramedPhysicalIndex.scalarColumn P T
      (pair terminal (BinaryNatCode.encode (prefixLength P terminal-prefixLength P older+i))) =
    IntegralMixedFramedPhysicalIndex.scalarColumn P T (pair older (BinaryNatCode.encode i)) := by
  have ha : prefixLength P terminal-prefixLength P older+i ≤ prefixLength P terminal := by omega
  have he : prefixLength P terminal-(prefixLength P terminal-prefixLength P older+i) = prefixLength P older-i := by omega
  unfold IntegralMixedFramedPhysicalIndex.scalarColumn IntegralMixedFramedPhysicalIndex.columnPacket
    IntegralMixedFramedPhysicalIndex.retainedPrefix
  simp only [pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    min_eq_left ha, min_eq_left hi.le]
  rw [he]
  exact congrArg (fun z : ℕ => z-1)
    (IntegralMixedFramedPhysicalSelectorPullback.prefix_same P T terminal older hr.symm _)

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
  CoefficientMarkedRecordNative.run CoefficientMarkedRecordPrefix.build
  IntegralMixedSourceIntegerRecordAppend.plan

/-- The literal certified native probe is the specialization of the original
untruncated coefficient query on its own persistent physical columns. -/
theorem specializes {R : List Bool → ℕ} (hR : BinaryFn R) (ctx : List Bool) (k : ℕ)
    (hk : k < IntegralMixedCausalRecordPlanBits.count ctx)
    (hc : IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code ctx k) = false)
    (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ R ctx)
    (requested tau : ℕ) :
    MvPolynomial.map (evalRingHom ((2 : ℤ)^R ctx))
      (CoefficientMarkedRecordChoicePhysical.polynomial hn ht ha ctx k hk.le requested tau) =
    polynomial (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha hR)
      (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha hR)
      (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedData hn ht ha hR)
      (CoefficientMarkedRecordRowLayout.key (n := n) ctx k (BinaryNatCode.encode 2)) requested tau := by
  let P := IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha
  let D := IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R
  let H := IntegralMixedAuxiliaryMarkedRecordPlan.data hn ht ha R
  let key := CoefficientMarkedRecordRowLayout.key (n := n) ctx k (BinaryNatCode.encode 2)
  have he := congrFun (congrFun (CoefficientMarkedRecordChoicePhysical.specializes_family hn ht ha ctx R k hk hc
    (BinaryNatCode.encode 2) hlarge) requested) tau
  exact he.trans ((native_eq P D H key requested tau).trans
    (polynomial_planned P D H (fun _ => 3) (IntegralMixedAuxiliaryMarkedRecordPlan.factor hn ht ha)
      (IntegralMixedAuxiliaryMarkedIntegerPlan.seed hn ht ha hR) key requested tau).symm)

end LeanCanny.Encoding.CoefficientMarkedRecordTraceProbePhysical
