/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordFullCutPrincipal
public import LeanCanny.Encoding.IntegralMixedPhysicalCutOpenInterval
/-! # Full-cut principals at literal native interval contexts -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordFullCutInstalled
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask Polynomial
open IntegralMixedAuxiliaryMarkedRecordPlan (certifiedParameters certifiedPlan certifiedData)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem principal_at (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (L F C : List Bool → ℕ)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (parent terminal : List Bool → List Bool) (d index : List Bool → ℕ)
    (power : Fin 3) (negative : Bool) (q : List Bool) (j : ℕ) :
    FixedWidthTarskiPrincipalBits.polynomial
      (IntegralMixedFramedFullCutIntervalFamily.family P D H L F C hs parent terminal d index (fun _ => power) negative) q j =
    FixedWidthTarskiPrincipalBits.polynomial
      (IntegralMixedFramedFullCutIntervalFamily.family P D H L F C hs
        (fun _ => parent q) (fun _ => terminal q) (fun _ => d q) (fun _ => index q) (fun _ => power) negative) [] j := rfl

private theorem principal_constants (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (L F C : List Bool → ℕ)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (parent parent' terminal terminal' : List Bool) (d d' index index' : ℕ)
    (power : Fin 3) (negative : Bool) (j : ℕ)
    (hp : parent = parent') (ht : terminal = terminal') (hd : d = d') (hi : index = index') :
    HEq (FixedWidthTarskiPrincipalBits.polynomial
      (IntegralMixedFramedFullCutIntervalFamily.family P D H L F C hs
        (fun _ => parent) (fun _ => terminal) (fun _ => d) (fun _ => index) (fun _ => power) negative) [] j)
      (FixedWidthTarskiPrincipalBits.polynomial
      (IntegralMixedFramedFullCutIntervalFamily.family P D H L F C hs
        (fun _ => parent') (fun _ => terminal') (fun _ => d') (fun _ => index') (fun _ => power) negative) [] j) := by
  cases hp
  cases ht
  cases hd
  cases hi
  rfl

def context {n : List Bool → ℕ} (ctx : List Bool) (k left right : ℕ) :=
  pair ctx (pair (List.replicate (CoefficientMarkedRecordCutSource.birth (n := n) ctx k) true)
    (pair (BinaryNatCode.encode left) (BinaryNatCode.encode right)))

theorem context_root {n : List Bool → ℕ} (ctx : List Bool) (k left right : ℕ) :
    pairFst (context (n := n) ctx k left right) = ctx := pairFst_pair _ _

theorem context_selected {n : List Bool → ℕ} (ctx : List Bool) (k left right : ℕ) (side : Bool) :
    IntegralMixedPhysicalCutOpenInterval.selected side (context (n := n) ctx k left right) =
      if side then right else left := by
  cases side <;> simp only [IntegralMixedPhysicalCutOpenInterval.selected, context,
    pairFst_pair, pairSnd_pair, Bool.false_eq_true, ite_false, ite_true,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)
  {R : List Bool → ℕ} (hR : BinaryFn R)
local notation "B" => IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false
local notation "PC" => certifiedParameters hn ht ha hR
local notation "DC" => certifiedPlan hn ht ha hR
local notation "HC" => certifiedData hn ht ha hR

attribute [local irreducible] IntegralMixedFramedHistoryFamilyBits.family
  IntegralMixedSourceIntegerRecordAppend.plan IntegralMixedSourceIntegerRecordAppend.data
  IntegralMixedAuxiliaryMarkedIntegerPlan.seed

theorem parent_context (ctx : List Bool) (k left right : ℕ) :
    IntegralMixedPhysicalCutOpenInterval.parent hn ht ha hR false (context (n := n) ctx k left right) =
      CoefficientMarkedRecordRawCutMetadata.parent hn ht ha hR ctx k := by
  simp only [IntegralMixedPhysicalCutOpenInterval.parent, IntegralMixedPhysicalCutOpenInterval.birthWord,
    context, pairFst_pair, pairSnd_pair]
  rfl

theorem terminal_context (ctx : List Bool) (k left right : ℕ) :
    (B).key (context (n := n) ctx k left right) = CoefficientMarkedRecordRawCutMetadata.terminal (n := n) ctx := by
  change IntegralMixedAuxiliaryMarkedRecordPlan.bankKey n (context (n := n) ctx k left right) = _
  simp only [IntegralMixedAuxiliaryMarkedRecordPlan.bankKey, context_root,
    CoefficientMarkedRecordRawCutMetadata.terminal, CoefficientMarkedRecordRowLayout.key,
    IntegralMixedAuxiliaryMarkedRecordPlan.fullCount, CoefficientMarkedPreludeActual.indices_length]

theorem degree_context (ctx : List Bool) (k left right : ℕ)
    (hk : k < IntegralMixedCausalRecordPlanBits.count ctx)
    (hc : IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code ctx k) = false) :
    IntegralMixedPhysicalCutOpenInterval.degree hn ht ha hR false (context (n := n) ctx k left right) =
      (CoefficientMarkedRecordCutSource.cut hn ht ha ctx k).degree := by
  rw [IntegralMixedPhysicalCutOpenInterval.degree_eq, parent_context hn ht ha hR ctx k left right]
  exact CoefficientMarkedRecordRawCutMetadata.declared_degree hn ht ha hR ctx k hk hc

/-- This is the actual family used by the native NoBad comparison, evaluated
at its literal interval context. The native comparison uses power one. -/
noncomputable def installedFamily (side : Bool) (power : Fin 3) (negative : Bool) :=
  IntegralFramedFullCutIntervalStatistic.mf (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
    (IntegralMixedPhysicalCutOpenInterval.parent hn ht ha hR false) (B).key
    (IntegralMixedPhysicalCutOpenInterval.degree hn ht ha hR false)
    (IntegralMixedPhysicalCutOpenInterval.selected side) power negative

theorem specializes (ctx : List Bool) (k : ℕ) (hk : k < IntegralMixedCausalRecordPlanBits.count ctx)
    (hc : IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code ctx k) = false)
    (left right : ℕ) (side : Bool) (power : Fin 3) (negative : Bool)
    (hlarge : CoefficientMarkedRecordEffectiveCutoff.effectiveCutoff hn ht ha ctx ≤ R ctx) (j : ℕ) :
    HEq (MvPolynomial.map (evalRingHom ((2 : ℤ)^R ctx))
      (CoefficientMarkedRecordFullCutPrincipal.polynomial hn ht ha ctx k hk
        (if side then right else left) power negative j))
      (FixedWidthTarskiPrincipalBits.polynomial (installedFamily hn ht ha hR side power negative)
        (context (n := n) ctx k left right) j) := by
  have HP := principal_at (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
    (IntegralMixedPhysicalCutOpenInterval.parent hn ht ha hR false) (B).key
    (IntegralMixedPhysicalCutOpenInterval.degree hn ht ha hR false)
    (IntegralMixedPhysicalCutOpenInterval.selected side) power negative (context (n := n) ctx k left right) j
  have HT := principal_constants (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed (B).bounds
    _ _ _ _ _ _ _ _ power negative j
    (parent_context hn ht ha hR ctx k left right) (terminal_context hn ht ha hR ctx k left right)
    (degree_context hn ht ha hR ctx k left right hk hc) (context_selected (n := n) ctx k left right side)
  have HAll := (heq_of_eq HP).trans HT
  have HM := CoefficientMarkedRecordFullCutPrincipal.specializes hn ht ha hR ctx k hk hc
    (if side then right else left) power negative hlarge j
  exact HM.trans HAll.symm

end LeanCanny.Encoding.CoefficientMarkedRecordFullCutInstalled
