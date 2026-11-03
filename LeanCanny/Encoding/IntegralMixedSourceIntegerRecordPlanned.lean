/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedSourceIntegerRecordControls
/-! # Derived native budgets for the complete causal record backend

Planning changes resource ceilings, retaining literal sources, commands and
all saved births. Original record cells are rebuilt under the new task decoder;
no identification of differently packed task words is assumed.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedSourceIntegerRecordAppend
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory
open IntegralCriticalHistoryTask IntegralMixedFramedHistoryFamilyBits
open IntegralMixedFramedNormalizationBits (planned plannedPlan plannedData planned_access)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (P : Parameters) (S : (root : List Bool)→ℕ→SpatialSource (P.ambient root))
  (hn : ∀root,0<P.ambient root) (hd : ∀root b,(S root b).degree=P.degree root)
  (hcap : ∀root,IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
  (N : List Bool→ℕ)
  (hq : ∀root,PurePowerReductionBounds.dimension (P.ambient root+1) (S root 0).degree≤2^P.width root)
  (T : IntegerPolynomialRootQueriesBits.Source) (hz : ∀q,T.polynomial q≠0)
  (hT : ∀root i,T.degree (pair root (BinaryNatCode.encode i))≤2^P.width root)
  (hroom : ∀root,IntegralMixedCausalRecordPlanBits.count root+N root+2≤P.cap root+1)
  (hW : ∀root,(P.degree root).size≤P.sourceWidth root)

local notation "D" => plan P S hn hd hcap N T hz hT hroom
local notation "J" => data P S hn hd hcap N hq T hz hT hroom hW

theorem plan_planned (L F C : List Bool→ℕ) :
    plan (planned P L F C) S hn hd hcap N T hz hT hroom=plannedPlan P D L F C := rfl

theorem data_planned (L F C : List Bool→ℕ) :
    data (planned P L F C) S hn hd hcap N hq T hz hT hroom hW=plannedData P D J L F C := rfl

theorem snapshot_planned (R : BoundedFullWriter.Readers) (s : BoundedRegularFramedOriginalBits.Snapshot P D R)
    (L F C : List Bool→ℕ) :
    BoundedRegularFramedOriginalBits.Snapshot (planned P L F C)
      (plan (planned P L F C) S hn hd hcap N T hz hT hroom) R :=
  ⟨s.ambient,s.source⟩

noncomputable def plannedControls (a : Access P) (hN : UnaryFn N) (hA : IntegerPolynomialRootQueriesBits.Access T)
    (R : BoundedFullWriter.Readers) (hR : R.PolyTime)
    (scope : ∀key,(ETR.TermView.term (R.source key)).arity≤R.dim key)
    (s : BoundedRegularFramedOriginalBits.Snapshot P D R)
    (L F C : List Bool→ℕ) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C) :
    IntegralMixedFramedCurrentQNativeBits.Controls (planned P L F C) (plannedPlan P D L F C) (plannedData P D J L F C) :=
  currentQControls (planned P L F C) S hn hd hcap N hq T hz hT hroom hW (planned_access P a hL hF hC) hN hA
    R hR scope (snapshot_planned P S hn hd hcap N T hz hT hroom R s L F C) L F C hL hF hC

theorem plannedBounds (a : Access P) (hN : UnaryFn N) (hA : IntegerPolynomialRootQueriesBits.Access T)
    (R : BoundedFullWriter.Readers) (hR : R.PolyTime)
    (scope : ∀key,(ETR.TermView.term (R.source key)).arity≤R.dim key)
    (s : BoundedRegularFramedOriginalBits.Snapshot P D R)
    (L F C : List Bool→ℕ) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (hi : IntegralMixedFramedStepHeight.FamilyInputs P D L F C) (hf : ∀root,1≤F root) (hl : ∀root,1≤L root) :
    IntegralMixedFramedCurrentQNativeBits.Bounds (planned P L F C) (plannedPlan P D L F C) (plannedData P D J L F C)
      (plannedControls P S hn hd hcap N hq T hz hT hroom hW a hN hA R hR scope s L F C hL hF hC) where
  original:=IntegralMixedFramedNormalizationBits.planned_familyInputs P D L F C hi
  factor:=hf
  fallback:=fallback_bounds (planned P L F C) S hn hd hcap N hq T hz hT hroom hW L C hl
  modulus:=IntegralMixedFramedNormalizationBits.planned_budget P L F C

theorem planned_model_space (a : Access P) (hN : UnaryFn N) (hA : IntegerPolynomialRootQueriesBits.Access T)
    (R : BoundedFullWriter.Readers) (hR : R.PolyTime)
    (scope : ∀key,(ETR.TermView.term (R.source key)).arity≤R.dim key)
    (s : BoundedRegularFramedOriginalBits.Snapshot P D R)
    (L F C : List Bool→ℕ) (hL : BinaryFn L) (hF : BinaryFn F) (hC : BinaryFn C)
    (hi : IntegralMixedFramedStepHeight.FamilyInputs P D L F C) (hf : ∀root,1≤F root) (hl : ∀root,1≤L root) :
    SpaceFunction (IntegralMixedFramedCurrentQNativeBits.machine (planned P L F C)
      (planned_access P a hL hF hC) (plannedPlan P D L F C) (plannedData P D J L F C)
      (plannedControls P S hn hd hcap N hq T hz hT hroom hW a hN hA R hR scope s L F C hL hF hC)).model :=
  IntegralMixedFramedCurrentQNativeBits.model_space _ _ _ _ _
    (plannedBounds P S hn hd hcap N hq T hz hT hroom hW a hN hA R hR scope s L F C hL hF hC hi hf hl)

end LeanCanny.Encoding.IntegralMixedSourceIntegerRecordAppend
