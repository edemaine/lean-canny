/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderCutIntervalCoefficients
/-! # The interval coefficient interpretation uses the actual scalar prefix -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderCutInterval
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem extend_embed {n m : ℕ} (h : n≤m) (z : Fin m→ℝ) (i : Fin n) :
    IntegralMixedFramedBankObservation.extend z (i.val+(m-n))=z (UniformIntegralPowerSchedule.embed h i) := by
  have HI : i.val+(m-n)<m := by have H := i.isLt;omega
  unfold IntegralMixedFramedBankObservation.extend
  rw [dite_eq_left HI]
  apply congrArg z
  apply Fin.ext
  exact Nat.add_comm _ _

private theorem family_cap (a : Parameters) (d : Plan a) (h : IntegralMixedFramedHistoryFamilyBits.Data a d) (k : List Bool) :
    (family a d h).cap k=a.cap (pairFst k)+1 := rfl

private theorem raw_embed (BB : IntegralFramedBankQuery.Bank) (q w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input BB) q w)
    (n t : ℕ) (h : n≤(family BB.parameters BB.plan BB.data).birth (BB.key q))
    (ht : t=(family BB.parameters BB.plan BB.data).birth (BB.key q)) (i : Fin n) :
    IntegralFramedPhysicalSuffixTest.rawTuple BB q w hv (i.val+(t-n))=
      IntegralFramedPhysicalSquare.scalarTuple BB.parameters BB.plan BB.data BB.nodes BB.factor BB.seed BB.bounds
        BB.key BB.positive q w hv (UniformIntegralPowerSchedule.embed h i) := by
  subst t
  unfold IntegralFramedPhysicalSuffixTest.rawTuple
  exact extend_embed h _ i

local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P" => IntegralFramedBankQuery.Bank.parameters FormulaSignSlotRadialProviderRecordPlan.bank
local notation "D" => IntegralFramedBankQuery.Bank.plan FormulaSignSlotRadialProviderRecordPlan.bank
local notation "H" => IntegralFramedBankQuery.Bank.data FormulaSignSlotRadialProviderRecordPlan.bank
local notation "G" => family P D H
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank family parent
  IntegralFramedPhysicalSuffixTest.rawTuple

theorem terminal_fits (q w : List Bool) (hb : Bounds (pair q w)) :
    IntegralMixedFramedFullCutTerminalHead.Valid P D H parent (B).key q := by
  change (G).birth (IntegralMixedVirtualTaskBits.saved P (parent q))≤count q
  rw [←bank_birth]
  exact fits q w hb

variable (q w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid FormulaSignSlotRadialProviderAtomic.input q w)
    (hb : Bounds (pair q w))
local notation "old" => IntegralMixedVirtualTaskBits.saved P (parent q)
local notation "x" => IntegralMixedCutSource.Family.state G old

theorem interval_generators_scalar
    (φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (hφ : IntervalGenerators q w hw φ) :
    ∀i,φ ((x).sampler.scalarPrefix.basis.generator i)=
      IntegralFramedPhysicalSquare.scalarTuple P D H (B).nodes (B).factor (B).seed (B).bounds (B).key (B).positive q w hw
        (UniformIntegralPowerSchedule.embed (terminal_fits q w hb) i)^
        UniformIntegralPowerSchedule.weights ((P).cap (pairFst old)+1) (2^(G).width old) ((G).birth old) i := by
  have HC : IntegralFramedTerminalCutTest.count P D H (IntegralFramedPhysicalTraceCutSource.taskKey B) (parent q)=
      (G).birth ((B).key q) := by
    rw [parent_eq]
    exact IntegralFramedPhysicalTraceCutSource.count_parent B FormulaSignSlotRadialProviderAtomic.Cuts.key_context q (birthWord q)
  have HH0 := IntegralFramedPhysicalTraceCutSource.parent_horizon B q (birthWord q)
  rw [←parent_eq q] at HH0
  have HH : IntegralMixedFramedChoiceProbeSourceBits.horizon P (parent q)=(P).cap (pairFst old)+1 :=
    HH0.symm.trans (family_cap P D H old)
  intro i
  have HX : IntegralFramedPhysicalSuffixTest.rawTuple B q w hw
      (i.val+(IntegralFramedTerminalCutTest.count P D H (IntegralFramedPhysicalTraceCutSource.taskKey B) (parent q)-(G).birth old))=
      IntegralFramedPhysicalSquare.scalarTuple P D H (B).nodes (B).factor (B).seed (B).bounds (B).key (B).positive q w hw
        (UniformIntegralPowerSchedule.embed (terminal_fits q w hb) i) := by
    exact raw_embed B q w hw _ _ (terminal_fits q w hb) HC i
  have HP : UniformIntegralPowerSchedule.weights (IntegralMixedFramedChoiceProbeSourceBits.horizon P (parent q))
      (2^(G).width old) ((G).birth old) i=
      UniformIntegralPowerSchedule.weights ((P).cap (pairFst old)+1) (2^(G).width old) ((G).birth old) i := by
    rw [HH]
  exact (hφ i).trans (congrArg₂ (fun (v : ℝ) (e : ℕ)=>v^e) HX HP)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderCutInterval
