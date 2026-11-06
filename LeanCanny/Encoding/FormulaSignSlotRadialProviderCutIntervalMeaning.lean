/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderCutIntervalScalar
/-! # Actual provider interval statistics have exact selected-factor meaning -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderCutInterval
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false
private theorem selected_factor (p : Parameters) (d : Plan p)
    (h : IntegralMixedFramedHistoryFamilyBits.Data p d) (par : List Bool→List Bool) (q : List Bool)
    (φ : ((family p d h).state (IntegralMixedVirtualTaskBits.saved p (par q))).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) :
    IntegralMixedFramedFullCutIntervalSelected.factor p d h par q φ=
      (IntegralMixedRelativeCuts.factor ((family p d h).state (IntegralMixedVirtualTaskBits.saved p (par q)))
        ((family p d h).birth_bound _) ((family p d h).rule _) ((family p d h).kind _)).map φ.toRingHom := rfl

private theorem ordered_iff {A B C E : Prop} (h : A↔B∧C) (he : C→(B↔E)) :
    A↔C∧E :=
  ⟨fun a=>⟨(h.mp a).2,(he (h.mp a).2).mp (h.mp a).1⟩,
    fun a=>h.mpr ⟨(he a.1).mpr a.2,a.1⟩⟩

local notation "B" => FormulaSignSlotRadialProviderRecordPlan.bank
local notation "P" => IntegralFramedBankQuery.Bank.parameters FormulaSignSlotRadialProviderRecordPlan.bank
local notation "D" => IntegralFramedBankQuery.Bank.plan FormulaSignSlotRadialProviderRecordPlan.bank
local notation "H" => IntegralFramedBankQuery.Bank.data FormulaSignSlotRadialProviderRecordPlan.bank
local notation "G" => family P D H
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.bank
  IntegralMixedFramedHistoryFamilyBits.family parent endpoint Bounds IntervalGenerators sign head choice cap degree
  IntegralMixedFramedFullCutIntervalSelected.factor IntegralMixedRelativeCuts.Valid
  IntegralMixedRelativeCuts.CoefficientGuards

variable (q w : List Bool)
  (hw : SquareSampleCompleteVertices.Valid FormulaSignSlotRadialProviderAtomic.input q w)
  (hb : Bounds (pair q w))
local notation "old" => IntegralMixedVirtualTaskBits.saved P (parent q)
local notation "x" => IntegralMixedCutSource.Family.state G old
local notation "bound" => IntegralMixedCutSource.Family.birth_bound G old
local notation "rule" => IntegralMixedCutSource.Family.rule G old
local notation "kind" => IntegralMixedCutSource.Family.kind G old
local notation "polynomial" => IntegralMixedFramedFullCutIntervalSelected.factor P D H parent q

include hb in
theorem left_bound : selected false q<count q := by
  unfold Bounds at hb
  simpa only [pairFst_pair] using hb.1
include hb in
theorem right_bound : selected true q<count q := by
  unfold Bounds at hb
  simpa only [pairFst_pair] using hb.2.1

include hw hb in
theorem interpreted_guards (hg : Guards (pair q w)) :
    ∃φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,IntervalGenerators q w hw φ ∧
      IntegralMixedRelativeCuts.Valid x bound rule φ kind ∧ polynomial φ≠0 ∧
      (polynomial φ).natDegree=degree q := by
  have HP := interpreted_coefficients q w hw hb hg
  let φ := Classical.choose HP
  have hφ := (Classical.choose_spec HP).1
  have HC := (Classical.choose_spec HP).2
  have HV := IntegralMixedRelativeCuts.coefficientGuards_valid x bound rule φ kind ((G).degree old) HC
  have HZ : polynomial φ≠0 := by
    rw [selected_factor]
    exact IntegralMixedRelativeCuts.selected_nonzero x bound rule φ kind HV
  have HD : (polynomial φ).natDegree=degree q := by
    rw [selected_factor]
    exact (IntegralMixedRelativeCuts.coefficientGuards_degree x bound rule φ kind ((G).degree old) HC).trans (degree_eq q).symm
  exact ⟨φ,hφ,HV,HZ,HD⟩

include hw hb in
theorem comparison_iff_no_root
    (φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (hφ : IntervalGenerators q w hw φ)
    (hc : IntegralMixedRelativeCuts.CoefficientGuards x bound rule φ kind ((G).degree old))
    (hab : endpoint false q w hw (left_bound q w hb)<endpoint true q w hw (right_bound q w hb)) :
    pair q w∈comparison ↔ ∀t,(polynomial φ).eval t=0→
      t∉Set.Ioo (endpoint false q w hw (left_bound q w hb)) (endpoint true q w hw (right_bound q w hb)) := by
  have HV := IntegralMixedRelativeCuts.coefficientGuards_valid x bound rule φ kind ((G).degree old) hc
  have HZ : polynomial φ≠0 := by
    rw [selected_factor]
    exact IntegralMixedRelativeCuts.selected_nonzero x bound rule φ kind HV
  have HD : (polynomial φ).natDegree=degree q := by
    rw [selected_factor]
    exact (IntegralMixedRelativeCuts.coefficientGuards_degree x bound rule φ kind ((G).degree old) hc).trans (degree_eq q).symm
  have HAB := hab
  unfold endpoint at HAB
  have HE := IntegralFramedFullCutOpenInterval.empty_iff P D H (B).nodes (B).factor (B).seed (B).bounds
    parent (B).key degree (selected false) (selected true) (B).positive
    FormulaSignSlotRadialProviderAtomic.Cuts.factor_positive FormulaSignSlotRadialProviderAtomic.Cuts.fallback
    q w hw (terminal_fits q w hb) (active q w hb) φ (interval_generators_scalar q w hw hb φ hφ)
    HZ HD (degree_cap q) (left_bound q w hb) (right_bound q w hb) HAB
  simpa only [comparison,endpoint] using HE

include hw hb in
theorem interpreted_empty_iff (hg : Guards (pair q w)) :
    ∃φ : (x).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,IntervalGenerators q w hw φ ∧
      IntegralMixedRelativeCuts.Valid x bound rule φ kind ∧ polynomial φ≠0 ∧
      (polynomial φ).natDegree=degree q ∧
      (pair q w∈language ↔
        endpoint false q w hw (left_bound q w hb)<endpoint true q w hw (right_bound q w hb) ∧
        ∀t,(polynomial φ).eval t=0→t∉Set.Ioo
          (endpoint false q w hw (left_bound q w hb)) (endpoint true q w hw (right_bound q w hb))) := by
  have HP := interpreted_coefficients q w hw hb hg
  let φ := Classical.choose HP
  have hφ := (Classical.choose_spec HP).1
  have hc := (Classical.choose_spec HP).2
  have HV := IntegralMixedRelativeCuts.coefficientGuards_valid x bound rule φ kind ((G).degree old) hc
  have HZ : polynomial φ≠0 := by
    rw [selected_factor]
    exact IntegralMixedRelativeCuts.selected_nonzero x bound rule φ kind HV
  have HD : (polynomial φ).natDegree=degree q := by
    rw [selected_factor]
    exact (IntegralMixedRelativeCuts.coefficientGuards_degree x bound rule φ kind ((G).degree old) hc).trans (degree_eq q).symm
  refine ⟨φ,hφ,HV,HZ,HD,?_⟩
  have HM := language_iff_comparison q w hw hb hg
  exact ordered_iff HM (fun hab=>comparison_iff_no_root q w hw hb φ hφ hc hab)

end LeanCanny.Encoding.FormulaSignSlotRadialProviderCutInterval
