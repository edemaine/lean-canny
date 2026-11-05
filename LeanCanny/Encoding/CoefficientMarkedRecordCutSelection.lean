/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.CoefficientMarkedRecordRuleSelection
public import LeanCanny.Algebra.IntegralMixedRelativeCutChoice
/-! # The actual saved cut rule and kind are the computed-current-Q causal choice -/
@[expose] public section
namespace LeanCanny.Encoding.CoefficientMarkedRecordCutSelection
open LeanCanny.Algebra LeanCanny.Computation IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedCausalRecordBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure KindSelection {n : ℕ} (P : SpatialSource n) where
  rule : IntegralMixedCriticalSweep.Rule n
  kind : IntegralMixedRelativeCuts.Kind P rule

private def choiceOfSelection {n : ℕ} {P : SpatialSource n}
    (s : IntegralMixedFullHistoryFamilyBits.Selection P) : KindSelection P := ⟨s.rule, s.kind⟩

private noncomputable def selectionOf {a B : ℕ} (c : Instruction a B)
    (fallback : IntegralMixedFullHistoryFamilyBits.Selection c.source) :
    IntegralMixedFullHistoryFamilyBits.Selection c.source :=
  match c.command with
  | .cut r k d hd _ => ⟨r, k, d, hd⟩
  | _ => fallback

private theorem selected_selection {a b B C : ℕ} (x : Instruction a B) (y : Instruction b C)
    (en : a = b) (eB : B = C) (hi : HEq x y)
    (fallback : IntegralMixedFullHistoryFamilyBits.Selection y.source)
    (r : IntegralMixedCriticalSweep.Rule a) (k : IntegralMixedRelativeCuts.Kind x.source r) (d : ℕ)
    (hs : d ≤ IntegralMixedExceptionalBounds.auxiliaryCap (a + 1) x.source.degree) (hd : d ≤ 2 ^ B)
    (hc : x.command = .cut r k d hs hd) : HEq (⟨r, k⟩ : KindSelection x.source) (choiceOfSelection (selectionOf y fallback)) := by
  cases en
  cases eB
  cases eq_of_heq hi
  unfold selectionOf
  rw [hc]
  rfl

private theorem family_ambient (P : IntegralCriticalHistoryTask.Parameters)
    (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) :
    (IntegralMixedFramedHistoryFamilyBits.family P D H).ambient key = P.ambient (pairFst key) := rfl

private theorem family_width (P : IntegralCriticalHistoryTask.Parameters)
    (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) :
    (IntegralMixedFramedHistoryFamilyBits.family P D H).width key = P.width (pairFst key) := rfl

noncomputable def familySelection (F : IntegralMixedCutSource.Family) (key : List Bool) :
    KindSelection (F.spatial key) :=
  ⟨F.rule key, F.kind key⟩

private theorem family_selection (P : IntegralCriticalHistoryTask.Parameters)
    (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) :
    HEq (choiceOfSelection (selectionOf (IntegralMixedFramedHistoryFamilyBits.instruction P D key) (H.fallback key)))
      (familySelection (IntegralMixedFramedHistoryFamilyBits.family P D H) key) := by
  simp only [familySelection, choiceOfSelection, IntegralMixedFramedHistoryFamilyBits.family,
    IntegralMixedFramedHistoryFamilyBits.selection, selectionOf]
  cases (IntegralMixedFramedHistoryFamilyBits.instruction P D key).command <;> rfl

private theorem unit_command {a S B m : ℕ} {P : SpatialSource a} {I : Type}
    (x : State P S B m I) (hp : 0 < a) (code : List Bool)
    (hP : IntegralMixedExceptionalBounds.auxiliaryCap (a + 1) P.degree ≤ 2 ^ B)
    (hc : IntegralMixedUnitRecordCode.critical code = false) :
    (instantiate x (IntegralMixedCausalUnitRecordBits.record P hp m code hP)).command =
      (Template.cut (IntegralMixedCausalUnitRecordBits.cut P hp m code hP)).command
        (commonDenominator x) (commonDenominator_ne_zero x) := by
  unfold instantiate IntegralMixedCausalUnitRecordBits.record
  simp only [hc, Bool.false_eq_true, ite_false]

private theorem selected_degree {a b B C : ℕ} (x : Instruction a B) (y : Instruction b C)
    (en : a = b) (eB : B = C) (hi : HEq x y)
    (fallback : IntegralMixedFullHistoryFamilyBits.Selection y.source)
    (r : IntegralMixedCriticalSweep.Rule a) (k : IntegralMixedRelativeCuts.Kind x.source r) (d : ℕ)
    (hs : d ≤ IntegralMixedExceptionalBounds.auxiliaryCap (a + 1) x.source.degree) (hd : d ≤ 2 ^ B)
    (hc : x.command = .cut r k d hs hd) : d = (selectionOf y fallback).degree := by
  cases en
  cases eB
  cases eq_of_heq hi
  unfold selectionOf
  rw [hc]

private theorem family_degree (P : IntegralCriticalHistoryTask.Parameters)
    (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) :
    (selectionOf (IntegralMixedFramedHistoryFamilyBits.instruction P D key) (H.fallback key)).degree =
      (IntegralMixedFramedHistoryFamilyBits.family P D H).degree key := by
  simp only [IntegralMixedFramedHistoryFamilyBits.family, IntegralMixedFramedHistoryFamilyBits.selection, selectionOf]
  cases (IntegralMixedFramedHistoryFamilyBits.instruction P D key).command <;> rfl

variable {n : List Bool → ℕ} {t : List Bool → LeanCanny.ETR.Term}
  (hn : UnaryFn n) (ht : (fun q => (t q).toData.toBits) ∈ FP) (ha : ∀ q, (t q).arity ≤ n q)

attribute [local irreducible] CoefficientMarkedRecordNative.run CoefficientMarkedRecordPrefix.build
  IntegralMixedSourceIntegerRecordAppend.plan

theorem selection_heq (ctx : List Bool) (R : List Bool → ℕ) (k : ℕ)
    (hk : k < IntegralMixedCausalRecordPlanBits.count ctx)
    (hc : IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code ctx k) = false) (aux : List Bool) :
    let x := CoefficientMarkedRecordCutSource.state hn ht ha ctx R k hk.le
    let c := CoefficientMarkedRecordNative.cut hn ht ha ctx R (CoefficientMarkedRecordCutSource.birth (n := n) ctx k)
      (IntegralMixedCausalRecordPlanBits.code ctx k)
    HEq (⟨c.rule (commonDenominator x) (commonDenominator_ne_zero x),
      c.kind (commonDenominator x) (commonDenominator_ne_zero x)⟩ :
      KindSelection (CoefficientMarkedRecordNative.source (n := n) (t := t) ctx R))
      (familySelection (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.actualFamily hn ht ha R)
        (CoefficientMarkedRecordRowLayout.key (n := n) ctx k aux)) := by
  let P := IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha
  let D := IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R
  let H := IntegralMixedAuxiliaryMarkedRecordPlan.data hn ht ha R
  let key := CoefficientMarkedRecordRowLayout.key (n := n) ctx k aux
  let x := CoefficientMarkedRecordCutSource.state hn ht ha ctx R k hk.le
  let c := CoefficientMarkedRecordNative.cut hn ht ha ctx R (CoefficientMarkedRecordCutSource.birth (n := n) ctx k)
    (IntegralMixedCausalRecordPlanBits.code ctx k)
  let ix := CoefficientMarkedRecordNative.instruction hn ht ha ctx R x (IntegralMixedCausalRecordPlanBits.code ctx k)
  let iy := IntegralMixedFramedHistoryFamilyBits.instruction P D key
  have HI := CoefficientMarkedRecordRuleSelection.instruction_heq hn ht ha ctx R k hk aux
  have HC := unit_command x (by change 0 < IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx + 3; omega)
    (IntegralMixedCausalRecordPlanBits.code ctx k) (CoefficientMarkedRecordNative.source_cap hn ht ha ctx R) hc
  change ix.command = (Template.cut c).command (commonDenominator x) (commonDenominator_ne_zero x) at HC
  have HR := selected_selection ix iy
    ((CoefficientMarkedRecordRows.family_ambient hn ht ha ctx R k aux).trans (family_ambient P D H key))
    ((CoefficientMarkedRecordRows.family_width hn ht ha ctx R k aux).trans (family_width P D H key))
    HI.symm (H.fallback key)
    (c.rule (commonDenominator x) (commonDenominator_ne_zero x))
    (c.kind (commonDenominator x) (commonDenominator_ne_zero x)) c.degree c.source_cap c.degree_cap
    (by simpa only [Template.command] using HC)
  exact HR.trans (family_selection P D H key)

/-- The declared degree is read from the same literal cut instruction. -/
theorem native_degree_eq (ctx : List Bool) (R : List Bool → ℕ) (k : ℕ)
    (hk : k < IntegralMixedCausalRecordPlanBits.count ctx)
    (hc : IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code ctx k) = false) (aux : List Bool) :
    (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.actualFamily hn ht ha R).degree
      (CoefficientMarkedRecordRowLayout.key (n := n) ctx k aux) =
      (CoefficientMarkedRecordNative.cut hn ht ha ctx R (CoefficientMarkedRecordCutSource.birth (n := n) ctx k)
        (IntegralMixedCausalRecordPlanBits.code ctx k)).degree := by
  let P := IntegralMixedAuxiliaryMarkedRecordPlan.parameters hn ht ha
  let D := IntegralMixedAuxiliaryMarkedRecordPlan.plan hn ht ha R
  let H := IntegralMixedAuxiliaryMarkedRecordPlan.data hn ht ha R
  let key := CoefficientMarkedRecordRowLayout.key (n := n) ctx k aux
  let x := CoefficientMarkedRecordCutSource.state hn ht ha ctx R k hk.le
  let c := CoefficientMarkedRecordNative.cut hn ht ha ctx R (CoefficientMarkedRecordCutSource.birth (n := n) ctx k)
    (IntegralMixedCausalRecordPlanBits.code ctx k)
  let ix := CoefficientMarkedRecordNative.instruction hn ht ha ctx R x (IntegralMixedCausalRecordPlanBits.code ctx k)
  let iy := IntegralMixedFramedHistoryFamilyBits.instruction P D key
  have HI := CoefficientMarkedRecordRuleSelection.instruction_heq hn ht ha ctx R k hk aux
  have HC := unit_command x (by change 0 < IntegralMixedAuxiliaryMarkedIntegerSource.number n ctx + 3; omega)
    (IntegralMixedCausalRecordPlanBits.code ctx k) (CoefficientMarkedRecordNative.source_cap hn ht ha ctx R) hc
  change ix.command = (Template.cut c).command (commonDenominator x) (commonDenominator_ne_zero x) at HC
  have HD := selected_degree ix iy
    ((CoefficientMarkedRecordRows.family_ambient hn ht ha ctx R k aux).trans (family_ambient P D H key))
    ((CoefficientMarkedRecordRows.family_width hn ht ha ctx R k aux).trans (family_width P D H key))
    HI.symm (H.fallback key)
    (c.rule (commonDenominator x) (commonDenominator_ne_zero x))
    (c.kind (commonDenominator x) (commonDenominator_ne_zero x)) c.degree c.source_cap c.degree_cap
    (by simpa only [Template.command] using HC)
  exact (HD.trans (family_degree P D H key)).symm

/-- Radius and AUX do not change the canonical declared factor degree. -/
theorem degree_eq (ctx : List Bool) (R : List Bool → ℕ) (k : ℕ)
    (hk : k < IntegralMixedCausalRecordPlanBits.count ctx)
    (hc : IntegralMixedUnitRecordCode.critical (IntegralMixedCausalRecordPlanBits.code ctx k) = false) (aux : List Bool) :
    (IntegralMixedAuxiliaryMarkedRecordRadiusHeight.actualFamily hn ht ha R).degree
      (CoefficientMarkedRecordRowLayout.key (n := n) ctx k aux) =
      (CoefficientMarkedRecordCutSource.cut hn ht ha ctx k).degree := by
  rw [native_degree_eq hn ht ha ctx R k hk hc aux]
  have HT := CoefficientMarkedRecordBirthSpecialization.cut_transport hn ht ha ctx R
    (CoefficientMarkedRecordCutSource.birth (n := n) ctx k) (IntegralMixedCausalRecordPlanBits.code ctx k)
  exact (congrArg (fun c => c.degree) HT).symm

end LeanCanny.Encoding.CoefficientMarkedRecordCutSelection
