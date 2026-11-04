/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPrefixSnapshotCodedFactor
public import LeanCanny.Algebra.IntegralMixedFramedCutSelectionReceipt
/-! # Whole creating selections retain a chosen factor, exact degree, and root -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCutCreationReceipt
open LeanCanny.Encoding IntegralMixedHistory IntegralMixedRelativeCuts IntegralMixedFramedHistoryScript
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Data extends IntegralMixedPrefixSnapshot.Data where
 selected : IntegralMixedFullHistoryFamilyBits.Selection source

noncomputable def ofCommand {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) :IntegralMixedFullHistoryScript.Command P B→Option Data
 | .cut r k d ha _=>some ⟨IntegralMixedPrefixSnapshot.ofState x,⟨r,k,d,ha⟩⟩
 | _=>none

noncomputable def Data.HasRoot (d : Data) (values : ℕ→ℝ) (a : ℝ):Prop:=
 ∃hm : d.birth≤d.horizon,∃φ : d.state.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
   (∀i,φ (d.state.bank.numerator i)/(d.state.bank.denominator i:ℝ)=values i.val) ∧
   Valid d.state hm d.selected.rule φ d.selected.kind ∧
   ((factor d.state hm d.selected.rule d.selected.kind).map φ.toRingHom).natDegree=d.selected.degree ∧
   (factor d.state hm d.selected.rule d.selected.kind).eval₂ φ.toRingHom a=0

theorem coded_command {n S B m : ℕ} {P : SpatialSource n} {ι : Type}
    (x : State P S B m ι) (hn : 0<n) (labels : List Bool) (values : ℕ→ℝ) (a : ℝ) (code : List Bool)
    (hcap :IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (h : (IntegralMixedPrefixSnapshot.ofState x).CodedFactor labels values a code) :
    ∃receipt,ofCommand x ((IntegralMixedCausalUnitRecordBits.record P hn m code hcap).template.command
      (commonDenominator x) (commonDenominator_ne_zero x))=some receipt ∧receipt.HasRoot values a:=by
 obtain ⟨hr,φ,c,hφ,hv,_,hroot,hcode⟩:=h
 let d:=IntegralMixedChronologicalCutCode.rawData n m labels (WordListRecords.count labels+1)
   (WordListRecords.count labels+1) ((IntegralMixedPrefixSnapshot.ofState x).rawGood labels hr)
 let degree:=selectedDegree x hr.1 ((IntegralMixedPrefixSnapshot.ofState x).rule labels hr) φ c
 have HD :degree≤IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree:=selectedDegree_bound x hr.1 _ φ c
 change code=d.chosenCode (commonDenominator x) (commonDenominator_ne_zero x) c degree at hcode
 rw [hcode,IntegralMixedCutRecordConstructor.chosen_command d P (commonDenominator x) (commonDenominator_ne_zero x) c degree HD hcap]
 refine ⟨_,rfl,hr.1,φ,hφ,?_,?_,?_⟩
 · exact (IntegralMixedSweepRetarget.valid_iff x hr.1 _ _ φ c).mpr hv
 · rw [IntegralMixedSweepRetarget.factor_eq]
   rfl
 · rw [IntegralMixedSweepRetarget.factor_eq]
   exact hroot

end LeanCanny.Algebra.IntegralMixedCutCreationReceipt
