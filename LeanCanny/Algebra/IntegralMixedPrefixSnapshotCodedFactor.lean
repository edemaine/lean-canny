/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPrefixSnapshotBad
public import LeanCanny.Encoding.IntegralMixedChronologicalCutRetarget
public import LeanCanny.Encoding.IntegralMixedChosenCutRecordBounds
/-! # A selected ordinary bad factor has an exact chosen-degree byte witness -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPrefixSnapshot
open LeanCanny.Encoding IntegralMixedHistory IntegralMixedRelativeCuts
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def Data.CodedFactor (d : Data) (labels : List Bool) (values : ℕ→ℝ) (a : ℝ) (code : List Bool) :Prop:=
 ∃hr : d.Ready labels,∃φ : d.state.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
 ∃c : Kind d.source (d.rule labels hr),
   (∀i,φ (d.state.bank.numerator i)/(d.state.bank.denominator i:ℝ)=values i.val) ∧
   Valid d.state hr.1 (d.rule labels hr) φ c ∧
   IntegralMixedSelectedBadMembership.Ordinary (d.rule labels hr) c ∧
   (factor d.state hr.1 (d.rule labels hr) c).eval₂ φ.toRingHom a=0 ∧
   code=(IntegralMixedChronologicalCutCode.rawData d.ambient d.birth labels
     (WordListRecords.count labels+1) (WordListRecords.count labels+1) (d.rawGood labels hr)).chosenCode
       (commonDenominator d.state) (commonDenominator_ne_zero d.state) c
       (selectedDegree d.state hr.1 (d.rule labels hr) φ c)

theorem Data.mem_bad_iff_coded (d : Data) (labels : List Bool) (values : ℕ→ℝ) (hx : Canonical d.state) (a : ℝ) :
    a∈d.bad labels values ↔∃code,d.CodedFactor labels values a code:=by
 constructor
 · intro H
   unfold Data.bad at H
   split_ifs at H with hr
   · obtain ⟨φ,hφ,cs,hc⟩:=H
     obtain ⟨c,hv,ho,hroot⟩:=(IntegralMixedSelectedBadMembership.mem_bad_iff d.state hr.1 (d.rule labels hr) φ cs a).mp hc
     exact ⟨_,hr,φ,c,hφ,hv,ho,hroot,rfl⟩
   · exact H.elim
 · rintro ⟨code,hr,φ,c,hφ,hv,ho,hroot,_⟩
   exact (d.mem_bad_factor_iff labels values hr hx φ hφ a).mpr ⟨c,hv,ho,hroot⟩

theorem Data.coded_values_congr (d : Data) (labels : List Bool) (values other : ℕ→ℝ) (a : ℝ) (code : List Bool)
    (h : ∀i<d.birth,values i=other i) :d.CodedFactor labels values a code↔d.CodedFactor labels other a code:=by
 constructor <;> rintro ⟨hr,φ,c,hφ,hv,ho,hroot,hcode⟩
 · exact ⟨hr,φ,c,fun i=>(hφ i).trans (h i.val i.isLt),hv,ho,hroot,hcode⟩
 · exact ⟨hr,φ,c,fun i=>(hφ i).trans (h i.val i.isLt).symm,hv,ho,hroot,hcode⟩

theorem Data.coded_transport (d e : Data) (he : d=e) (labels : List Bool)
    (values other : ℕ→ℝ) (a : ℝ) (code : List Bool) (h : ∀i<d.birth,values i=other i) :
    d.CodedFactor labels values a code↔e.CodedFactor labels other a code:=by
 subst e
 exact d.coded_values_congr labels values other a code h

theorem Data.coded_length (d : Data) (labels : List Bool) (values : ℕ→ℝ) (a : ℝ) (code : List Bool)
    (hcap :IntegralMixedExceptionalBounds.auxiliaryCap (d.ambient+1) d.source.degree≤2^d.width)
    (h : d.CodedFactor labels values a code) :code.length≤IntegralMixedCutRecordConstructor.codeBudget d.ambient d.birth d.width:=by
 obtain ⟨hr,φ,c,_,_,_,_,hc⟩:=h
 rw [hc]
 exact IntegralMixedCutRecordConstructor.Data.chosenCode_length _ d.source _ _ c _
   (selectedDegree_bound d.state hr.1 (d.rule labels hr) φ c) hcap

end LeanCanny.Algebra.IntegralMixedPrefixSnapshot
