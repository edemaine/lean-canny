/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPrefixSnapshot
public import LeanCanny.Algebra.IntegralMixedSelectedBadMembership
public import LeanCanny.Geometry.IntegralMixedBankValueInterpretation
public import LeanCanny.Encoding.IntegralMixedChronologicalCutRaw
/-! # The ordinary chronological bad set is fixed by actual bank quotients

The interpretation is existential in the definition, and on a canonical
state every interpretation with those quotient values is the same.  The
classical factor choices are likewise immaterial.  No physical raw tuple
or independently chosen root is an argument of the bad set.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPrefixSnapshot
open LeanCanny.Encoding LeanCanny.Geometry IntegralMixedHistory IntegralMixedCriticalSweep
open IntegralMixedRelativeCuts LeanCanny.Connectivity.IntegralMixedSelectedCriticalCuts
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def Data.Ready (d : Data) (labels : List Bool) : Prop:=
 d.birth≤d.horizon ∧ IntegralMixedChronologicalFrameCode.Good d.ambient d.birth labels ∧
 WordListRecords.count labels+1<d.ambient+1

theorem Data.rawGood (d : Data) (labels : List Bool) (h : d.Ready labels) :
    IntegralMixedChronologicalCutCode.Good d.ambient d.birth labels
      (WordListRecords.count labels+1) (WordListRecords.count labels+1):=
 ⟨h.2.1,le_refl _,h.2.2,le_refl _,h.2.2⟩

noncomputable def Data.rule (d : Data) (labels : List Bool) (h : d.Ready labels) : Rule d.ambient:=
 (IntegralMixedChronologicalCutCode.rawData d.ambient d.birth labels
   (WordListRecords.count labels+1) (WordListRecords.count labels+1) (d.rawGood labels h)).rule
   (commonDenominator d.state) (commonDenominator_ne_zero d.state)

noncomputable def Data.bad (d : Data) (labels : List Bool) (values : ℕ→ℝ) : Set ℝ:=
 if h : d.Ready labels then
   {a | ∃φ : d.state.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
     (∀i,φ (d.state.bank.numerator i)/(d.state.bank.denominator i:ℝ)=values i.val) ∧
     ∃c : Choices d.state h.1 (d.rule labels h) φ,
       a∈LeanCanny.Connectivity.IntegralMixedSelectedCriticalCuts.bad d.state h.1 (d.rule labels h) φ c}
 else ∅

theorem Data.mem_bad_iff (d : Data) (labels : List Bool) (values : ℕ→ℝ)
    (hr : d.Ready labels) (hx : Canonical d.state)
    (φ : d.state.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀i,φ (d.state.bank.numerator i)/(d.state.bank.denominator i:ℝ)=values i.val)
    (c : Choices d.state hr.1 (d.rule labels hr) φ) (a : ℝ) :
    a∈d.bad labels values ↔ a∈LeanCanny.Connectivity.IntegralMixedSelectedCriticalCuts.bad
      d.state hr.1 (d.rule labels hr) φ c:=by
 simp only [Data.bad,dite_eq_left hr,Set.mem_ofPred_eq]
 constructor
 · rintro ⟨ψ,hψ,e,he⟩
   have HE : ψ=φ:=IntegralMixedBankValueInterpretation.hom_ext d.state hx ψ φ
     (fun i=>(hψ i).trans (hφ i).symm)
   subst ψ
   rw [IntegralMixedCurrentQCoordinateScaling.bad_choices_eq d.state hr.1 (d.rule labels hr) φ e c] at he
   exact he
 · exact fun h=>⟨φ,hφ,c,h⟩

theorem Data.mem_bad_factor_iff (d : Data) (labels : List Bool) (values : ℕ→ℝ)
    (hr : d.Ready labels) (hx : Canonical d.state)
    (φ : d.state.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ : ∀i,φ (d.state.bank.numerator i)/(d.state.bank.denominator i:ℝ)=values i.val)
    (a : ℝ) :
    a∈d.bad labels values ↔ ∃k : Kind d.source (d.rule labels hr),
      Valid d.state hr.1 (d.rule labels hr) φ k ∧
      IntegralMixedSelectedBadMembership.Ordinary (d.rule labels hr) k ∧
      (factor d.state hr.1 (d.rule labels hr) k).eval₂ φ.toRingHom a=0:=by
 obtain ⟨c⟩:=exists_choices d.state hr.1 (d.rule labels hr) φ
 exact (d.mem_bad_iff labels values hr hx φ hφ c a).trans
   (IntegralMixedSelectedBadMembership.mem_bad_iff d.state hr.1 (d.rule labels hr) φ c a)

theorem Data.bad_values_congr (d : Data) (labels : List Bool) (values other : ℕ→ℝ)
    (h : ∀i<d.birth,values i=other i) : d.bad labels values=d.bad labels other:=by
 unfold Data.bad
 split_ifs with hr
 · ext a
   constructor <;> rintro ⟨φ,hφ,c,hc⟩
   · exact ⟨φ,fun i=>(hφ i).trans (h i.val i.isLt),c,hc⟩
   · exact ⟨φ,fun i=>(hφ i).trans (h i.val i.isLt).symm,c,hc⟩
 · rfl

theorem Data.bad_transport (d e : Data) (he : d=e) (labels : List Bool) (values other : ℕ→ℝ)
    (hv : ∀i<d.birth,values i=other i) : d.bad labels values=e.bad labels other:=by
 subst e
 exact d.bad_values_congr labels values other hv

end LeanCanny.Algebra.IntegralMixedPrefixSnapshot
