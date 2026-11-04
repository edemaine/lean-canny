/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPrefixSnapshot
public import LeanCanny.Algebra.IntegralMixedRelativeCutFiniteGuards
/-! # Exact cut receipts transport with the creating prefix and old values

The receipt retains coefficient-choice guards, the stored specialized degree
and the actual untruncated factor root. Full-row roots alone are insufficient.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPrefixSnapshot
open IntegralMixedHistory IntegralMixedFullHistoryScript IntegralMixedRelativeCuts
open scoped Classical

theorem hom_eq_of_quotients {n S B m :ℕ} {P :SpatialSource n} {ι :Type}
    (x :State P S B m ι) (hx :Canonical x)
    (φ ψ :x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (h :∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=
      ψ (x.bank.numerator i)/(x.bank.denominator i:ℝ)) :φ=ψ:=by
  apply x.sampler.scalarPrefix.basis.algHom_ext
  intro i
  rw [←hx i]
  exact (div_left_inj' (Int.cast_ne_zero.mpr (x.denominator_ne_zero i))).mp (h i)

noncomputable def Data.CutReceipt (d :Data) (hm :d.birth≤d.horizon)
    (cmd :Command d.source d.width) (values :ℕ→ℝ) (a :ℝ) :Prop:=
  match cmd with
  | .cut r kind degree _ _=>
    ∃φ :d.state.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      (∀i,φ (d.state.bank.numerator i)/(d.state.bank.denominator i:ℝ)=values i.val) ∧
      CoefficientGuards d.state hm r φ kind degree ∧
      (factor d.state hm r kind).eval₂ φ.toRingHom a=0
  | _=>True

theorem Data.cutReceipt_values_congr (d :Data) (hm :d.birth≤d.horizon)
    (cmd :Command d.source d.width) (values other :ℕ→ℝ) (a :ℝ)
    (he :∀i<d.birth,values i=other i) :
    d.CutReceipt hm cmd values a↔d.CutReceipt hm cmd other a:=by
  cases cmd with
  | integer =>rfl
  | critical =>rfl
  | cut r kind degree hs hd=>
    constructor
    · rintro ⟨φ,hφ,hc,hr⟩
      exact ⟨φ,fun i=>(hφ i).trans (he i.val i.isLt),hc,hr⟩
    · rintro ⟨φ,hφ,hc,hr⟩
      exact ⟨φ,fun i=>(hφ i).trans (he i.val i.isLt).symm,hc,hr⟩

/-- Equality is of the full coefficient-algebra snapshot and actual command;
there is no replacement of the selected interpretation by unrelated roots. -/
theorem Data.cutReceipt_transport (d e :Data) (hm :d.birth≤d.horizon)
    (hn :e.birth≤e.horizon) (cmd :Command d.source d.width) (cmd' :Command e.source e.width)
    (hd :d=e) (hc :HEq cmd cmd') (values other :ℕ→ℝ) (a :ℝ)
    (he :∀i<d.birth,values i=other i) :
    d.CutReceipt hm cmd values a↔e.CutReceipt hn cmd' other a:=by
  subst e
  cases eq_of_heq hc
  exact d.cutReceipt_values_congr hm cmd values other a he

theorem Data.cutReceipt_iff_at (d :Data) (hm :d.birth≤d.horizon) (hx :Canonical d.state)
    (r :IntegralMixedCriticalSweep.Rule d.ambient) (kind :Kind d.source r)
    (degree :ℕ) (hs :degree≤IntegralMixedExceptionalBounds.auxiliaryCap (d.ambient+1) d.source.degree)
    (hd :degree≤2^d.width) (values :ℕ→ℝ) (a :ℝ)
    (φ :d.state.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (hφ :∀i,φ (d.state.bank.numerator i)/(d.state.bank.denominator i:ℝ)=values i.val) :
    d.CutReceipt hm (.cut r kind degree hs hd) values a↔
      CoefficientGuards d.state hm r φ kind degree ∧
        (factor d.state hm r kind).eval₂ φ.toRingHom a=0:=by
  constructor
  · rintro ⟨ψ,hψ,hc,hr⟩
    have H:ψ=φ:=hom_eq_of_quotients d.state hx ψ φ (fun i=>(hψ i).trans (hφ i).symm)
    simpa only [H] using And.intro hc hr
  · rintro ⟨hc,hr⟩
    exact ⟨φ,hφ,hc,hr⟩

end LeanCanny.Algebra.IntegralMixedPrefixSnapshot
