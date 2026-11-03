/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedChronologicalMeanCut
/-! # Parameter zero in the actual mean-cut ABI is the ordinary numerical mean

The comparison is between specialized polynomials and their root multisets.
It does not transport complete sample words or ordinal encodings.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedChronologicalMeanCut
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedCriticalSweep
open IntegralMixedFrozenFrame IntegralMixedCausalRowConstructor IntegralMixedNumericalSweep Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n birth : ℕ}

noncomputable def mean (values : Fin birth→ℝ) (a b : Fin birth):=
  (values (IntegralMixedChronologicalMidpoint.reference a)+values (IntegralMixedChronologicalMidpoint.reference b))/2

section Numerical
variable (d : IntegralMixedChronologicalFrame.Descriptor n birth) (hk : d.labels.length<n+1)
    (a b : Fin birth) (g j : Fin (n+1))
    (hg : g∉(IntegralMixedChronologicalMidpoint.frame d hk a b).frozen)
    (hj : j∉(IntegralMixedChronologicalMidpoint.frame d hk a b).frozen)
    (Q : ℤ) (hQ : Q≠0)
local notation "r0"=>IntegralMixedCutRecordConstructor.Data.rule (IntegralMixedChronologicalSweepFrame.data d hk g j hg hj) Q hQ
local notation "rm"=>IntegralMixedCutRecordConstructor.Data.rule (data d hk a b g j hg hj) Q hQ

theorem ordinary_height_zero (values : Fin birth→ℝ) :
    ((r0).critical.heights (r0).height).evaluate values=0:=by
  change ((d.atom (FrozenCoordinateOrdering.permutation (IntegralMixedChronologicalSweepFrame.frame d hk).frozen
    (IntegralMixedChronologicalMidpoint.next d hk))).value).evaluate values=0
  rw [(IntegralMixedChronologicalSweepFrame.prefix_frozen d hk).permutation]
  simp only [Equiv.refl_apply,IntegralMixedChronologicalFrame.Descriptor.atom,
    IntegralMixedChronologicalMidpoint.next,Fin.val_mk,Nat.lt_irrefl,dite_false,Atom.value,AffineExpr.evaluate]
  norm_num

theorem normalized_zero (values : Fin birth→ℝ) (i : Fin (n+1)) :
    (normalized rm values i.val).eval 0=(normalized r0 values i.val).eval (mean values a b):=by
  rw [data_rule]
  exact (IntegralMixedMeanCenteredSweep.normalized_at_mean r0
    (IntegralMixedChronologicalMidpoint.reference a) (IntegralMixedChronologicalMidpoint.reference b) values
    (ordinary_height_zero d hk a b g j hg hj Q hQ values) rfl i).symm

theorem normalized_frozen_zero (values : Fin birth→ℝ) :
    ∀i,i<(r0).critical.offset.val→
      (normalized r0 values i).eval (mean values a b)=(normalized rm values i).eval 0:=by
  intro i hi
  exact (normalized_zero d hk a b g j hg hj Q hQ values ⟨i,hi.trans (r0).critical.offset.isLt⟩).symm

theorem coordinateAt_zero (P : SpatialSource n) (values : Fin birth→ℝ)
    (i : Fin (n-(r0).critical.offset.val+1)) :
    coordinateAt P rm values 0 (indexCast r0 rm rfl i)=coordinateAt P r0 values (mean values a b) i:=
  (coordinateAt_congr P r0 rm rfl rfl values values (mean values a b) 0
    (normalized_frozen_zero d hk a b g j hg hj Q hQ values) i).symm
end Numerical

section Actual
variable {S B : ℕ} {P : SpatialSource n} {ι : Type}
variable (x : State P S B birth ι) (hm : birth≤S)
    (d : IntegralMixedChronologicalFrame.Descriptor n birth) (hk : d.labels.length<n+1)
    (a b : Fin birth) (g j : Fin (n+1))
    (hg : g∉(IntegralMixedChronologicalMidpoint.frame d hk a b).frozen)
    (hj : j∉(IntegralMixedChronologicalMidpoint.frame d hk a b).frozen)
local notation "r0"=>IntegralMixedCutRecordConstructor.Data.rule (IntegralMixedChronologicalSweepFrame.data d hk g j hg hj) (commonDenominator x) (commonDenominator_ne_zero x)
local notation "rm"=>IntegralMixedCutRecordConstructor.Data.rule (data d hk a b g j hg hj) (commonDenominator x) (commonDenominator_ne_zero x)

theorem selected_zero_scaling (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (values : Fin birth→ℝ) (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (i : Fin (n-(r0).critical.offset.val+1)) :
    (selected x hm rm (indexCast r0 rm rfl i) φ).map (evalRingHom 0)=
      C (coordinateScale x hm rm/coordinateScale x hm r0)*
        (selected x hm r0 i φ).map (evalRingHom (mean values a b)):=
  specialized_selected_scaling x hm x hm r0 rm rfl rfl rfl rfl φ φ values values H H
    (mean values a b) 0
    (normalized_frozen_zero d hk a b g j hg hj _ _ values) i

theorem selected_zero_roots (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (values : Fin birth→ℝ) (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (i : Fin (n-(r0).critical.offset.val+1)) :
    ((selected x hm rm (indexCast r0 rm rfl i) φ).map (evalRingHom 0)).roots=
      ((selected x hm r0 i φ).map (evalRingHom (mean values a b))).roots:=
  specialized_selected_roots x hm x hm r0 rm rfl rfl rfl rfl φ φ values values H H
    (mean values a b) 0
    (normalized_frozen_zero d hk a b g j hg hj _ _ values) i

theorem selected_zero_degree (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (values : Fin birth→ℝ) (H : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (i : Fin (n-(r0).critical.offset.val+1)) :
    ((selected x hm rm (indexCast r0 rm rfl i) φ).map (evalRingHom 0)).natDegree=
      ((selected x hm r0 i φ).map (evalRingHom (mean values a b))).natDegree:=by
  rw [selected_zero_scaling x hm d hk a b g j hg hj φ values H i]
  exact Polynomial.natDegree_C_mul (div_ne_zero (coordinateScale_ne_zero x hm rm) (coordinateScale_ne_zero x hm r0))
end Actual

end LeanCanny.Geometry.IntegralMixedChronologicalMeanCut
