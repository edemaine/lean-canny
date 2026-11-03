/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPrefixSnapshotRetarget
public import LeanCanny.Encoding.IntegralMixedChronologicalCutRetarget
/-! # An actual ordinary raw rule has exactly the packed parent bad set -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPrefixSnapshot
open LeanCanny.Encoding IntegralMixedHistory IntegralMixedRelativeCuts
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

theorem ofState_mem_bad_iff (x : State P S B m ι) (hm : m≤S) (hx : Canonical x)
    (labels : List Bool) (j : ℕ)
    (h : IntegralMixedChronologicalCutCode.Good n m labels (WordListRecords.count labels+1) j)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (values : ℕ→ℝ)
    (hφ : ∀i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i.val) (a : ℝ) :
    a∈(ofState x).bad labels values ↔
      ∃k : Kind P ((IntegralMixedChronologicalCutCode.rawData n m labels (WordListRecords.count labels+1) j h).rule
        (commonDenominator x) (commonDenominator_ne_zero x)),
      Valid x hm ((IntegralMixedChronologicalCutCode.rawData n m labels (WordListRecords.count labels+1) j h).rule
        (commonDenominator x) (commonDenominator_ne_zero x)) φ k ∧
      IntegralMixedSelectedBadMembership.Ordinary
        ((IntegralMixedChronologicalCutCode.rawData n m labels (WordListRecords.count labels+1) j h).rule
          (commonDenominator x) (commonDenominator_ne_zero x)) k ∧
      (factor x hm ((IntegralMixedChronologicalCutCode.rawData n m labels (WordListRecords.count labels+1) j h).rule
        (commonDenominator x) (commonDenominator_ne_zero x)) k).eval₂ φ.toRingHom a=0:=by
 have HR :(ofState x).Ready labels:=⟨hm,h.1,h.2.2.1⟩
 have HT:=IntegralMixedChronologicalCutCode.raw_rule_retarget x labels (WordListRecords.count labels+1) j h
 have HB :(ofState x).rule labels HR=
     (IntegralMixedChronologicalCutCode.rawData n m labels (WordListRecords.count labels+1)
       (WordListRecords.count labels+1) (IntegralMixedChronologicalCutCode.raw_base_good _ _ _ _ _ h)).rule
       (commonDenominator x) (commonDenominator_ne_zero x):=rfl
 have H0:=(ofState x).mem_bad_retarget_factor_iff labels values HR hx φ hφ
   (j-(WordListRecords.count labels+1)) a
 rw [HB,←HT] at H0
 exact H0

end LeanCanny.Algebra.IntegralMixedPrefixSnapshot
