/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedSourceIntegerRules
public import LeanCanny.Algebra.IntegralMixedFramedZeroRules
/-! # Actual integer-prelude zero/unit rules, including malformed saved words -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedSourceIntegerPrelude
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask IntegralMixedHistory
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (P : Parameters) (Q : ∀root,SpatialSource (P.ambient root))
  (hdegree : ∀root,(Q root).degree=P.degree root)
  (hcap : ∀root,IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
  (S : IntegerPolynomialRootQueriesBits.Source) (count : List Bool → ℕ)
  (hz : ∀q,S.polynomial q≠0) (hd : ∀root i,S.degree (pair root (BinaryNatCode.encode i))≤2^P.width root)
  (hroom : ∀root,count root+2≤P.cap root+1)
  (hn : ∀root,0<P.ambient root) (hSW : ∀root,(P.degree root).size≤P.sourceWidth root)

local notation "D" => plan P Q hdegree hcap S count hz hd hroom
local notation "J" => data P Q hdegree hcap S count hz hd hroom hn hSW

theorem zeroRules : IntegralMixedFramedZeroRulesBits.Rules P D J where
  physical key:=by
    rw [physical_rule]
    exact ⟨fun _=>rfl,fun _=>rfl⟩
  virtual key:=by
    rw [virtual_rule]
    refine ⟨⟨?_,fun _=>rfl⟩,?_,rfl⟩
    · intro i
      simp [IntegralMixedCanonicalUnitRuleBits.virtual,IntegralMixedUnitRecordCode.field,
        IntegralMixedUnitRowCode.expression,IntegralMixedUnitRowCode.active,WordList.get,pairFst]
    · simp [IntegralMixedCanonicalUnitRuleBits.virtual,IntegralMixedUnitRecordCode.height,
        IntegralMixedUnitRecordCode.virtualOffset,IntegralMixedUnitRecordCode.field,WordList.get,pairFst]
      simp only [show Nat.fromBitsLE ([] : List Bool)=0 from rfl,Nat.zero_mod]

end LeanCanny.Algebra.IntegralMixedSourceIntegerPrelude
