/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedMarkedPreludeCongruence
/-! # Actual marked replay geometry is fixed by candidate and record count

Resource height and modulus bounds may change with unused original bytes.
The state horizon, scalar width, spatial arity and degree are equal.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedMarkedPrefixParameters
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR
open IntegralMixedAuxiliaryMarkedIntegerSource (candidate original number)
open IntegralMixedOriginalRegularSource (radius radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound
  IntegralMixedAuxiliaryMarkedIntegerPlan.degree IntegralMixedExceptionalBounds.auxiliaryCap
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R0 : List Bool→ℕ} (hR0 : BinaryFn R0) (cL cR : List Bool)
  (hc : candidate cL=candidate cR)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)

include hc in
theorem ambient : (P).ambient cL=(P).ambient cR :=by
  change number n cL+3=number n cR+3
  rw [IntegralMixedMarkedPreludeCongruence.number_eq cL cR hc]
include hc in
theorem degree : (P).degree cL=(P).degree cR :=by
  change IntegralMixedAuxiliaryMarkedIntegerPlan.degree t cL=IntegralMixedAuxiliaryMarkedIntegerPlan.degree t cR
  unfold IntegralMixedAuxiliaryMarkedIntegerPlan.degree
  rw [IntegralMixedMarkedPreludeCongruence.original_eq cL cR hc]
include hc in
theorem sourceWidth : (P).sourceWidth cL=(P).sourceWidth cR :=
  congrArg Nat.size (degree hn ht ha hR0 cL cR hc)
include hc in
theorem width : (P).width cL=(P).width cR :=by
  change (IntegralMixedExceptionalBounds.auxiliaryCap (number n cL+3+1)
      (IntegralMixedAuxiliaryMarkedIntegerPlan.degree t cL)+IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound hn ht ha cL).size=
    (IntegralMixedExceptionalBounds.auxiliaryCap (number n cR+3+1)
      (IntegralMixedAuxiliaryMarkedIntegerPlan.degree t cR)+IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound hn ht ha cR).size
  have HD : IntegralMixedAuxiliaryMarkedIntegerPlan.degree t cL=IntegralMixedAuxiliaryMarkedIntegerPlan.degree t cR:=
    degree hn ht ha hR0 cL cR hc
  rw [IntegralMixedMarkedPreludeCongruence.number_eq cL cR hc,HD,
    IntegralMixedMarkedPreludeCongruence.degree_bound hn ht ha cL cR hc]
include hc in
theorem cap (hcount : IntegralMixedCausalRecordPlanBits.count cL=IntegralMixedCausalRecordPlanBits.count cR) :
    (P).cap cL=(P).cap cR :=by
  change number n cL+8+IntegralMixedCausalRecordPlanBits.count cL+2=
    number n cR+8+IntegralMixedCausalRecordPlanBits.count cR+2
  rw [IntegralMixedMarkedPreludeCongruence.number_eq cL cR hc,hcount]
end LeanCanny.Encoding.IntegralMixedMarkedPrefixParameters
