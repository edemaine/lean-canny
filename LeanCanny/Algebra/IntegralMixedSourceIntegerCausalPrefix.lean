/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedSourceIntegerCausalAppend
/-! # Causal continuation retains the literal target-width integer prefix

The continuation may be arbitrary. This statement concerns the instructions
already interpreted at the prelude birth, not solvability of later records.
All prefixes use the same parameters, including the target cap and width.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedSourceIntegerPrelude
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedCausalRecordBits
open IntegralMixedFramedHistoryFamilyBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (P : Parameters) (Q : ∀root,SpatialSource (P.ambient root))
  (hdegree : ∀root,(Q root).degree=P.degree root)
  (hcap : ∀root,IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient root+1) (P.degree root)≤2^P.width root)
  (S : IntegerPolynomialRootQueriesBits.Source) (N : List Bool→ℕ) (hz : ∀q,S.polynomial q≠0)
  (hd : ∀root i,S.degree (pair root (BinaryNatCode.encode i))≤2^P.width root)
  (later : ∀root,List (Record (P.ambient root) (P.width root)))
  (hroom : ∀root,(later root).length+N root+2≤P.cap root+1)
local notation "D"=>extendedPlan P Q hdegree hcap S N hz hd later hroom
local notation "I"=>plan P Q hdegree hcap S N hz hd (prelude_room P N later hroom)

theorem extended_past (root : List Bool) :
    past ((D).rules root) (N root)=(I).rules root :=by
  rw [past,List.reverse_take,List.length_reverse,List.reverse_reverse,
    extended_length,show (later root).length+N root-N root=(later root).length by omega]
  exact extended_suffix P Q hdegree hcap S N hz hd later hroom root

theorem extended_paddedPast (root : List Bool) :
    paddedPast (defaultInstruction P D root) ((D).rules root) (N root)=(I).rules root :=by
  rw [paddedPast_valid _ _ _ (by rw [extended_length]; omega)]
  exact extended_past P Q hdegree hcap S N hz hd later hroom root

theorem extended_commands_at (key : List Bool) (hb : prefixLength P key=N (pairFst key)) :
    IntegralMixedFramedHistoryFamilyBits.commands P D key=(I).rules (pairFst key) :=by
  change paddedPast _ _ (prefixLength P key)=_
  rw [hb]
  exact extended_paddedPast P Q hdegree hcap S N hz hd later hroom _

theorem extended_commands_key (root tail : List Bool) :
    IntegralMixedFramedHistoryFamilyBits.commands P D (keyAt root (N root) tail)=
      (I).rules (pairFst (keyAt root (N root) tail)) :=by
  apply extended_commands_at
  rw [keyAt_root,keyAt_prefix P root (N root) tail (by have H:=hroom root; omega)]

/-- The initial quotient algebra is also literal; no legacy width or cap
transport is needed. The eventual selected source may still differ. -/
theorem extended_initial (root : List Bool) :
    initial P D root=initial P I root :=rfl

end LeanCanny.Algebra.IntegralMixedSourceIntegerPrelude
