/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapProperAppendPadding
public import LeanCanny.Encoding.IntegralMixedMarkedSeedTailRetained
/-! # A fresh own-context word retains the fixed constructed proper-level tuple -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR
open IntegralCriticalHistoryTask IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedHistoryFamilyBits (initial)
open IntegralMixedOriginalRegularSource (radius radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
open IntegralMixedFramedPhysicalIndex (arity)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "B"=>IntegralMixedMarkedReservedParent.bank hn ht ha hR0
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false
local notation "Q" root=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) root
theorem proper_input_eq :IntegralMixedMarkedReservedParent.input hn ht ha hR0=S:=by
  unfold IntegralMixedMarkedReservedParent.input IntegralMixedMarkedReservedParent.bank
    IntegralMixedPhysicalMarkedTest.input IntegralMixedPhysicalMarkedPlan.bank
  rfl

theorem proper_valid_to_parent (ctx w :List Bool) (hw :SquareSampleCompleteVertices.Valid S ctx w):
    SquareSampleCompleteVertices.Valid (IntegralMixedMarkedReservedParent.input hn ht ha hR0) ctx w:=
  Eq.mp (congrArg (fun I=>SquareSampleCompleteVertices.Valid I ctx w)
    (proper_input_eq hn ht ha hR0).symm) hw

private theorem sample_full (root :List Bool) (u :ℕ→ℝ)
    (hu :(IntegralMixedMarkedPrefixFieldReadback.fullObservation hn ht ha hR0 root).Roots u):
    IntegralMixedMarkedSeedTailRetained.Sampled hn ht ha hR0 root u:=by
  have HE :IntegralMixedMarkedSeedTailRetained.fullObservation hn ht ha hR0 root=
      IntegralMixedMarkedPrefixFieldReadback.fullObservation hn ht ha hR0 root:=by
    unfold IntegralMixedMarkedSeedTailRetained.fullObservation
      IntegralMixedMarkedPrefixFieldReadback.fullObservation IntegralMixedMarkedReservedParent.bank
    rfl
  have HC:=IntegralMixedMarkedReservedParent.full_prefix hn ht ha hR0 root
  rw [←IntegralMixedMarkedPrefixFieldReadback.rules_length hn ht ha hR0] at HC
  apply IntegralMixedMarkedSeedTailRetained.sample_observation hn ht ha hR0 root u
  · exact Eq.mpr (congrArg (fun O :IntegralMixedFramedRunObservation.Data=>O.Roots u) HE) hu
  · have HR :((B).plan.rules root).length=
        ((IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha (radius_binary hR0)).rules root).length:=by
      unfold IntegralMixedMarkedReservedParent.bank
      rfl
    exact HC.trans HR.symm

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedExceptionalBounds.auxiliaryCap preparedRoot compiledProgram
  compiledObservation canonicalObservation IntegralMixedMarkedPrefixFieldReadback.fullObservation
  seedTailCount IntegralMixedRoadmapAtomic.payload

structure ProperWordData (root :List Bool)
    (canonical actual :IntegralMixedFramedRunObservation.Data)
    (commands :List (Instruction ((P).ambient root) ((P).width root))) (paddingCount :ℕ)
    (localTuple :ℕ→ℝ) (p0 :Fin ((P).ambient root+1)→ℝ) where
  tuple :ℕ→ℝ
  word :List Bool
  valid :SquareSampleCompleteVertices.Valid S (pair root []) word
  word_length :word.length=SquareSampleCompleteVertices.width S (pair root [])
  joint :∀i :Fin (IntegralFramedPhysicalSquare.count (B).parameters (B).plan ((B).key (pair root []))),
    IntegralFramedPhysicalSquare.joint (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed
      (B).bounds (B).key (B).positive (pair root []) word (proper_valid_to_parent hn ht ha hR0 _ _ valid) i=tuple i.val
  canonical_roots :canonical.Roots localTuple
  local_roots :actual.Roots localTuple
  roots :(IntegralMixedMarkedPrefixFieldReadback.fullObservation hn ht ha hR0 root).Roots tuple
  preserved :∀i,i<canonical.arity→tuple i=localTuple i
  padding_blocks :∀j :Fin (IntegralMixedCanonicalPadding.paddingSelections ((P).ambient root) paddingCount).length,∀i,
    tuple (arity commands+(2*(P).ambient root+4)*((IntegralMixedCanonicalPadding.paddingSelections ((P).ambient root) paddingCount).length-1-j.val)+i.val)^
      UniformIntegralPowerSchedule.physical ((P).cap root+1) (2^(P).width root)
        ((commands).length+((IntegralMixedCanonicalPadding.paddingSelections ((P).ambient root) paddingCount).length-1-j.val))=p0 i
  values :∀i :Fin ((commands).length+(IntegralMixedCanonicalPadding.paddingSelections ((P).ambient root) paddingCount).length),
    (IntegralMixedMarkedPrefixFieldReadback.fullObservation hn ht ha hR0 root).point tuple i.val=
      IntegralMixedPointCompanion.values p0 (fun j=>canonical.point localTuple j.val)
        (IntegralMixedCanonicalPadding.paddingSelections ((P).ambient root) paddingCount) i

variable (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
  (hd :IntegralMixedRoadmapAtomic.depth old<IntegralMixedRoadmapAtomic.dimension hn ht ha hR0 old)
  (left right :ParentEndpoint hn ht ha hR0 old hv hd)
  (R :CanonicalPair hn ht ha hR0 old hv hd left right) (side :Bool)
local notation "r"=>preparedRoot hn ht ha hR0 old R.leftSpec R.rightSpec side
local notation "localCs"=>compiledProgram hn ht ha hR0 old hv hd left right R side
local notation "tailCount"=>seedTailCount hn ht ha hR0 old hv hd left right R side
local notation "CTX"=>pair r []

noncomputable abbrev WordReceipt (localTuple :ℕ→ℝ) (p0 :Fin ((P).ambient r+1)→ℝ):=
  ProperWordData hn ht ha hR0 r
    (canonicalObservation hn ht ha hR0 old hv hd left right R side)
    (compiledObservation hn ht ha hR0 old hv hd left right R side) localCs tailCount localTuple p0

theorem WordReceipt.column {z :ℕ→ℝ} {p0 :Fin ((P).ambient r+1)→ℝ}
    (W :WordReceipt hn ht ha hR0 old hv hd left right R side z p0) (i :Fin (canonicalObservation hn ht ha hR0 old hv hd left right R side).arity):
    W.tuple i.val=z i.val:=W.preserved i.val i.isLt

theorem WordReceipt.powered_column {z :ℕ→ℝ} {p0 :Fin ((P).ambient r+1)→ℝ}
    (W :WordReceipt hn ht ha hR0 old hv hd left right R side z p0)
    (i :Fin (canonicalObservation hn ht ha hR0 old hv hd left right R side).arity)
    (power :ℕ) (value :ℝ) (hi :z i.val^power=value):W.tuple i.val^power=value:=by
  rw [W.column hn ht ha hR0 old hv hd left right R side i]
  exact hi

theorem exists_word_receipt (z :ℕ→ℝ)
    (hz :(canonicalObservation hn ht ha hR0 old hv hd left right R side).Roots z)
    (p0 :Fin ((P).ambient r+1)→ℝ)
    (hp0 :(FermatCriticalHomogenization.polynomial (Q r).low (Q r).leading (Q r).degree).eval₂
      (Int.castRingHom ℝ) p0=0)
    (hg0 :∀i,i≠0→(MvPolynomial.pderiv i
      (FermatCriticalHomogenization.polynomial (Q r).low (Q r).leading (Q r).degree)).eval₂
        (Int.castRingHom ℝ) p0=0):
    Nonempty (WordReceipt hn ht ha hR0 old hv hd left right R side z p0):=by
  obtain ⟨u,HU,HK,HP,HF⟩:=pad_local_tuple hn ht ha hR0 old hv hd left right R side z hz p0 hp0 hg0
  obtain ⟨w,hw,hlen,HJ⟩:=sample_full hn ht ha hR0 r u HU
  have hwS :SquareSampleCompleteVertices.Valid S CTX w:=Eq.mp
    (congrArg (fun I=>SquareSampleCompleteVertices.Valid I CTX w) (proper_input_eq hn ht ha hR0)) hw
  have HK' :∀i,i<(canonicalObservation hn ht ha hR0 old hv hd left right R side).arity→u i=z i:=by
    intro i hi
    apply HK i
    have H:=tuple_arity hn ht ha hR0 old hv hd left right R side
    have H' :arity localCs=(canonicalObservation hn ht ha hR0 old hv hd left right R side).arity:=by
      simpa only [compiledObservation,IntegralMixedFramedRunObservation.ofCommands] using H
    exact hi.trans_eq H'.symm
  refine ⟨⟨u,w,hwS,?_,HJ,hz,tuple_roots hn ht ha hR0 old hv hd left right R side z hz,HU,HK',HP,HF⟩⟩
  simpa only [proper_input_eq hn ht ha hR0,IntegralMixedMarkedReservedParent.context] using hlen

end LeanCanny.Encoding.IntegralMixedRoadmapProperAppend
