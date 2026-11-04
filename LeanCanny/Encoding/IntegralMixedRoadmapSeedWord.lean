/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedRoadmapSeedRealization
public import LeanCanny.Encoding.IntegralMixedMarkedSeedTailRetained
/-! # Fresh complete words preserve the prescribed full seed tuple -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedRoadmapSeedResampling
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFramedPhysicalIndex
open IntegralMixedFramedHistoryFamilyBits (initial defaultInstruction)
open IntegralMixedOriginalRegularSource (radius radius_binary)
open IntegralMixedFramedRunObservation (ofCommands)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "P"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0)
local notation "D"=>IntegralMixedAuxiliaryMarkedRecordPlan.certifiedPlan hn ht ha (radius_binary hR0)
local notation "B"=>IntegralMixedMarkedReservedParent.bank hn ht ha hR0
local notation "Q" root=>IntegralMixedAuxiliaryMarkedIntegerPlan.spatial n t (radius R0) root
attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank IntegralMixedMarkedReservedParent.bank
  IntegralMixedExceptionalBounds.auxiliaryCap
  preparedRoot seedOlder seedSelections seedTail seedState seedPoint seedObservation
  IntegralMixedMarkedRecordContinuation.oldCommands

private theorem retained_observation_eq (root :List Bool) :
    IntegralMixedMarkedSeedTailRetained.fullObservation hn ht ha hR0 root=
      IntegralMixedMarkedPrefixFieldReadback.fullObservation hn ht ha hR0 root:=by
  unfold IntegralMixedMarkedSeedTailRetained.fullObservation
    IntegralMixedMarkedPrefixFieldReadback.fullObservation IntegralMixedMarkedReservedParent.bank
  rfl

private theorem parent_rules_eq (root :List Bool) :((B).plan.rules root).length=((D).rules root).length:=by
  unfold IntegralMixedMarkedReservedParent.bank
  rfl

private theorem sample_full (root :List Bool) (u :ℕ→ℝ)
    (hu :(IntegralMixedMarkedPrefixFieldReadback.fullObservation hn ht ha hR0 root).Roots u) :
    IntegralMixedMarkedSeedTailRetained.Sampled hn ht ha hR0 root u:=by
  have HC:=IntegralMixedMarkedReservedParent.full_prefix hn ht ha hR0 root
  rw [←IntegralMixedMarkedPrefixFieldReadback.rules_length hn ht ha hR0] at HC
  apply IntegralMixedMarkedSeedTailRetained.sample_observation hn ht ha hR0 root u
  · exact Eq.mpr (congrArg (fun O:IntegralMixedFramedRunObservation.Data=>O.Roots u)
      (retained_observation_eq hn ht ha hR0 root)) hu
  · exact HC.trans (parent_rules_eq hn ht ha hR0 root).symm

private theorem seed_observation_eq (old :List Bool) :seedObservation hn ht ha hR0 old=
    IntegralMixedMarkedPrefixFieldReadback.fullObservation hn ht ha hR0 (preparedRoot hn ht ha hR0 old):=by
  unfold seedObservation IntegralMixedMarkedPrefixFieldReadback.fullObservation
  rfl

theorem sample_seed (old :List Bool) (u :ℕ→ℝ) (hu :(seedObservation hn ht ha hR0 old).Roots u) :
    IntegralMixedMarkedSeedTailRetained.Sampled hn ht ha hR0 (preparedRoot hn ht ha hR0 old) u:=by
  exact sample_full hn ht ha hR0 _ u
    (Eq.mp (congrArg (fun O:IntegralMixedFramedRunObservation.Data=>O.Roots u)
      (seed_observation_eq hn ht ha hR0 old)) hu)

theorem seed_input_eq :IntegralMixedMarkedReservedParent.input hn ht ha hR0=
    IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false:=by
  unfold IntegralMixedPhysicalMarkedTest.input IntegralMixedPhysicalMarkedPlan.bank
    IntegralMixedMarkedReservedParent.input IntegralMixedMarkedReservedParent.bank
  rfl

theorem seed_valid_to_parent (c w :List Bool)
    (hw :SquareSampleCompleteVertices.Valid
      (IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false) c w) :
    SquareSampleCompleteVertices.Valid (IntegralMixedMarkedReservedParent.input hn ht ha hR0) c w:=by
  exact Eq.mp (congrArg (fun I=>SquareSampleCompleteVertices.Valid I c w)
    (seed_input_eq hn ht ha hR0).symm) hw

noncomputable def WordReceipt (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (p :Fin ((P).ambient (preparedRoot hn ht ha hR0 old)+1)→ℝ) :Prop:=
  ∃u :ℕ→ℝ,∃w,∃hw :SquareSampleCompleteVertices.Valid
      (IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false)
      (pair (preparedRoot hn ht ha hR0 old) []) w,
    w.length=SquareSampleCompleteVertices.width
      (IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false)
      (pair (preparedRoot hn ht ha hR0 old) []) ∧
    (∀i :Fin (IntegralFramedPhysicalSquare.count (B).parameters (B).plan
        ((B).key (pair (preparedRoot hn ht ha hR0 old) []))),
      IntegralFramedPhysicalSquare.joint (B).parameters (B).plan (B).data (B).nodes (B).factor (B).seed
        (B).bounds (B).key (B).positive (pair (preparedRoot hn ht ha hR0 old) []) w
          (seed_valid_to_parent hn ht ha hR0 _ _ hw) i=u i.val) ∧
    (seedObservation hn ht ha hR0 old).Roots u ∧
    (∀i :Index (Fin 0) (seedOlder hn ht ha hR0 old),
      u (enumerate (seedOlder hn ht ha hR0 old) i).val=
        oldTuple hn ht ha hR0 old hv (enumerate (seedOlder hn ht ha hR0 old) i).val) ∧
    (∀k :Fin (seedSelections hn ht ha hR0 old).length,∀i,
      u (arity (seedOlder hn ht ha hR0 old)+(2*(P).ambient (preparedRoot hn ht ha hR0 old)+4)*
        ((seedSelections hn ht ha hR0 old).length-1-k.val)+i.val)^
        UniformIntegralPowerSchedule.physical ((P).cap (preparedRoot hn ht ha hR0 old)+1)
          (2^(P).width (preparedRoot hn ht ha hR0 old))
          ((seedOlder hn ht ha hR0 old).length+((seedSelections hn ht ha hR0 old).length-1-k.val))=p i) ∧
    ∀i :Fin ((seedOlder hn ht ha hR0 old).length+(seedSelections hn ht ha hR0 old).length),
      (seedObservation hn ht ha hR0 old).point u i.val=
        IntegralMixedPointCompanion.values p (seedPoint hn ht ha hR0 old hv)
          (seedSelections hn ht ha hR0 old) i

theorem exists_seed_word (old :List Bool) (hv :IntegralMixedRoadmapAtomic.Valid hn ht ha hR0 old)
    (p :Fin ((P).ambient (preparedRoot hn ht ha hR0 old)+1)→ℝ)
    (hp :(FermatCriticalHomogenization.polynomial (Q (preparedRoot hn ht ha hR0 old)).low
      (Q (preparedRoot hn ht ha hR0 old)).leading (Q (preparedRoot hn ht ha hR0 old)).degree).eval₂
        (Int.castRingHom ℝ) p=0)
    (hg :∀i,i.val≠0→(MvPolynomial.pderiv i
      (FermatCriticalHomogenization.polynomial (Q (preparedRoot hn ht ha hR0 old)).low
        (Q (preparedRoot hn ht ha hR0 old)).leading (Q (preparedRoot hn ht ha hR0 old)).degree)).eval₂
          (Int.castRingHom ℝ) p=0) :WordReceipt hn ht ha hR0 old hv p:=by
  obtain ⟨u,hu,hold,hblocks,hpoint⟩:=exists_seed_tuple hn ht ha hR0 old hv p hp hg
  obtain ⟨w,hw,hlen,hjoint⟩:=sample_seed hn ht ha hR0 old u hu
  have hwS :SquareSampleCompleteVertices.Valid
      (IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false)
      (pair (preparedRoot hn ht ha hR0 old) []) w:=
    Eq.mp (congrArg (fun I=>SquareSampleCompleteVertices.Valid I
      (pair (preparedRoot hn ht ha hR0 old) []) w) (seed_input_eq hn ht ha hR0)) hw
  refine ⟨u,w,hwS,?_,?_,hu,hold,hblocks,hpoint⟩
  · simpa only [seed_input_eq hn ht ha hR0,IntegralMixedMarkedReservedParent.context] using hlen
  · exact hjoint

end LeanCanny.Encoding.IntegralMixedRoadmapSeedResampling
