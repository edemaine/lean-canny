/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedMarkedSeedTailVertex
public import LeanCanny.Encoding.IntegralMixedSourceIntegerSeedTailObservation
public import LeanCanny.Encoding.IntegralFramedPhysicalExactVertex
/-! # Fresh actual marked words retain the prescribed old physical tuple

Only an honest full-root tuple at the meaningful prefix is supplied. The
tail and final record execute actual seed commands. The fresh complete word
reads the resulting entire physical tuple, not merely its bank quotients.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedMarkedSeedTailRetained
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryFamilyBits
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open IntegralMixedFramedRunObservation (ofCommands)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n :List Bool→ℕ} {t :List Bool→Term} (hn :UnaryFn n)
  (ht :(fun q=>(t q).toData.toBits)∈FP) (ha :∀q,(t q).arity≤n q)
  {R0 :List Bool→ℕ} (hR0 :BinaryFn R0)
local notation "B"=>IntegralMixedMarkedReservedParent.bank hn ht ha hR0
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "D"=>IntegralFramedBankQuery.Bank.plan B
local notation "V"=>IntegralMixedMarkedReservedCutView.plan hn ht ha hR0
local notation "Q"=>IntegralMixedMarkedReservedCutView.spatial hn ht ha hR0
attribute [local irreducible] IntegralMixedMarkedReservedParent.bank
  IntegralMixedExceptionalBounds.auxiliaryCap IntegralMixedSourceIntegerRecordAppend.plan

noncomputable def fullObservation (root :List Bool):=
  ofCommands (initial P D root) ((D).rules root) (by have HH:=(D).room root;omega)

noncomputable def beforeObservation (root :List Bool) (codes :List (List Bool)) (k :ℕ)
    (hcodes :IntegralMixedCausalRecordPlanBits.records root=WordList.encode
      (codes++List.replicate k (IntegralMixedChronologicalFrameCode.code ((P).ambient root) [] 0 0))):=
  IntegralFramedPhysicalPrefixObservation.atRoot P V root (number n root+8+codes.length)
    (IntegralMixedSourceIntegerSeedTail.before_bound P (fun root=>number n root+8)
      (IntegralMixedMarkedReservedCutView.room hn ht ha hR0) root codes k hcodes)

theorem exists_observation (root :List Bool) (codes :List (List Bool)) (k :ℕ)
    (hcodes :IntegralMixedCausalRecordPlanBits.records root=WordList.encode
      (codes++List.replicate k (IntegralMixedChronologicalFrameCode.code ((P).ambient root) [] 0 0)))
    (z :ℕ→ℝ) (hz :(beforeObservation hn ht ha hR0 root codes k hcodes).Roots z)
    (charge :ℕ) (hcharge :(Q root).degree=BoundedZeroSource.powerDegree charge)
    (p :Fin ((P).ambient root+1)→ℝ)
    (hp :(FermatCriticalHomogenization.polynomial (Q root).low (Q root).leading (Q root).degree).eval₂
      (Int.castRingHom ℝ) p=0)
    (hg :∀i,i≠0→(MvPolynomial.pderiv i
      (FermatCriticalHomogenization.polynomial (Q root).low (Q root).leading (Q root).degree)).eval₂
        (Int.castRingHom ℝ) p=0) :
    ∃y :ℕ→ℝ,(fullObservation hn ht ha hR0 root).Roots y ∧
      (∀i,i<(beforeObservation hn ht ha hR0 root codes k hcodes).arity→y i=z i) ∧
      ∀i,i<((D).rules root).length→(fullObservation hn ht ha hR0 root).point y i=
        IntegralMixedCanonicalPadding.values (p 0)
          ((beforeObservation hn ht ha hR0 root codes k hcodes).point z) k i :=by
  unfold beforeObservation at hz
  have HR:=IntegralMixedSourceIntegerSeedTail.full_observation P Q
    (IntegralMixedMarkedReservedCutView.positive hn ht ha hR0)
    (IntegralMixedMarkedReservedCutView.degree hn ht ha hR0)
    (IntegralMixedMarkedReservedCutView.scalar_cap hn ht ha hR0) (fun root=>number n root+8)
    (IntegralMixedMarkedReservedCutView.integerSource hn ht ha hR0)
    (IntegralMixedMarkedReservedCutView.integer_nonzero hn ht ha hR0)
    (IntegralMixedMarkedReservedCutView.integer_cap hn ht ha hR0)
    (IntegralMixedMarkedReservedCutView.room hn ht ha hR0)
    (IntegralMixedMarkedReservedCutView.data hn ht ha hR0) root [] codes k hcodes charge hcharge z hz p hp hg
  change ∃y :ℕ→ℝ,
    (ofCommands (initial P V root) ((V).rules root) (by have HH:=(V).room root;omega)).Roots y ∧
      (∀i,i<(beforeObservation hn ht ha hR0 root codes k hcodes).arity→y i=z i) ∧
      ∀i,i<((V).rules root).length→
        (ofCommands (initial P V root) ((V).rules root) (by have HH:=(V).room root;omega)).point y i=
          IntegralMixedCanonicalPadding.values (p 0)
            ((beforeObservation hn ht ha hR0 root codes k hcodes).point z) k i at HR
  simpa only [fullObservation,beforeObservation,IntegralMixedMarkedReservedCutView.plan_eq] using HR

attribute [local irreducible] fullObservation beforeObservation

noncomputable def Sampled (root :List Bool) (y :ℕ→ℝ) :Prop:=
  ∃w,∃hw :SquareSampleCompleteVertices.Valid (IntegralMixedMarkedReservedParent.input hn ht ha hR0)
    (IntegralMixedMarkedReservedParent.context root) w,
    w.length=SquareSampleCompleteVertices.width (IntegralMixedMarkedReservedParent.input hn ht ha hR0)
      (IntegralMixedMarkedReservedParent.context root) ∧
    ∀i :Fin (IntegralFramedPhysicalSquare.count P D ((B).key (IntegralMixedMarkedReservedParent.context root))),
      IntegralFramedPhysicalSquare.joint P D (B).data (B).nodes (B).factor (B).seed (B).bounds
        (B).key (B).positive (IntegralMixedMarkedReservedParent.context root) w hw i=y i.val

theorem sample_observation (root :List Bool) (y :ℕ→ℝ)
    (hy :(fullObservation hn ht ha hR0 root).Roots y)
    (hc :prefixLength P ((B).key (IntegralMixedMarkedReservedParent.context root))=((D).rules root).length) :
    Sampled hn ht ha hR0 root y:=by
  unfold fullObservation at hy
  exact IntegralFramedPhysicalSquare.exists_full_observation P D (B).data
    (B).nodes (B).factor (B).seed (B).bounds (B).key (B).positive
    (IntegralMixedMarkedReservedParent.context root) root
    (IntegralMixedMarkedReservedParent.key_root hn ht ha hR0 root) hc y hy

attribute [local irreducible] Sampled

theorem exists_vertex (root :List Bool) (codes :List (List Bool)) (k :ℕ)
    (hcodes :IntegralMixedCausalRecordPlanBits.records root=WordList.encode
      (codes++List.replicate k (IntegralMixedChronologicalFrameCode.code ((P).ambient root) [] 0 0)))
    (z :ℕ→ℝ) (hz :(beforeObservation hn ht ha hR0 root codes k hcodes).Roots z)
    (charge :ℕ) (hcharge :(Q root).degree=BoundedZeroSource.powerDegree charge)
    (p :Fin ((P).ambient root+1)→ℝ)
    (hp :(FermatCriticalHomogenization.polynomial (Q root).low (Q root).leading (Q root).degree).eval₂
      (Int.castRingHom ℝ) p=0)
    (hg :∀i,i≠0→(MvPolynomial.pderiv i
      (FermatCriticalHomogenization.polynomial (Q root).low (Q root).leading (Q root).degree)).eval₂
        (Int.castRingHom ℝ) p=0) :
    ∃y :ℕ→ℝ,Sampled hn ht ha hR0 root y ∧
      (fullObservation hn ht ha hR0 root).Roots y ∧
      (∀i,i<(beforeObservation hn ht ha hR0 root codes k hcodes).arity→y i=z i) ∧
      ∀i,i<((D).rules root).length→
        (fullObservation hn ht ha hR0 root).point y i=
          IntegralMixedCanonicalPadding.values (p 0)
            ((beforeObservation hn ht ha hR0 root codes k hcodes).point z) k i :=by
  obtain ⟨y,hy,hold,hpoint⟩:=exists_observation hn ht ha hR0 root codes k hcodes z hz charge hcharge p hp hg
  have HC :prefixLength P ((B).key (IntegralMixedMarkedReservedParent.context root))=((D).rules root).length:=by
    rw [IntegralMixedMarkedReservedParent.full_prefix,←IntegralMixedMarkedReservedCutView.plan_eq,
      IntegralMixedMarkedSeedTailVertex.full_length hn ht ha hR0 root codes k hcodes]
    rfl
  exact ⟨y,sample_observation hn ht ha hR0 root y hy HC,hy,hold,hpoint⟩

end LeanCanny.Encoding.IntegralMixedMarkedSeedTailRetained
