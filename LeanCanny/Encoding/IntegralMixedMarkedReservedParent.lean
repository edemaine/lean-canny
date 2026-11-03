/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalPrefixObservation
public import LeanCanny.Encoding.IntegralMixedMarkedPrefixObservation
public import LeanCanny.Encoding.IntegralFramedPhysicalBankTermPoint
/-! # A base full vertex supplies the honest parent of a replacement probe -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedMarkedReservedParent
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedHistoryFamilyBits (family keyAt prefixLength)
open IntegralMixedMarkedPrefixRun (reservedRoot reserved_count)
open IntegralMixedAuxiliaryMarkedIntegerSource (number)
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
 {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)

noncomputable def bank : IntegralFramedBankQuery.Bank:=IntegralMixedAuxiliaryMarkedRecordPlan.bank hn ht ha (radius_binary hR0)
local notation "B"=>bank hn ht ha hR0
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "D"=>IntegralFramedBankQuery.Bank.plan B
local notation "H"=>IntegralFramedBankQuery.Bank.data B

def context (root : List Bool):=pair root []

theorem key_root (root : List Bool) : pairFst ((B).key (context root))=root:=by
 change pairFst (IntegralMixedAuxiliaryMarkedRecordPlan.bankKey n (context root))=root
 simp only [IntegralMixedAuxiliaryMarkedRecordPlan.bankKey,context,pairFst_pair]

theorem full_prefix (root : List Bool) :
    prefixLength P ((B).key (context root))=IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n root :=by
 change prefixLength (IntegralMixedAuxiliaryMarkedRecordPlan.certifiedParameters hn ht ha (radius_binary hR0))
   (IntegralMixedAuxiliaryMarkedRecordPlan.bankKey n (context root))=_
 have HE:=IntegralMixedAuxiliaryMarkedRecordPlan.bank_count hn ht ha (radius_binary hR0) (context root)
 rw [IntegralMixedFramedBankSnapshotBits.count_prefix] at HE
 simpa only [context,pairFst_pair] using HE

theorem bound (root : List Bool) (j : ℕ) (hj : j≤IntegralMixedCausalRecordPlanBits.count root) :
    number n root+8+j≤(P).cap root+1:=IntegralMixedMarkedPrefixRun.bound hn ht ha hR0 root j hj

theorem observation_view (root : List Bool) (j : ℕ) (hj : j≤IntegralMixedCausalRecordPlanBits.count root) :
    IntegralFramedPhysicalPrefixObservation.atRoot P D root (number n root+8+j) (bound hn ht ha hR0 root j hj)=
      IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 root j hj:=rfl

attribute [local irreducible] bank

noncomputable abbrev input:=IntegralFramedPhysicalBankTerm.input B

theorem before_fit (old : List Bool) (codes : List (List Bool)) (probe aux : List Bool) :
    number n (reservedRoot old codes probe aux)+8+codes.length≤
      prefixLength P ((B).key (context (reservedRoot old codes probe aux))) :=by
 rw [full_prefix hn ht ha hR0,IntegralMixedAuxiliaryMarkedRecordPlan.fullCount,reserved_count]
 omega

theorem codes_good (old : List Bool) (codes : List (List Bool)) (probe aux : List Bool) :
    codes.length≤IntegralMixedCausalRecordPlanBits.count (reservedRoot old codes probe aux):=by
 rw [reserved_count]
 omega

variable (old : List Bool) (codes : List (List Bool)) (oldProbe oldAux : List Bool) (w : List Bool)
 (hv : SquareSampleCompleteVertices.Valid (input hn ht ha hR0) (context (reservedRoot old codes oldProbe oldAux)) w)
local notation "base"=>reservedRoot old codes oldProbe oldAux
local notation "jgood"=>codes_good old codes oldProbe oldAux

noncomputable def tuple : ℕ→ℝ:=IntegralFramedPhysicalPrefixObservation.tuple P D H
 (B).nodes (B).factor (B).seed (B).bounds (B).key (B).positive (context base) w hv

noncomputable def values : ℕ→ℝ :=(IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 base codes.length jgood).point
 (tuple hn ht ha hR0 old codes oldProbe oldAux w hv)

theorem base_roots : (IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 base codes.length jgood).Roots
    (tuple hn ht ha hR0 old codes oldProbe oldAux w hv) :=by
 have HM:=before_fit hn ht ha hR0 old codes oldProbe oldAux
 have HR:=IntegralFramedPhysicalPrefixObservation.roots P D H (B).nodes (B).factor (B).seed (B).bounds
   (B).key (B).positive (context base) w hv (number n base+8+codes.length) HM
 have HE:=IntegralFramedPhysicalPrefixObservation.at_congr P D
   (pairFst ((B).key (context base))) base (number n base+8+codes.length) (number n base+8+codes.length)
   (HM.trans (min_le_right _ _)) (bound hn ht ha hR0 base codes.length jgood)
   (key_root hn ht ha hR0 base) rfl
 have HH:=HE.trans (observation_view hn ht ha hR0 base codes.length jgood)
 exact (congrArg (fun O : IntegralMixedFramedRunObservation.Data=>O.Roots
   (tuple hn ht ha hR0 old codes oldProbe oldAux w hv)) HH).mp HR

theorem prepared_realizes (probe aux : List Bool) :
    IntegralMixedIntegerRealization.Realizes
      (IntegralMixedFramedFamilyRunView.runAt P D (reservedRoot old codes probe aux)
        (number n (reservedRoot old codes probe aux)+8+codes.length)
        (bound hn ht ha hR0 _ codes.length (codes_good old codes probe aux)))
      (values hn ht ha hR0 old codes oldProbe oldAux w hv) :=by
 have HE:=IntegralMixedMarkedPrefixObservation.reserved_eq hn ht ha hR0 old codes oldProbe probe oldAux aux
 have HZ : (IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 (reservedRoot old codes probe aux) codes.length
     (codes_good old codes probe aux)).Roots (tuple hn ht ha hR0 old codes oldProbe oldAux w hv) :=by
   exact (congrArg (fun O : IntegralMixedFramedRunObservation.Data=>O.Roots
     (tuple hn ht ha hR0 old codes oldProbe oldAux w hv)) HE).mp
       (base_roots hn ht ha hR0 old codes oldProbe oldAux w hv)
 have HZ' : (IntegralFramedPhysicalPrefixObservation.atRoot P D (reservedRoot old codes probe aux)
     (number n (reservedRoot old codes probe aux)+8+codes.length)
     (bound hn ht ha hR0 _ codes.length (codes_good old codes probe aux))).Roots
       (tuple hn ht ha hR0 old codes oldProbe oldAux w hv) :=by
   exact (congrArg (fun O : IntegralMixedFramedRunObservation.Data=>O.Roots
     (tuple hn ht ha hR0 old codes oldProbe oldAux w hv))
       (observation_view hn ht ha hR0 _ codes.length (codes_good old codes probe aux))).mpr HZ
 have HR:=IntegralFramedPhysicalPrefixObservation.at_realizes P D (reservedRoot old codes probe aux)
   (number n (reservedRoot old codes probe aux)+8+codes.length)
   (bound hn ht ha hR0 _ codes.length (codes_good old codes probe aux))
   (tuple hn ht ha hR0 old codes oldProbe oldAux w hv) HZ'
 have HP :=congrArg (fun O : IntegralMixedFramedRunObservation.Data=>O.point
   (tuple hn ht ha hR0 old codes oldProbe oldAux w hv))
     ((observation_view hn ht ha hR0 _ codes.length (codes_good old codes probe aux)).trans HE.symm)
 exact (congrArg (fun v : ℕ→ℝ=>IntegralMixedIntegerRealization.Realizes
   (IntegralMixedFramedFamilyRunView.runAt P D (reservedRoot old codes probe aux)
     (number n (reservedRoot old codes probe aux)+8+codes.length)
     (bound hn ht ha hR0 _ codes.length (codes_good old codes probe aux))) v) HP).mp HR

theorem prepared_canonical_realizes (probe aux savedAux : List Bool) :
    IntegralMixedIntegerRealization.Realizes
      (IntegralMixedFramedFamilyRunView.stateView P D H
        (keyAt (reservedRoot old codes probe aux) (number n (reservedRoot old codes probe aux)+8+codes.length) savedAux))
      (values hn ht ha hR0 old codes oldProbe oldAux w hv) :=
 (IntegralMixedSourceIntegerPaddingRealization.realizes_at_key_iff P D H _ savedAux _
   (bound hn ht ha hR0 _ codes.length (codes_good old codes probe aux)) _).mpr
   (prepared_realizes hn ht ha hR0 old codes oldProbe oldAux w hv probe aux)

end LeanCanny.Encoding.IntegralMixedMarkedReservedParent
