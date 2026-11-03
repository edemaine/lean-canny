/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralMixedMarkedReservedParent
public import LeanCanny.Encoding.IntegralMixedMarkedPrefixFieldReadback
public import LeanCanny.Encoding.IntegralMixedPhysicalMarkedContext
/-! # Prepared-probe old values are the literal native parent readback -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedMarkedReservedPoint
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (family)
open IntegralMixedMarkedPrefixRun (reservedRoot)
open IntegralMixedOriginalRegularSource (radius_binary)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralMixedExceptionalBounds.auxiliaryCap
 IntegralMixedAuxiliaryMarkedIntegerSource.degreeBound IntegralMixedAuxiliaryMarkedIntegerPlan.degree
 IntegralMixedAuxiliaryMarkedIntegerSource.source IntegralMixedFramedRawHeight.rootCeiling
 IntegralMixedFramedNormalizationBits.requiredModulus
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
 (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q) {R0 : List Bool→ℕ} (hR0 : BinaryFn R0)

theorem input_eq :IntegralMixedMarkedReservedParent.input hn ht ha hR0=
    IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false:=rfl

private theorem natural_input_eq (I J : SquareSampleInput.Inputs) (he : I=J) (c w : List Bool)
    (hi : SquareSampleCompleteVertices.Valid I c w) (hj : SquareSampleCompleteVertices.Valid J c w) :
    IntegralFramedPhysicalSquareContext.naturalValue I c w hi=
      IntegralFramedPhysicalSquareContext.naturalValue J c w hj:=by cases he;rfl

private theorem tuple_natural (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (L F C : List Bool→ℕ)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C) (key : List Bool→List Bool)
    (hp : ∀c,0<(family P D H).birth (key c)) (c w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input P D H L F C hs key hp) c w) :
    IntegralFramedPhysicalPrefixObservation.tuple P D H L F C hs key hp c w hv=
      IntegralFramedPhysicalSquareContext.naturalValue (IntegralFramedPhysicalSquare.input P D H L F C hs key hp) c w hv:=rfl

private theorem square_natural (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (L F C : List Bool→ℕ)
    (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C) (key : List Bool→List Bool)
    (hp : ∀c,0<(family P D H).birth (key c)) (c w : List Bool)
    (hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input P D H L F C hs key hp) c w) :
    IntegralFramedPhysicalSquare.naturalPoint P D H L F C hs key hp c w hv=
      IntegralFramedPhysicalSquareContext.naturalValue (IntegralFramedPhysicalSquare.input P D H L F C hs key hp) c w hv:=rfl

variable (old : List Bool) (codes : List (List Bool)) (probe aux w : List Bool)
 (hv : SquareSampleCompleteVertices.Valid (IntegralMixedMarkedReservedParent.input hn ht ha hR0)
   (IntegralMixedMarkedReservedParent.context (reservedRoot old codes probe aux)) w)

include hv in
theorem native_valid :SquareSampleCompleteVertices.Valid (IntegralMixedPhysicalMarkedTest.input hn ht ha (radius_binary hR0) false)
    (IntegralMixedMarkedPrefixFieldReadback.context (reservedRoot old codes probe aux)) w:=
 (congrArg (fun I : SquareSampleInput.Inputs=>SquareSampleCompleteVertices.Valid I
   (IntegralMixedMarkedReservedParent.context (reservedRoot old codes probe aux)) w)
     (input_eq hn ht ha hR0)).mp hv

attribute [local irreducible] IntegralMixedMarkedReservedParent.bank IntegralMixedPhysicalMarkedPlan.bank
 IntegralFramedPhysicalSquare.input

theorem tuple_eq :IntegralMixedMarkedReservedParent.tuple hn ht ha hR0 old codes probe aux w hv=
    IntegralMixedMarkedPrefixFieldReadback.natural hn ht ha hR0 (reservedRoot old codes probe aux) w
      (native_valid hn ht ha hR0 old codes probe aux w hv):=by
 let B:=IntegralMixedMarkedReservedParent.bank hn ht ha hR0
 let C:=IntegralMixedPhysicalMarkedPlan.bank hn ht ha (radius_binary hR0) false
 let c:=IntegralMixedMarkedReservedParent.context (reservedRoot old codes probe aux)
 have HL:=tuple_natural B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds B.key B.positive c w hv
 have HR:=square_natural C.parameters C.plan C.data C.nodes C.factor C.seed C.bounds C.key C.positive c w
   (native_valid hn ht ha hR0 old codes probe aux w hv)
 exact HL.trans ((natural_input_eq _ _ (input_eq hn ht ha hR0) c w hv _).trans HR.symm)

private theorem observation_congr (root : List Bool) (i j : ℕ)
    (hi : i≤IntegralMixedCausalRecordPlanBits.count root) (hj : j≤IntegralMixedCausalRecordPlanBits.count root) (he : i=j) :
    IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 root i hi=
      IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 root j hj:=by cases he;rfl

theorem values_eq :IntegralMixedMarkedReservedParent.values hn ht ha hR0 old codes probe aux w hv=
    IntegralMixedMarkedPrefixFieldReadback.parentPoint hn ht ha hR0 (reservedRoot old codes probe aux) w
      (native_valid hn ht ha hR0 old codes probe aux w hv):=by
 let root:=reservedRoot old codes probe aux
 have HC : codes.length=IntegralMixedCausalRecordPlanBits.count root-1:=by
   rw [IntegralMixedMarkedPrefixRun.reserved_count]
   omega
 have HE:=observation_congr hn ht ha hR0 root codes.length (IntegralMixedCausalRecordPlanBits.count root-1)
   (IntegralMixedMarkedReservedParent.codes_good old codes probe aux) (Nat.sub_le _ _) HC
 have HV:=congrArg (fun O : IntegralMixedFramedRunObservation.Data=>O.point
   (IntegralMixedMarkedReservedParent.tuple hn ht ha hR0 old codes probe aux w hv)) HE
 have HZ:=congrArg (fun z : ℕ→ℝ=>(IntegralMixedMarkedPrefixObservation.observation hn ht ha hR0 root
   (IntegralMixedCausalRecordPlanBits.count root-1) (Nat.sub_le _ _)).point z)
   (tuple_eq hn ht ha hR0 old codes probe aux w hv)
 exact HV.trans HZ

end LeanCanny.Encoding.IntegralMixedMarkedReservedPoint
