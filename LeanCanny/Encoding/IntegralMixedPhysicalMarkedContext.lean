/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalSquareContext
public import LeanCanny.Encoding.IntegralFramedPhysicalPrefixPoint
public import LeanCanny.Encoding.IntegralMixedPhysicalFieldEqualitySemantics
/-! # Auxiliary context changes preserve the entire actual marked sample

This is only a SAME-root theorem. All sampler input fields factor through
the root, so naturality preserves this complete word and its full tuple.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalMarkedContext
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (family commands initial keyAt)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n : List Bool→ℕ} {t : List Bool→Term} (hn : UnaryFn n)
  (ht : (fun q=>(t q).toData.toBits)∈FP) (ha : ∀q,(t q).arity≤n q)
  {R : List Bool→ℕ} (hR : BinaryFn R)
local notation "B"=>IntegralMixedPhysicalMarkedPlan.bank hn ht ha hR false
local notation "P"=>IntegralFramedBankQuery.Bank.parameters B
local notation "D"=>IntegralFramedBankQuery.Bank.plan B
local notation "H"=>IntegralFramedBankQuery.Bank.data B
local notation "S"=>IntegralMixedPhysicalMarkedTest.input hn ht ha hR false

theorem key_eq (c d : List Bool) (hc : pairFst c=pairFst d) :(B).key c=(B).key d :=by
  change IntegralMixedAuxiliaryMarkedRecordPlan.bankKey n c=IntegralMixedAuxiliaryMarkedRecordPlan.bankKey n d
  simp only [IntegralMixedAuxiliaryMarkedRecordPlan.bankKey,hc]

theorem root_positive (r : List Bool) :
    0<(family P D H).birth (keyAt r (IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n r) []) :=by
  rw [IntegralMixedFramedHistoryFamilyBits.family_birth,
    IntegralMixedFramedHistoryFamilyBits.keyAt_prefix P r _ [] (by
      change IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n r≤
        IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n r+2+1;omega)]
  unfold IntegralMixedAuxiliaryMarkedRecordPlan.fullCount
  omega

noncomputable def rootInput :=IntegralFramedPhysicalSquareContext.rootInput P D H
  (B).nodes (B).factor (B).seed (B).bounds
  (IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n) (root_positive hn ht ha hR)

theorem input_factor :S=SquareSampleInput.comp (rootInput hn ht ha hR) pairFst :=by
  exact IntegralFramedPhysicalSquareContext.input_root_factor P D H (B).nodes (B).factor (B).seed (B).bounds
    (IntegralMixedAuxiliaryMarkedRecordPlan.fullCount n) (fun _=>[]) (root_positive hn ht ha hR)

theorem valid_root (c w : List Bool) :SquareSampleCompleteVertices.Valid S c w↔
    SquareSampleCompleteVertices.Valid (rootInput hn ht ha hR) (pairFst c) w :=by
  rw [input_factor]
  exact SquareSampleCompleteNaturality.complete_valid_comp _ _ _ _

theorem valid_iff (c d w : List Bool) (hc : pairFst c=pairFst d) :
    SquareSampleCompleteVertices.Valid S c w↔SquareSampleCompleteVertices.Valid S d w :=by
  rw [valid_root,valid_root,hc]

attribute [local irreducible] IntegralMixedPhysicalMarkedPlan.bank

private theorem natural_input_eq (I J : SquareSampleInput.Inputs) (hI : I=J) (c w : List Bool)
    (hi : SquareSampleCompleteVertices.Valid I c w) (hj : SquareSampleCompleteVertices.Valid J c w) :
    IntegralFramedPhysicalSquareContext.naturalValue I c w hi=
      IntegralFramedPhysicalSquareContext.naturalValue J c w hj :=by
  cases hI
  rfl

private theorem natural_context_eq (I : SquareSampleInput.Inputs) (c d w : List Bool) (hc : c=d)
    (hi : SquareSampleCompleteVertices.Valid I c w) (hj : SquareSampleCompleteVertices.Valid I d w) :
    IntegralFramedPhysicalSquareContext.naturalValue I c w hi=
      IntegralFramedPhysicalSquareContext.naturalValue I d w hj :=by
  cases hc
  rfl

private theorem natural_comp (I : SquareSampleInput.Inputs) (f : List Bool→List Bool) (c w : List Bool)
    (hi : SquareSampleCompleteVertices.Valid (SquareSampleInput.comp I f) c w)
    (hj : SquareSampleCompleteVertices.Valid I (f c) w) :
    IntegralFramedPhysicalSquareContext.naturalValue (SquareSampleInput.comp I f) c w hi=
      IntegralFramedPhysicalSquareContext.naturalValue I (f c) w hj :=by
  funext i
  unfold IntegralFramedPhysicalSquareContext.naturalValue
  change (if h : i<I.count (f c) then
    (SquareSampleCompleteVertices.candidate (SquareSampleInput.comp I f) c w hi).val ⟨i,h⟩ else 0)=_
  split_ifs with h
  · exact congrFun (SquareSampleCompleteNaturality.candidate_comp I f c w hi hj) ⟨i,h⟩
  · rfl

theorem natural_root (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w) :
    IntegralFramedPhysicalSquareContext.naturalValue S c w hv=
    IntegralFramedPhysicalSquareContext.naturalValue (rootInput hn ht ha hR) (pairFst c) w
      ((valid_root hn ht ha hR c w).mp hv) :=by
  have HE:=input_factor hn ht ha hR
  have HC :SquareSampleCompleteVertices.Valid (SquareSampleInput.comp (rootInput hn ht ha hR) pairFst) c w:=HE ▸ hv
  exact (natural_input_eq _ _ HE c w hv HC).trans (natural_comp _ _ c w HC _)

theorem natural_eq (c d w : List Bool) (hc : pairFst c=pairFst d)
    (hv : SquareSampleCompleteVertices.Valid S c w) (hd : SquareSampleCompleteVertices.Valid S d w) :
    IntegralFramedPhysicalSquare.naturalPoint P D H (B).nodes (B).factor (B).seed (B).bounds
      (B).key (B).positive c w hv=
    IntegralFramedPhysicalSquare.naturalPoint P D H (B).nodes (B).factor (B).seed (B).bounds
      (B).key (B).positive d w hd :=by
  change IntegralFramedPhysicalSquareContext.naturalValue S c w hv=
    IntegralFramedPhysicalSquareContext.naturalValue S d w hd
  rw [natural_root hn ht ha hR c w hv,natural_root hn ht ha hR d w hd]
  exact natural_context_eq _ _ _ _ hc _ _

private noncomputable def observation (k : List Bool) :=IntegralMixedFramedRunObservation.ofCommands
  (initial P D (pairFst k)) (commands P D k)
  (((family P D H).birth_bound k).trans (Nat.le_succ _))

private theorem newest_value (c w : List Bool) (hv : SquareSampleCompleteVertices.Valid S c w) (i : ℕ) :
    IntegralMixedPhysicalFieldEquality.pointNewest hn ht ha hR c w hv i=
      (observation hn ht ha hR ((B).key c)).point
        (IntegralFramedPhysicalSquare.naturalPoint P D H (B).nodes (B).factor (B).seed (B).bounds
          (B).key (B).positive c w hv) (min i (IntegralMixedPhysicalFieldEquality.count hn ht ha hR c-1)) :=by
  unfold IntegralMixedPhysicalFieldEquality.pointNewest
  exact (IntegralFramedPhysicalPrefixPoint.full_point P D H (B).nodes (B).factor (B).seed (B).bounds
    (B).key (B).positive c w hv _).symm

theorem pointNewest_eq (c d w : List Bool) (hc : pairFst c=pairFst d)
    (hv : SquareSampleCompleteVertices.Valid S c w) (hd : SquareSampleCompleteVertices.Valid S d w) (i : ℕ) :
    IntegralMixedPhysicalFieldEquality.pointNewest hn ht ha hR c w hv i=
      IntegralMixedPhysicalFieldEquality.pointNewest hn ht ha hR d w hd i :=by
  have HK:=key_eq hn ht ha hR c d hc
  have HC :IntegralMixedPhysicalFieldEquality.count hn ht ha hR c=
      IntegralMixedPhysicalFieldEquality.count hn ht ha hR d :=congrArg ((family P D H).birth) HK
  refine (newest_value hn ht ha hR c w hv i).trans (Eq.trans ?_
    (newest_value hn ht ha hR d w hd i).symm)
  have HO:=congrArg (observation hn ht ha hR) HK
  have HN:=natural_eq hn ht ha hR c d w hc hv hd
  refine (congrArg₂ (fun data z=>data.point z (min i (IntegralMixedPhysicalFieldEquality.count hn ht ha hR c-1))) HO HN).trans ?_
  exact congrArg (fun j=>(observation hn ht ha hR ((B).key d)).point
    (IntegralFramedPhysicalSquare.naturalPoint P D H (B).nodes (B).factor (B).seed (B).bounds
      (B).key (B).positive d w hd) j) (congrArg (fun m=>min i (m-1)) HC)

theorem point_eq (c d w : List Bool) (hc : pairFst c=pairFst d)
    (hv : SquareSampleCompleteVertices.Valid S c w) (hd : SquareSampleCompleteVertices.Valid S d w) (i : ℕ) :
    IntegralMixedPhysicalFieldEquality.point hn ht ha hR c w hv i=
      IntegralMixedPhysicalFieldEquality.point hn ht ha hR d w hd i :=by
  have HC :IntegralMixedPhysicalFieldEquality.count hn ht ha hR c=
      IntegralMixedPhysicalFieldEquality.count hn ht ha hR d :=
    congrArg ((family P D H).birth) (key_eq hn ht ha hR c d hc)
  unfold IntegralMixedPhysicalFieldEquality.point
  rw [HC]
  exact pointNewest_eq hn ht ha hR c d w hc hv hd _
end LeanCanny.Encoding.IntegralMixedPhysicalMarkedContext
