/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendWord
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendPaddingPoint
/-! # A coherent fresh retained-child word with all local and padding readbacks -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFramedPhysicalIndex
open IntegralMixedFramedHistoryFamilyBits (initial)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "D" => FormulaSignSlotRadialProviderRecordPlan.certifiedPlan
local notation "Q" => FormulaSignSlotRadialProviderRecordPlan.spatial
local notation "cap" => FormulaSignSlotRadialProviderRecordReceipt.actual_spatial_cap
local notation "N" => FormulaSignSlotRadialProviderAtomic.initial
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid
open FormulaSignSlotRadialProviderAtomic (dimension depth endBirth)
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  parentState parentTuple parentValues parentHom parentCommands parentDescriptor
  levelProgram levelObservation fullObservation

def FullReadback (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (N old) old) (R : Pair old hv hd e he)
    (z : ℕ→ℝ) (p : Fin ((P).ambient (preparedRoot old e)+1)→ℝ) (u : ℕ→ℝ) : Prop :=
  (fullObservation old e).Roots u ∧
    (∀i,i<arity (levelProgram old hv hd e he R false)→u i=z i) ∧
    (∀j : Fin (IntegralMixedCanonicalPadding.paddingSelections
        ((P).ambient (preparedRoot old e)) (tailCount old e)).length,
      ∀i : Fin ((P).ambient (preparedRoot old e)+1),
      u (arity (levelProgram old hv hd e he R false)+
        (2*(P).ambient (preparedRoot old e)+4)*
          ((IntegralMixedCanonicalPadding.paddingSelections ((P).ambient (preparedRoot old e)) (tailCount old e)).length-1-j.val)+i.val)^
        UniformIntegralPowerSchedule.physical ((P).cap (preparedRoot old e)+1) (2^(P).width (preparedRoot old e))
          ((levelProgram old hv hd e he R false).length+
            ((IntegralMixedCanonicalPadding.paddingSelections ((P).ambient (preparedRoot old e)) (tailCount old e)).length-1-j.val))=p i) ∧
    ∀i : Fin ((levelProgram old hv hd e he R false).length+
        (IntegralMixedCanonicalPadding.paddingSelections ((P).ambient (preparedRoot old e)) (tailCount old e)).length),
      (fullObservation old e).point u i.val=IntegralMixedPointCompanion.values p
        (fun j=>(levelObservation old hv hd e he R false).point z j.val)
        (IntegralMixedCanonicalPadding.paddingSelections ((P).ambient (preparedRoot old e)) (tailCount old e)) i

def LocalReadback (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (N old) old) (R : Pair old hv hd e he)
    (z : ℕ→ℝ) (p : Fin ((P).ambient (preparedRoot old e)+1)→ℝ) : Prop :=
  (levelObservation old hv hd e he R false).Roots z ∧
    R.PhysicalReadback
      (IntegralMixedStaticRecordPrefix.cap (Q (preparedRoot old e)) (cap (preparedRoot old e)))
      (parentCommands old hv hd e he) (parent_descriptor_fit old hv hd e he)
      (childCoordinate old hv hd e he) (child_coordinate_free old hv hd e he) false
      (pair_level_room old hv hd e he R) (arity (levelProgram old hv hd e he R false)) z p p
      (fun j=>(levelObservation old hv hd e he R false).point z j) ∧
    ∀j : Index (Fin 0) (parentCommands old hv hd e he),
      z (enumerate (parentCommands old hv hd e he) j).val=parentTuple old hv hd e he j

structure BankWord (B : IntegralFramedBankQuery.Bank) (c : List Bool) (u : ℕ→ℝ) where
  word : List Bool
  valid : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalBankTerm.input B) c word
  width : word.length=SquareSampleCompleteVertices.width (IntegralFramedPhysicalBankTerm.input B) c
  joint : ∀i : Fin (IntegralFramedPhysicalSquare.count B.parameters B.plan (B.key c)),
    IntegralFramedPhysicalSquare.joint B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds
      B.key B.positive c word valid i=u i.val

structure WordReceipt (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (N old) old)
    (p : Fin ((P).ambient (preparedRoot old e)+1)→ℝ) where
  pair : Pair old hv hd e he
  localTuple : ℕ→ℝ
  local_readback : LocalReadback old hv hd e he pair localTuple p
  paddingPoint : Fin ((P).ambient (preparedRoot old e)+1)→ℝ
  tuple : ℕ→ℝ
  full : FullReadback old hv hd e he pair localTuple paddingPoint tuple
  sample : BankWord FormulaSignSlotRadialProviderRecordPlan.bank
    (FormulaSignSlotRadialProviderRecordPrefix.context (preparedRoot old e)) tuple

abbrev WordReceipt.word {old hv hd e he p} (W : WordReceipt old hv hd e he p) := W.sample.word
abbrev WordReceipt.valid {old hv hd e he p} (W : WordReceipt old hv hd e he p) := W.sample.valid
abbrev WordReceipt.width {old hv hd e he p} (W : WordReceipt old hv hd e he p) := W.sample.width
abbrev WordReceipt.joint {old hv hd e he p} (W : WordReceipt old hv hd e he p) := W.sample.joint

theorem exists_word_receipt (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (e : ℕ) (he : e<endBirth (dimension old) (N old) old)
    (p : Fin ((P).ambient (preparedRoot old e)+1)→ℝ)
    (HS : p∈IntegralMixedFrozenFrame.slice (Q (preparedRoot old e))
      (parentDescriptor old hv hd e he).frame (parentValues old hv hd e he))
    (Hh : p (IntegralMixedChronologicalSweepFrame.next (parentDescriptor old hv hd e he)
      (parent_descriptor_fit old hv hd e he))=
        parentValues old hv hd e he (IntegralMixedChronologicalMidpoint.reference (endpointLabel old hv hd e he)))
    (Hgrad : ∀i,i∉insert (IntegralMixedChronologicalSweepFrame.next (parentDescriptor old hv hd e he)
      (parent_descriptor_fit old hv hd e he)) (parentDescriptor old hv hd e he).frame.frozen→
        i≠childCoordinate old hv hd e he→(MvPolynomial.pderiv i
          (FermatCriticalHomogenization.polynomial (Q (preparedRoot old e)).low
            (Q (preparedRoot old e)).leading (Q (preparedRoot old e)).degree)).eval₂ (Int.castRingHom ℝ) p=0) :
    Nonempty (WordReceipt old hv hd e he p) := by
  have HL := exists_level_tuple old hv hd e he p HS Hh Hgrad
  unfold LevelTuple PhysicalLevelTuple at HL
  obtain ⟨R,HR⟩ := HL
  let z : ℕ→ℝ := Classical.choose (HR false)
  have HL : LocalReadback old hv hd e he R z p := by
    unfold LocalReadback levelObservation levelProgram
    exact Classical.choose_spec (HR false)
  obtain ⟨p0,hp0,hg0⟩ := exists_padding_critical old e p HS.1
  have HP := exists_padding_tuple old hv hd e he R z HL.1 p0 hp0 hg0
  unfold PaddingTuple at HP
  obtain ⟨u,hu,hO,hB,hV⟩ := HP
  have HF : FullReadback old hv hd e he R z p0 u := ⟨hu,hO,hB,hV⟩
  have HW := sample_full_tuple old e u hu
  unfold Sampled JointSampled at HW
  obtain ⟨w,hw,hwidth,hjoint⟩ := HW
  exact ⟨⟨R,z,HL,p0,u,HF,⟨w,hw,hwidth,hjoint⟩⟩⟩

end LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
