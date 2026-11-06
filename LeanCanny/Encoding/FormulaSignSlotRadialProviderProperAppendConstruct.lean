/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendCriticalScan
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendCompanions
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendBeforeProbe
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendPrelude
/-! # Fresh accepted proper children at prescribed geometric endpoints -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open IntegralMixedHistory
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem cast_function_heq {n m : ℕ} (h : n=m) (p : Fin (m+1)→ℝ) :
    HEq (fun i : Fin (n+1)=>p (Fin.cast (congrArg (·+1) h) i)) p := by cases h;rfl

private theorem point_at_context (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid FormulaSignSlotRadialProviderAtomic.input c w)
    (b : ℕ) (hc : FormulaSignSlotRadialProviderAtomic.context q=c)
    (hword : FormulaSignSlotRadialProviderAtomic.word q=w)
    (hb : FormulaSignSlotRadialProviderAtomic.anchor (FormulaSignSlotRadialProviderAtomic.dimension q)
      (FormulaSignSlotRadialProviderAtomic.initial q) q=b) :
    HEq (FormulaSignSlotRadialProviderAtomic.point q hv)
      (FormulaSignSlotRadialProviderAtomic.geometricPoint c w hw b) := by
  cases hc
  cases hword
  cases hb
  rfl

local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
local notation "C" => FormulaSignSlotRadialProviderRecordPrefix.context
local notation "N" => FormulaSignSlotRadialProviderAtomic.initial
local notation "A" => FormulaSignSlotRadialProviderAtomic.Valid
open FormulaSignSlotRadialProviderAtomic (dimension depth)
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderRetainedAppend.parentState FormulaSignSlotRadialProviderRetainedAppend.parentTuple
  FormulaSignSlotRadialProviderRetainedAppend.parentValues FormulaSignSlotRadialProviderRetainedAppend.parentHom
  FormulaSignSlotRadialProviderRetainedAppend.parentCommands FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor

variable {old : List Bool} {hv : A old} {hd : depth old<dimension old}
  {left right : ParentEndpoint old hv hd} {R : CanonicalPair old hv hd left right} {side : Bool}
  {pMID pChild : Fin ((P).ambient (FormulaSignSlotRadialProviderRetainedAppend.preparedRoot old
    (FormulaSignSlotRadialProviderAtomic.ownBirth old))+1)→ℝ}

theorem nativePoint_heq (old : List Bool) (hv : A old) (hd : depth old<dimension old)
    (left right : ParentEndpoint old hv hd) (R : CanonicalPair old hv hd left right) (side : Bool)
    (p : Fin ((P).ambient (FormulaSignSlotRadialProviderRetainedAppend.preparedRoot old
      (FormulaSignSlotRadialProviderAtomic.ownBirth old))+1)→ℝ) :
    HEq (nativePoint old hv hd left right R side p) p :=
  cast_function_heq (native_dimension old hv hd left right R side) p

theorem SampledLevel.atomic_valid (S : SampledLevel old hv hd left right R side pMID pChild) :
    A (packet (dimension old) old R.leftSpec R.rightSpec side S.receipt.word) :=
  ⟨grammar old hv hd R.leftSpec R.rightSpec side (endpoints_good old hv hd left right R) S.receipt.word,
    S.receipt.full_valid,S.before_probe,S.all_critical,S.latest_companions,S.marked,S.replay⟩

theorem SampledLevel.point_heq (S : SampledLevel old hv hd left right R side pMID pChild)
    (hnew : A (packet (dimension old) old R.leftSpec R.rightSpec side S.receipt.word)) :
    HEq (FormulaSignSlotRadialProviderAtomic.point
      (packet (dimension old) old R.leftSpec R.rightSpec side S.receipt.word) hnew) pChild := by
  let anchor := midpointBirth old hv hd left right R+1+(dimension old-depth old)
  have HA : FormulaSignSlotRadialProviderAtomic.anchor
      (dimension (packet (dimension old) old R.leftSpec R.rightSpec side S.receipt.word))
      (N (packet (dimension old) old R.leftSpec R.rightSpec side S.receipt.word))
      (packet (dimension old) old R.leftSpec R.rightSpec side S.receipt.word)=anchor := by
    change IntegralMixedRoadmapAtomic.anchor (dimension (packet (dimension old) old R.leftSpec R.rightSpec side S.receipt.word))
      (N (packet (dimension old) old R.leftSpec R.rightSpec side S.receipt.word)) _=_
    rw [dimension_packet,initial_packet]
    exact latest_anchor_packet old hv hd left right R side S.receipt.word
  have H := point_at_context _ hnew (C (preparedRoot old R.leftSpec R.rightSpec side)) S.receipt.word S.receipt.valid anchor
    (context_packet old R.leftSpec R.rightSpec side S.receipt.word) (word_packet _ _ _ _ _ _) HA
  have HF := finish_eq old hv hd left right R side
  have HG := S.local_geometric_point old hv hd left right R side anchor (by dsimp only [anchor];omega)
    (by dsimp only [anchor];omega)
  have HPhase : ¬anchor<midpointBirth old hv hd left right R+1+(dimension old-depth old) := by omega
  simp only [ite_eq_right HPhase] at HG
  exact H.trans ((heq_of_eq HG).trans (nativePoint_heq old hv hd left right R side pChild))

private theorem field_at_context (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q)
    (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid FormulaSignSlotRadialProviderAtomic.input c w)
    (hc : FormulaSignSlotRadialProviderAtomic.context q=c)
    (hword : FormulaSignSlotRadialProviderAtomic.word q=w) (b : ℕ) :
    FormulaSignSlotRadialProviderAtomic.field q hv b=FormulaSignSlotRadialProviderAtomic.bankField c w hw b := by
  cases hc
  cases hword
  rfl

theorem SampledLevel.accepted_old_fields (S : SampledLevel old hv hd left right R side pMID pChild)
    (b : ℕ) (hb : b<N old+start old) :
    FormulaSignSlotRadialProviderAtomic.field
      (packet (dimension old) old R.leftSpec R.rightSpec side S.receipt.word) S.atomic_valid b=
      FormulaSignSlotRadialProviderAtomic.field old hv b :=
  (field_at_context _ S.atomic_valid (C (preparedRoot old R.leftSpec R.rightSpec side)) S.receipt.word S.receipt.valid
    (context_packet old R.leftSpec R.rightSpec side S.receipt.word) (word_packet _ _ _ _ _ _) b).trans (S.old_fields b hb)

section GeometricConstruction
open LeanCanny.Connectivity IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryScript IntegralMixedChronologicalEndpoint
open IntegralMixedChronologicalFrame IntegralMixedFrozenFrame IntegralMixedOptionalEndpoints IntegralMixedRelativeCuts
open IntegralMixedChosenLocalRealization IntegralMixedCriticalSweep
variable (old : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid old)
  (hd : FormulaSignSlotRadialProviderAtomic.depth old<FormulaSignSlotRadialProviderAtomic.dimension old)
local notation "E" => FormulaSignSlotRadialProviderAtomic.ownBirth old
local notation "he" => FormulaSignSlotRadialProviderRetainedAppend.own_endpoint_fit old
local notation "c" => FormulaSignSlotRadialProviderRetainedAppend.preparedRoot old E
local notation "cs" => FormulaSignSlotRadialProviderRetainedAppend.parentCommands old hv hd E he
local notation "x" => FormulaSignSlotRadialProviderRetainedAppend.parentState old hv hd E he
local notation "d" => FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor old hv hd E he
local notation "hk" => FormulaSignSlotRadialProviderRetainedAppend.parent_descriptor_fit old hv hd E he
local notation "V" => FormulaSignSlotRadialProviderRetainedAppend.parentValues old hv hd E he
local notation "phi" => FormulaSignSlotRadialProviderRetainedAppend.parentHom old hv hd E he
local notation "hm" => FormulaSignSlotRadialProviderRetainedAppend.parent_horizon old hv hd E he
local notation "g" => FormulaSignSlotRadialProviderRetainedAppend.childCoordinate old hv hd E he
local notation "hg" => FormulaSignSlotRadialProviderRetainedAppend.child_coordinate_free old hv hd E he
local notation "h" => IntegralMixedChronologicalSweepFrame.next d hk
local notation "choices" => FormulaSignSlotRadialProviderRetainedAppend.levelChoices old hv hd E he
attribute [local irreducible] FormulaSignSlotRadialProviderRetainedAppend.levelChoices
variable (left right : ParentEndpoint old hv hd)
local notation "a" => left.value V
local notation "b" => right.value V

theorem exists_valid_level
    (HL : left.Allowed (jointEndpointSet x hm phi (d).frame h g hg V choices))
    (HR : right.Allowed (jointEndpointSet x hm phi (d).frame h g hg V choices))
    (hab : a<b)
    (M : MatchedSlabInterior x hm phi (line (d).frame h) h (Finset.mem_insert_self _ _) g hg V a b
      ⟨(a+b)/2,by constructor <;> linarith⟩)
    (fiber : IntegralMixedSelectedPhysicalFiber.physical (cutSource x (d).frame h) hm
      (cutRule x (d).frame h g hg) phi ((a+b)/2)) :
    let rho := FrozenCoordinateOrdering.permutation (line (d).frame h).frozen
    let pMID := M.curve fiber ((a+b)/2)∘rho.symm
    ∃R : CanonicalPair old hv hd left right,∀side,
      let pChild := M.curve fiber (if side then b else a)∘rho.symm
      ∃S : SampledLevel old hv hd left right R side pMID pChild,
      ∃hq : A (packet (dimension old) old R.leftSpec R.rightSpec side S.receipt.word),
        FormulaSignSlotRadialProviderAtomic.provider
          (packet (dimension old) old R.leftSpec R.rightSpec side S.receipt.word)=FormulaSignSlotRadialProviderAtomic.provider old ∧
        depth (packet (dimension old) old R.leftSpec R.rightSpec side S.receipt.word)=depth old+1 ∧
        HEq (FormulaSignSlotRadialProviderAtomic.point
          (packet (dimension old) old R.leftSpec R.rightSpec side S.receipt.word) hq) pChild ∧
        ∀j<N old+start old,FormulaSignSlotRadialProviderAtomic.field
          (packet (dimension old) old R.leftSpec R.rightSpec side S.receipt.word) hq j=
            FormulaSignSlotRadialProviderAtomic.field old hv j := by
  dsimp only
  obtain ⟨R,HR⟩ := exists_sampled_level old hv hd left right HL HR hab M fiber
  refine ⟨R,?_⟩
  intro side
  obtain ⟨S⟩ := HR side
  exact ⟨S,S.atomic_valid,provider_packet _ _ _ _ _ _,depth_packet _ _ _ _ _ _,
    S.point_heq S.atomic_valid,S.accepted_old_fields⟩
end GeometricConstruction

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
