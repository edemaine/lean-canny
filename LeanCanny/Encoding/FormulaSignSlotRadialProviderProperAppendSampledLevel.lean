/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendGeometry
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendWordReceipt
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppendPaddingPoint
/-! # One actual proper family has fresh own words and all coherent readbacks -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation LeanCanny.Connectivity IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedChronologicalEndpoint
open IntegralMixedChronologicalFrame IntegralMixedFrozenFrame IntegralMixedOptionalEndpoints IntegralMixedRelativeCuts
open IntegralMixedChosenLocalRealization IntegralMixedCriticalSweep
open IntegralMixedFramedPhysicalIndex (arity)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
local notation "P" => FormulaSignSlotRadialProviderRecordPlan.certifiedParameters
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
noncomputable local instance providerProperSampledLevelIndexFintype : Fintype (Index (Fin 0) cs) := indexFintype (Fin 0) cs
attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderRetainedAppend.parentCommands FormulaSignSlotRadialProviderRetainedAppend.parentState
  FormulaSignSlotRadialProviderRetainedAppend.parentDescriptor FormulaSignSlotRadialProviderRetainedAppend.parentValues
  FormulaSignSlotRadialProviderRetainedAppend.parentHom FormulaSignSlotRadialProviderRetainedAppend.levelChoices
  FormulaSignSlotRadialProviderRetainedAppend.parentTuple
  FormulaSignSlotRadialProviderAtomic.dimension FormulaSignSlotRadialProviderAtomic.initial
  FormulaSignSlotRadialProviderAtomic.depth

structure SampledLevel (left right : ParentEndpoint old hv hd) (R : CanonicalPair old hv hd left right)
    (side : Bool) (pMID pChild : Fin ((P).ambient c+1)→ℝ) where
  localTuple : ℕ→ℝ
  physical : PhysicalReadback old hv hd left right R side localTuple pMID pChild
  old_raw : ∀j,j<arity cs→localTuple j=FormulaSignSlotRadialProviderRetainedAppend.oldNatural old hv j
  paddingPoint : Fin ((P).ambient (preparedRoot old R.leftSpec R.rightSpec side)+1)→ℝ
  receipt : WordReceipt old hv hd left right R side localTuple paddingPoint

variable (left right : ParentEndpoint old hv hd)
local notation "a" => left.value V
local notation "b" => right.value V

theorem exists_sampled_level
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
      Nonempty (SampledLevel old hv hd left right R side pMID pChild) := by
  dsimp only
  obtain ⟨R,HR⟩ := exists_geometric_level old hv hd left right HL HR hab M fiber
  refine ⟨R,?_⟩
  intro side
  obtain ⟨u,hu,HN,hOld⟩ := HR side
  obtain ⟨p0,hp0,hg0⟩ := exists_padding_critical old hv R.leftSpec R.rightSpec side
  obtain ⟨W⟩ := exists_word_receipt old hv hd left right R side u hu p0 hp0 hg0
  exact ⟨⟨u,HN,hOld,p0,W⟩⟩

end LeanCanny.Encoding.FormulaSignSlotRadialProviderProperAppend
