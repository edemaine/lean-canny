/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialJointStratumLabels
public import LeanCanny.Encoding.FormulaSignSlotRadialExternalCoordinates
/-! # The external provider uses the same sampled stratum coordinates -/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialProviderStratumProjection
open LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry LeanCanny.Computation
open CoerciveComponentSampling
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem candidate_heq (I:SquareSampleInput.Inputs) (c d w z:List Bool)
    (hc:c=d) (hw:w=z) (hv:SquareSampleCompleteVertices.Valid I c w)
    (hd:SquareSampleCompleteVertices.Valid I d z):
    HEq (SquareSampleCompleteVertices.candidate I c w hv).val
      (SquareSampleCompleteVertices.candidate I d z hd).val:=by cases hc;cases hw;rfl

private theorem coordinate_heq {n m:ℕ} (hn:n=m) (p:Fin n→ℝ) (q:Fin m→ℝ)
    (he:HEq p q) (i:Fin n) (j:Fin m) (hi:i.val=j.val):p i=q j:=by
  cases hn
  cases eq_of_heq he
  exact congrArg p (Fin.ext hi)

noncomputable def projectedCoordinate (side:Bool) (c:List Bool)
    (x:FormulaSignSlotRadialJointStratumLabels.Space c)
    (i:Fin (FormulaSignSlotRadialJointLayout.circleCount side (FormulaSignSlotRadialJointStratum.header c))):ℝ:=
  (FormulaSignSlotRadialJointStratumLabels.project side c x).val i

theorem project_coordinate (side:Bool) (c:List Bool)
    (x:FormulaSignSlotRadialJointStratumLabels.Space c)
    (i:Fin (FormulaSignSlotRadialJointLayout.circleCount side (FormulaSignSlotRadialJointStratum.header c))):
    projectedCoordinate side c x i=
      x.val ⟨FormulaSignSlotRadialJointLayout.column (if side then 1 else 0) i.val,
        (FormulaSignSlotRadialJointComponentTransport.coordinate_lt side
          (FormulaSignSlotRadialJointStratum.header c) i).trans (Nat.lt_succ_self _)⟩:=
  FormulaSignSlotRadialJointComponentTransport.project_coordinate side
    (FormulaSignSlotRadialJointStratum.header c) (FormulaSignSlotRadialJointStratumLabels.corePoint c x) i

local notation "S"=>FormulaSignSlotRadialJointStratum.source
local notation "F"=>FormulaSignSlotRadialJointStratumSampler.input
variable (H:List Bool) (k:ℕ) (Gamma label:List Bool) (side:Bool) (w:List Bool)
local notation "c"=>FormulaSignSlotRadialJointStratum.packet H k
local notation "ctx"=>FormulaSignSlotRadialExternalContext.packet H k Gamma label side w

attribute [local irreducible] CanonicalAuxiliaryCandidateCover.dimension
  CanonicalAuxiliaryCandidateCover.equation FormulaSignSlotRadialJointCore.equation
  FormulaSignSlotRadialJointStratum.polynomial

theorem header_packet:FormulaSignSlotRadialJointStratum.header c=H:=pairFst_pair _ _

theorem arity_packet:(S).arity c=FormulaSignSlotRadialJointLayout.dimension H+1:=by
  simp only [FormulaSignSlotRadialJointStratum.source,FormulaSignSlotRadialJointStratum.arity,
    FormulaSignSlotRadialJointStratum.oldArity,header_packet]

theorem own_valid (hw:SquareSampleCompleteVertices.Valid F (pair c Gamma) w):
    FormulaSignSlotRadialExternalCoordinates.OwnValid ctx:=by
  simpa only [FormulaSignSlotRadialExternalCoordinates.OwnValid,
    FormulaSignSlotRadialExternalContext.gridContext_packet,FormulaSignSlotRadialExternalContext.ownWord_packet] using hw

def slotIndex (i:Fin (FormulaSignSlotRadialJointLayout.circleCount side H)):Fin ((S).arity c):=
  ⟨FormulaSignSlotRadialJointLayout.column (if side then 1 else 0) i.val,by
    rw [arity_packet]
    exact (FormulaSignSlotRadialJointComponentTransport.coordinate_lt side H i).trans (Nat.lt_succ_self _)⟩

theorem external_coordinate (hw:SquareSampleCompleteVertices.Valid F (pair c Gamma) w)
    (x:FormulaSignSlotRadialJointStratumLabels.Space c)
    (hx:HEq (SquareSampleCompleteVertices.candidate F (pair c Gamma) w hw).val x.val)
    (i:Fin (FormulaSignSlotRadialJointLayout.circleCount side H)):
    FormulaSignSlotRadialExternalCoordinates.point ctx (own_valid H k Gamma label side w hw) i.val=
      x.val (slotIndex H k side i):=by
  have HC:FormulaSignSlotRadialExternalContext.gridContext ctx=pair c Gamma:=
    FormulaSignSlotRadialExternalContext.gridContext_packet H k Gamma label side w
  have HW:FormulaSignSlotRadialExternalContext.ownWord ctx=w:=
    FormulaSignSlotRadialExternalContext.ownWord_packet H k Gamma label side w
  have HE:=(candidate_heq F _ _ _ _ HC HW (own_valid H k Gamma label side w hw) hw).trans hx
  have HN:(F).count (FormulaSignSlotRadialExternalContext.gridContext ctx)=(S).arity c:=by
    rw [HC,FormulaSignSlotRadialExternalCoordinates.count_packet H k Gamma,arity_packet]
  change (SquareSampleCompleteVertices.candidate F _ _ _).val _=_
  exact coordinate_heq HN _ _ HE _ _ (FormulaSignSlotRadialExternalCoordinates.index_packet_val H k Gamma label side w i)

theorem external_project_coordinate (hw:SquareSampleCompleteVertices.Valid F (pair c Gamma) w)
    (x:FormulaSignSlotRadialJointStratumLabels.Space c)
    (hx:HEq (SquareSampleCompleteVertices.candidate F (pair c Gamma) w hw).val x.val)
    (i:Fin (FormulaSignSlotRadialJointLayout.circleCount side H)):
    FormulaSignSlotRadialExternalCoordinates.point ctx (own_valid H k Gamma label side w hw) i.val=
      projectedCoordinate side c x
        (Fin.cast (congrArg (FormulaSignSlotRadialJointLayout.circleCount side) (header_packet H k)).symm i):=by
  rw [external_coordinate H k Gamma label side w hw x hx i,project_coordinate]
  apply congrArg x.val
  apply Fin.ext
  rfl

end LeanCanny.Connectivity.FormulaSignSlotRadialProviderStratumProjection
