/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendConstruct
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendOwnPoint
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderEdge
/-! # Every accepted provider node extends by an actual equal-point identity edge -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
open LeanCanny.Algebra LeanCanny.Computation
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem identity_cast_point_heq {n m : ℕ} (h : n=m) (p : Fin (m+1)→ℝ) :
    HEq (fun i : Fin (n+1)=>p (Fin.cast (congrArg (·+1) h) i)) p := by cases h;rfl

private theorem identity_point_heq (q : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid q) :
    HEq (FormulaSignSlotRadialProviderIdentity.point q hv) (FormulaSignSlotRadialProviderAtomic.point q hv) := by
  unfold FormulaSignSlotRadialProviderIdentity.point
  exact identity_cast_point_heq (FormulaSignSlotRadialProviderAtomic.native_dimension q).symm _

attribute [local irreducible] FormulaSignSlotRadialProviderRecordPlan.parameters
  FormulaSignSlotRadialProviderRecordPlan.spatial FormulaSignSlotRadialProviderRecordPlan.source
  FormulaSignSlotRadialProviderAtomic.point FormulaSignSlotRadialProviderAtomic.Valid
  FormulaSignSlotRadialProviderIdentity.point

theorem identity_of_atomic_point_heq (a b : List Bool)
    (ha : FormulaSignSlotRadialProviderAtomic.Valid a) (hb : FormulaSignSlotRadialProviderAtomic.Valid b)
    (hc : FormulaSignSlotRadialProviderAtomic.provider a=FormulaSignSlotRadialProviderAtomic.provider b)
    (hp : HEq (FormulaSignSlotRadialProviderAtomic.point a ha) (FormulaSignSlotRadialProviderAtomic.point b hb)) :
    LeanCanny.pair a b∈FormulaSignSlotRadialProviderIdentity.language :=
  (FormulaSignSlotRadialProviderIdentity.language_iff a b ha hb hc).mpr
    ((identity_point_heq a ha).trans (hp.trans (identity_point_heq b hb).symm))

open FormulaSignSlotRadialProviderAtomic (dimension depth endBirth initial)

theorem exists_identity_child (old : List Bool) (hv : FormulaSignSlotRadialProviderAtomic.Valid old)
    (hd : depth old<dimension old) :
    ∃q,∃hq : FormulaSignSlotRadialProviderAtomic.Valid q,
      FormulaSignSlotRadialProviderAtomic.provider q=FormulaSignSlotRadialProviderAtomic.provider old ∧
      depth q=depth old+1 ∧
      HEq (FormulaSignSlotRadialProviderAtomic.point q hq) (FormulaSignSlotRadialProviderAtomic.point old hv) ∧
      LeanCanny.pair old q∈FormulaSignSlotRadialProviderIdentity.language ∧
      FormulaSignSlotRadialProviderEdge.Adjacent old q ∧
      ∀b < initial old+start old,FormulaSignSlotRadialProviderAtomic.field q hq b=
        FormulaSignSlotRadialProviderAtomic.field old hv b := by
  have HE := own_point_eligible old hv hd
  dsimp only at HE
  obtain ⟨q,hq,hprovider,hdepth,hpoint,hfields⟩ := exists_valid_at old hv hd
    (FormulaSignSlotRadialProviderAtomic.ownBirth old) (own_endpoint_fit old) (ownPoint old hv)
    HE.1 HE.2.1 HE.2.2
  have HP : HEq (FormulaSignSlotRadialProviderAtomic.point q hq) (FormulaSignSlotRadialProviderAtomic.point old hv) :=
    hpoint.trans (ownPoint_heq old hv)
  have HI := identity_of_atomic_point_heq old q hv hq hprovider.symm HP.symm
  exact ⟨q,hq,hprovider,hdepth,HP,HI,Or.inl HI,hfields⟩

end LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
