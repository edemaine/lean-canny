/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.BoundedGateWitnessSpace
/-! # The actual native polynomial zero set is the bounded witness space -/
@[expose] public section
namespace LeanCanny.Connectivity.BoundedGateCoordinates
open ETR Set LeanCanny.Encoding LeanCanny.Geometry
open MonotoneGateSource MonotoneGateGraph
open scoped Classical
set_option backward.isDefEq.respectTransparency false

abbrev NativeZero (F : Family) (c : List Bool) :=
  (BoundedMonotoneGateSource.description F c).realization

noncomputable abbrev RawTight (F : Family) (c : List Bool) :=
  {z : (Fin (total F c) → ℝ) × (Fin (F.count c) → CircularWitness.Plane) //
    (MonotoneGateSource.polynomial F c).eval (Formula.extend z.1)=0 ∧
    ∀ i < F.count c, (BoundedMonotoneGateSource.slack F (BoundedMonotoneGateSource.query c i)).eval
      (Formula.extend (encode F c z))=0}

noncomputable def rawHomeomorph (F : Family) (c : List Bool)
    (ha : ∀ i < F.count c, (F.atom (BoundedMonotoneGateSource.query c i)).arity≤F.dimension c) :
    RawTight F c ≃ₜ NativeZero F c :=
  (FiniteCircularCoordinates.homeomorph (total F c) (F.count c)).subtype (fun z => by
    change (_ ∧ _) ↔ (BoundedMonotoneGateSource.polynomial F c).eval (Formula.extend (encode F c z))=0
    rw [BoundedMonotoneGateSource.polynomial_zero]
    rw [old_eval F c z _ ((MonotoneGateSource.polynomial_arity F c ha).trans (by
      dsimp [MonotoneGateSource.outputDimension,total,base]; omega))])

noncomputable def packHomeomorph (F : Family) (c : List Bool)
    (ha : ∀ i < F.count c, (F.atom (BoundedMonotoneGateSource.query c i)).arity≤F.dimension c)
    (hk : ∀ q, F.kind q≠3) : RawTight F c ≃ₜ TightSpace F c ha hk where
  toFun z := ⟨(⟨z.val.1,z.property.1⟩,z.val.2),fun i => by
    have H := z.property.2 i.val i.isLt
    rw [slack_eval F c ha hk ⟨z.val.1,z.property.1⟩ z.val.2 i] at H
    exact sub_eq_zero.mp H⟩
  invFun z := ⟨(z.val.1.val,z.val.2),⟨z.val.1.property,fun i hi => by
    rw [slack_eval F c ha hk z.val.1 z.val.2 ⟨i,hi⟩]
    exact sub_eq_zero.mpr (z.property ⟨i,hi⟩)⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    (((continuous_fst.comp continuous_subtype_val).subtype_mk _).prodMk
      (continuous_snd.comp continuous_subtype_val)).subtype_mk _
  continuous_invFun :=
    ((continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)).prodMk
      (continuous_snd.comp continuous_subtype_val)).subtype_mk _

noncomputable def zeroWitnessHomeomorph (F : Family) (c : List Bool)
    (ha : ∀ i < F.count c, (F.atom (BoundedMonotoneGateSource.query c i)).arity≤F.dimension c)
    (hk : ∀ q, F.kind q≠3) : NativeZero F c ≃ₜ Witness F c :=
  (rawHomeomorph F c ha).symm.trans ((packHomeomorph F c ha hk).trans (witnessHomeomorph F c ha hk))

end LeanCanny.Connectivity.BoundedGateCoordinates
