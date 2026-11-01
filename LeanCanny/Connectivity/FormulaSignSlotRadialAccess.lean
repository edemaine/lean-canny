/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotComponentMaxima
public import LeanCanny.Connectivity.ClopenPathCover
public import LeanCanny.Geometry.RadialArcAccess
/-! # Actual positive radial branches give access in the same selected piece

One interior hit fixes the clopen component label along the entire branch.
The projected old tuple reaches the prescribed center, even when auxiliary
native witness coordinates do not have a uniquely chosen endpoint.
-/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialAccess
open Set LeanCanny.Encoding LeanCanny.Geometry
open FormulaSignSlotMarginProjection FormulaSignSlotComponentMaxima
open scoped Classical

noncomputable def projectedPiece (c : List Bool) (s : Set (Positive c)) :
    Set (Fin (FormulaSignSlotSource.dimension c) → ℝ) :=
  (fun y : Source c => (projection c y).val) '' ambient c s

theorem projectedPiece_selected (c : List Bool) (s : Set (Positive c))
    {x : Fin (FormulaSignSlotSource.dimension c) → ℝ} (hx : x∈projectedPiece c s) :
    (FormulaSignSlotSource.stratum c).Holds (ETR.Formula.extend x) := by
  obtain ⟨y,hy,rfl⟩ := hx
  exact (value_positive_iff c y).mp (ambient_positive c s hy)

theorem arc_label (c : List Bool) {I : Type*} (C : ClopenPathCover (Positive c) I) (i : I)
    (b : ℝ) (f : ℝ → Source c) (hf : ContinuousOn f (Ioo 0 b))
    (hp : ∀ t∈Ioo 0 b, 0 < value c (f t)) (a : ℝ) (ha : a∈Ioo 0 b)
    (hi : f a∈ambient c (C.piece i)) : ∀ t∈Ioo 0 b, f t∈ambient c (C.piece i) := by
  let G : Ioo (0 : ℝ) b → Positive c := fun t => ⟨f t,hp t t.property⟩
  have HG : Continuous G := hf.domRestrict.subtype_mk _
  let : PreconnectedSpace (Ioo (0 : ℝ) b) := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ioo
  have HA : G ⟨a,ha⟩∈C.piece i := by
    obtain ⟨z,hz,HZ⟩ := hi
    have HE : G ⟨a,ha⟩=z := Subtype.ext HZ.symm
    rw [HE]
    exact hz
  have HS := (isPreconnected_range HG).subset_isClopen (C.clopen i)
    ⟨G ⟨a,ha⟩,⟨⟨a,ha⟩,rfl⟩,HA⟩
  intro t ht
  exact ⟨G ⟨t,ht⟩,HS ⟨⟨t,ht⟩,rfl⟩,rfl⟩

theorem joined_center (c : List Bool) {I : Type*} (C : ClopenPathCover (Positive c) I) (i : I)
    (center : Fin (FormulaSignSlotSource.dimension c) → ℝ) (b : ℝ) (f : ℝ → Source c)
    (hf : ContinuousOn f (Ioo 0 b)) (hp : ∀ t∈Ioo 0 b, 0 < value c (f t))
    (hr : ∀ t∈Ioo 0 b, SquaredDistanceFibers.value center (projection c (f t)).val=t)
    (a : ℝ) (ha : a∈Ioo 0 b) (hi : f a∈ambient c (C.piece i)) :
    JoinedIn (insert center (projectedPiece c (C.piece i))) center (projection c (f a)).val := by
  apply RadialArcAccess.joined_center center b (fun t => (projection c (f t)).val)
    ((continuous_subtype_val.comp (proper_projection c).continuous).comp_continuousOn hf) hr
    (projectedPiece c (C.piece i)) _ a ha
  intro t ht
  exact ⟨f t,arc_label c C i b f hf hp a ha hi t ht,rfl⟩

theorem piece_paths (c : List Bool) {I : Type*} (C : ClopenPathCover (Positive c) I) (i : I)
    (x : Fin (FormulaSignSlotSource.dimension c) → ℝ) (hx : x∈projectedPiece c (C.piece i))
    (y : Fin (FormulaSignSlotSource.dimension c) → ℝ) (hy : y∈projectedPiece c (C.piece i)) :
    JoinedIn (projectedPiece c (C.piece i)) x y := by
  obtain ⟨z,⟨z',hz',HZ⟩,rfl⟩ := hx
  obtain ⟨w,⟨w',hw',HW⟩,rfl⟩ := hy
  subst z
  subst w
  have HC : Continuous (fun v : Positive c => (projection c v.val).val) :=
    continuous_subtype_val.comp ((proper_projection c).continuous.comp continuous_subtype_val)
  have HP := (C.paths i z' hz' w' hw').map HC.continuousOn
  apply HP.mono
  rintro v ⟨v',hv',rfl⟩
  exact ⟨v'.val,⟨v',hv',rfl⟩,rfl⟩

theorem joined_center_piece (c : List Bool) {I : Type*} (C : ClopenPathCover (Positive c) I) (i : I)
    (center : Fin (FormulaSignSlotSource.dimension c) → ℝ) (b : ℝ) (f : ℝ → Source c)
    (hf : ContinuousOn f (Ioo 0 b)) (hp : ∀ t∈Ioo 0 b, 0 < value c (f t))
    (hr : ∀ t∈Ioo 0 b, SquaredDistanceFibers.value center (projection c (f t)).val=t)
    (a : ℝ) (ha : a∈Ioo 0 b) (hi : f a∈ambient c (C.piece i))
    (y : Fin (FormulaSignSlotSource.dimension c) → ℝ) (hy : y∈projectedPiece c (C.piece i)) :
    JoinedIn (insert center (projectedPiece c (C.piece i))) center y := by
  have HA : (projection c (f a)).val∈projectedPiece c (C.piece i) := ⟨f a,hi,rfl⟩
  exact (joined_center c C i center b f hf hp hr a ha hi).trans
    ((piece_paths c C i _ HA y hy).mono (subset_insert _ _))

end LeanCanny.Connectivity.FormulaSignSlotRadialAccess
