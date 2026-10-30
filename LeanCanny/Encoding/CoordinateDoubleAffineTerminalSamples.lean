/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.ScaledCoordinateTerminalCritical
public import LeanCanny.Encoding.CoordinateDoubleAffineSliceRegularity
public import Mathlib.Topology.Connected.TotallyDisconnected

/-! # Complete point sampling at a terminal coordinate slice

When the selected objective is the last coordinate, the prefix fixes every
other coordinate. Every feasible point has a critical lift, including multiple
source roots. The complete next-stage cone bound therefore bounds all points
of this slice, rather than only its connected components.
-/

@[expose] public section
namespace LeanCanny.Encoding.CoordinateDoubleAffineTerminalSamples
open Set LeanCanny.Algebra LeanCanny.Geometry
open CoordinateDoubleAffinePrefix (inputs)
open FlatAffineFullSourceTower (stage arity)
open FlatAffineCompleteRootStages (next newest)
open FlatAffineCompleteComponentSamples (source active direction levels ancestors slice)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

def pivot (P : BoundedFullWriter.Readers) (u : List Bool) : Fin (P.dim u + 4) := ⟨P.dim u + 3, by omega⟩

lemma selected_eq (P : BoundedFullWriter.Readers) (objective : List Bool → ℕ) (u : List Bool) (k : ℕ)
    (hmax : P.dim u + 3 ≤ objective (stage u k)) : CoordinateAffineTower.selected P objective u k = pivot P u :=
  Fin.ext (Nat.min_eq_right hmax)

lemma active_eq (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) (k : ℕ)
    (hmax : P.dim u + 3 ≤ objective (stage u k)) :
    FlatAffineFullSourceTower.free (inputs P depth objective level) u k = Finset.univ.erase (pivot P u) := by
  ext j
  rw [CoordinateDoubleAffinePrefix.active_iff, selected_eq P objective u k hmax]
  simp only [Finset.mem_erase, Finset.mem_univ, and_true]
  change j.val < P.dim u + 3 ↔ j ≠ pivot P u
  constructor
  · intro H HE
    have HV := congrArg Fin.val HE
    change j.val = P.dim u + 3 at HV
    omega
  · intro H
    by_contra HL
    change ¬j.val < P.dim u + 3 at HL
    apply H
    apply Fin.ext
    have HJ := j.isLt
    change j.val < P.dim u + 4 at HJ
    change j.val = P.dim u + 3
    omega

lemma direction_eq (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool) (k : ℕ)
    (hmax : P.dim u + 3 ≤ objective (stage u k)) :
    FlatAffineFullSourceTower.direction (inputs P depth objective level) u k = ScaledCoordinateTerminalCritical.table 2 (pivot P u) := by
  funext m i
  refine Fin.cases ?_ (fun j => ?_) m
  · have H := CoordinateDoubleAffinePrefix.objective P depth objective level u k i
    rw [selected_eq P objective u k hmax] at H
    exact H
  · exact CoordinateDoubleAffinePrefix.normal P depth objective level u k j i

theorem exists_label (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool)
    (x : FlatAffinePowerSampleInput.OriginalRoots (inputs P depth objective level) u)
    (hmax : P.dim u + 3 ≤ objective (stage u (depth u)))
    (z : Fin (P.dim u + 4) → ℝ) (hz : z ∈ slice (inputs P depth objective level) u x) :
    ∃ w : {w : List Bool // FlatAffineCompleteVertices.Valid (next (inputs P depth objective level))
      (CoordinateDoubleAffineSliceRegularity.cone P depth objective level) u w},
      FlatAffineCompleteRootStages.project (next (inputs P depth objective level)) depth u (Nat.le_succ _)
        (FlatAffineCompleteVertices.vertexEquiv (next (inputs P depth objective level))
          (CoordinateDoubleAffineSliceRegularity.cone P depth objective level) u w) = x ∧
      newest (inputs P depth objective level) u (FlatAffineCompleteVertices.vertexEquiv (next (inputs P depth objective level))
        (CoordinateDoubleAffineSliceRegularity.cone P depth objective level) u w).val ∘ Sum.inl = z := by
  let F := inputs P depth objective level
  have HA : active F u = Finset.univ.erase (pivot P u) := active_eq P depth objective level u (depth u) hmax
  have HT : direction F u = ScaledCoordinateTerminalCritical.table 2 (pivot P u) := direction_eq P depth objective level u (depth u) hmax
  have HL : ∀ j ∈ Finset.univ.erase (pivot P u),
      ∑ i, (ScaledCoordinateTerminalCritical.table 2 (pivot P u) j.succ i : ℝ) * z i =
        (levels F u j).eval₂ (Int.castRingHom ℝ) (ancestors F u x.val) := by
    intro j hj
    have H := hz.2 j (HA.symm ▸ hj)
    change (∑ i, (direction F u j.succ i : ℝ) * z i) =
      (levels F u j).eval₂ (Int.castRingHom ℝ) (ancestors F u x.val) at H
    rw [HT] at H
    exact H
  have HR := ScaledCoordinateTerminalCritical.exists_root 2 (by decide) (source F u) (pivot P u) (levels F u) (ancestors F u x.val) z hz.1 HL
  rw [← HA, ← HT] at HR
  let root := FlatAffineCompleteRootStages.extend F u x
    (Sum.elim z (ScaledCoordinateTerminalCritical.multipliers 2 (source F u) (pivot P u) z)) HR
  let cone := CoordinateDoubleAffineSliceRegularity.cone P depth objective level
  let w := (FlatAffineCompleteVertices.vertexEquiv (next F) cone u).symm root
  have HW : FlatAffineCompleteVertices.vertexEquiv (next F) cone u w = root := Equiv.apply_symm_apply _ _
  refine ⟨w, ?_, ?_⟩
  · rw [HW]
    exact FlatAffineCompleteRootStages.extend_prefix F u x _ HR
  · rw [HW, FlatAffineCompleteRootStages.extend_newest]
    rfl

theorem finite_card_le (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool)
    (x : FlatAffinePowerSampleInput.OriginalRoots (inputs P depth objective level) u)
    (hmax : P.dim u + 3 ≤ objective (stage u (depth u))) :
    Finite (slice (inputs P depth objective level) u x) ∧
      Nat.card (slice (inputs P depth objective level) u x) ≤
        FlatAffinePowerSampleInput.originalCountBound (next (inputs P depth objective level)) u := by
  let F := inputs P depth objective level
  let cone := CoordinateDoubleAffineSliceRegularity.cone P depth objective level
  let I := FlatAffinePowerSampleInput.input (next F) cone
  let : Finite (SquareSampleComplete.Roots I u) :=
    (SquareSampleComplete.finite_roots I (FlatAffinePowerSampleInput.complete (next F) cone) u).1
  let : Finite (FlatAffinePowerSampleInput.OriginalRoots (next F) u) :=
    Finite.of_equiv (SquareSampleComplete.Roots I u) (FlatAffinePowerSampleInput.originalRootsEquiv (next F) u)
  let f : slice F u x → FlatAffinePowerSampleInput.OriginalRoots (next F) u := fun z =>
    FlatAffineCompleteVertices.vertexEquiv (next F) cone u (Classical.choose (exists_label P depth objective level u x hmax z.val z.property))
  have HF (z : slice F u x) : newest F u (f z).val ∘ Sum.inl = z.val :=
    (Classical.choose_spec (exists_label P depth objective level u x hmax z.val z.property)).2
  have HI : Function.Injective f := by
    intro z y H
    apply Subtype.ext
    exact (HF z).symm.trans ((congrArg (fun r : FlatAffinePowerSampleInput.OriginalRoots (next F) u => newest F u r.val ∘ Sum.inl) H).trans (HF y))
  exact ⟨Finite.of_injective f HI, (Nat.card_le_card_of_injective f HI).trans (FlatAffinePowerSampleInput.originalCount_le (next F) cone u)⟩

theorem component_iff_eq (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool)
    (x : FlatAffinePowerSampleInput.OriginalRoots (inputs P depth objective level) u)
    (hmax : P.dim u + 3 ≤ objective (stage u (depth u)))
    (z y : Fin (P.dim u + 4) → ℝ) (hz : z ∈ slice (inputs P depth objective level) u x) :
    y ∈ connectedComponentIn (slice (inputs P depth objective level) u x) z ↔ y = z := by
  let S := slice (inputs P depth objective level) u x
  let : Finite S := (finite_card_le P depth objective level u x hmax).1
  let : TotallyDisconnectedSpace S := inferInstance
  constructor
  · intro H
    rw [connectedComponentIn_eq_image hz] at H
    obtain ⟨p, hp, he⟩ := H
    have HC : (connectedComponent (⟨z, hz⟩ : S)).Subsingleton := isPreconnected_connectedComponent.subsingleton
    have HP := HC hp mem_connectedComponent
    exact he.symm.trans (congrArg Subtype.val HP)
  · rintro rfl
    exact mem_connectedComponentIn hz

theorem joined_iff_eq (P : BoundedFullWriter.Readers) (depth objective : List Bool → ℕ)
    (level : List Bool → List Bool) (u : List Bool)
    (x : FlatAffinePowerSampleInput.OriginalRoots (inputs P depth objective level) u)
    (hmax : P.dim u + 3 ≤ objective (stage u (depth u)))
    (z y : Fin (P.dim u + 4) → ℝ) (hz : z ∈ slice (inputs P depth objective level) u x) :
    JoinedIn (slice (inputs P depth objective level) u x) z y ↔ y = z := by
  constructor
  · rintro ⟨path, hp⟩
    apply (component_iff_eq P depth objective level u x hmax z y hz).mp
    have HS : range path ⊆ slice (inputs P depth objective level) u x := by
      rintro t ⟨s, rfl⟩
      exact hp s
    exact (isPreconnected_range path.continuous).subset_connectedComponentIn path.source_mem_range HS path.target_mem_range
  · rintro rfl
    exact JoinedIn.refl hz

end LeanCanny.Encoding.CoordinateDoubleAffineTerminalSamples
