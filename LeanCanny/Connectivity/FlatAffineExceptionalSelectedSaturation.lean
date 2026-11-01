/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FlatAffineExceptionalSelectedPaths
public import LeanCanny.Connectivity.FlatAffineRegularSectionSaturation
public import LeanCanny.Connectivity.FlatAffineTranslatedSections
/-! # Full exceptional-slice saturation from actual selected-parent critical sections -/
@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineExceptionalSelectedSaturation
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineLastHeightRow (parentCone)
open FlatAffineExceptionalBankSource (births)
open FlatAffineExceptionalOrderedRule (frozen order state rule sweep)
open FlatAffineExceptionalBankCorrelation (JointIndex MatchesFrame Correlated)
open FlatAffineExceptionalSelectedSlice (selectedSlice)
open FlatAffineShiftedSlice (projection)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
  (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u v a : List Bool) (hm : births F u ≤ S)
  (hh : h u ∈ frozen F u) (r : Fin (arity F u)) (hr : r ∉ frozen F u)
  (hv : FlatAffineCompleteVertices.Valid F (parentCone F C) u v)
  (z : JointIndex F u → ℝ) (HF : MatchesFrame F C h u v a hv z)
  (HG : Correlated F C h S u (hm.trans (Nat.le_succ S)) z)
  (φ : (state F C h S u (hm.trans (Nat.le_succ S))).sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
  (Hφ : ∀ i, φ ((FlatAffineExceptionalParentBank.bank F C h S u (hm.trans (Nat.le_succ S))).sampler.scalarPrefix.basis.generator i) =
    z (Sum.inl ((FlatAffineExceptionalParentBank.bank F C h S u (hm.trans (Nat.le_succ S))).sampler.scalar i)) ^
      UniformIntegralPowerSchedule.weights S (2 ^ FlatAffineExceptionalBankSource.width F u) (births F u) i)
  (hn : ∀ j i, FlatAffineFullSourceTower.direction F u (F.depth u) j.succ i = 2 * FermatCoordinateCone.normal j i)

include z HF HG Hφ hn in
theorem exists_interior_data
    (c : IntegralMixedRelativeCuts.Choices (state F C h S u (hm.trans (Nat.le_succ S))) hm (sweep F C h S u hm hh r hr) φ)
    (A B : ℝ) (t₀ : Ioo A B)
    (havoid : ∀ t ∈ Ioo A B, t ∉ FlatAffineExceptionalSelectedPaths.bad F C h S u hm hh r hr φ c) :
    Finite (IntegralMixedSelectedPhysicalFiber.physical (state F C h S u (hm.trans (Nat.le_succ S))) hm
      (sweep F C h S u hm hh r hr) φ t₀.val) ∧
    ∃ D : ComponentSlabCover.InteriorData (projection F u (FlatAffineExceptionalSliceFrame.parent F C u v hv) (h u))
      (FlatAffineExceptionalSliceFrame.scalar F C h u a+A) (FlatAffineExceptionalSliceFrame.scalar F C h u a+B)
      (IntegralMixedSelectedPhysicalFiber.physical (state F C h S u (hm.trans (Nat.le_succ S))) hm
        (sweep F C h S u hm hh r hr) φ t₀.val),
      (∀ j, IsClopen (D.piece j)) ∧
      (∀ j, (D.arc j (FlatAffineExceptionalSliceFrame.scalar F C h u a+t₀.val)).val = j.val ∘ (order F u).symm) ∧
      ∀ i j, ClosedPathCover.Overlap D.piece i j ↔
        JoinedIn (FlatAffineShiftedSlice.slice F u (FlatAffineExceptionalSliceFrame.parent F C u v hv) (h u)
          (FlatAffineExceptionalSliceFrame.scalar F C h u a+t₀.val))
          (D.arc i (FlatAffineExceptionalSliceFrame.scalar F C h u a+t₀.val)).val
          (D.arc j (FlatAffineExceptionalSliceFrame.scalar F C h u a+t₀.val)).val := by
  let α := FlatAffineExceptionalSliceFrame.scalar F C h u a
  obtain ⟨Hfin,curve,HA,HC,HR,HS⟩ := FlatAffineExceptionalSelectedPaths.exists_sections F C h S u v a hm hh r hr hv z HF HG φ Hφ hn c A B t₀ havoid
  let : Finite (IntegralMixedSelectedPhysicalFiber.physical (state F C h S u (hm.trans (Nat.le_succ S))) hm
    (sweep F C h S u hm hh r hr) φ t₀.val) := Hfin
  obtain ⟨arc,Hcont,Hlevel,Hvalue,Hsample⟩ := FlatAffineTranslatedSections.exists_lift F u
    (FlatAffineExceptionalSliceFrame.parent F C u v hv) (h u) hh α A B t₀ curve HC HR HS
  let anchor : Ioo (α+A) (α+B) := ⟨α+t₀.val,by constructor <;> linarith [t₀.property.1,t₀.property.2]⟩
  have HV := FlatAffineExceptionalBankCorrelation.recovery_of_correlated F C h S u v a (hm.trans (Nat.le_succ S)) hv z HF HG φ Hφ
  have Hregular := FlatAffineExceptionalSelectedRegularity.regular_on F C h S u v a hm hh hv φ HV hn A B
    (fun t ht HZ => havoid t ht (Or.inr HZ))
  obtain ⟨D,Hcl,HD,HE⟩ := FlatAffineRegularSectionSaturation.exists_interior_data F u
    (FlatAffineExceptionalSliceFrame.parent F C u v hv) (h u) hh (α+A) (α+B) anchor Hregular arc Hcont Hlevel Hsample
  refine ⟨Hfin,D,Hcl,?_,?_⟩
  · intro j
    calc
      _ = (arc j (α+t₀.val)).val := congrArg Subtype.val (HD j _)
      _ = curve j ((α+t₀.val)-α) := Hvalue j _ (Ioo_subset_Icc_self anchor.property)
      _ = j.val ∘ (order F u).symm := by rw [show (α+t₀.val)-α=t₀.val by ring,HA]
  · intro i j
    simpa only [HD] using HE i j

end LeanCanny.Connectivity.FlatAffineExceptionalSelectedSaturation
