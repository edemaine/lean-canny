/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FlatAffineExceptionalSelectedSweepCover
public import LeanCanny.Connectivity.FlatAffineExceptionalSelectedRealization
public import LeanCanny.Connectivity.FiniteCriticalSweepCuts
/-! # Valid exceptional frames admit a finite recursive sweep of the whole coarse slice

The correlated old hom, selected exceptional factors, all interior regularity
and the local slab covers are constructed. Recursive endpoint-fiber covers
are required only at the finitely many cuts. This theorem makes no claim
that the finite cut enumeration or those recursive covers are effective.
-/
@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineExceptionalRecursiveSweep
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineLastHeightRow (parentCone)
open FlatAffineExceptionalBankSource (births)
open FlatAffineExceptionalOrderedRule (frozen state sweep)
open FlatAffineShiftedSlice (projection coarseSlice)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem exists_sweep (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u v a : List Bool) (hm : births F u ≤ S)
    (hh : h u ∈ frozen F u) (r : Fin (arity F u)) (hr : r ∉ frozen F u)
    (hv : FlatAffineCompleteVertices.Valid F (parentCone F C) u v)
    (ha : SquareSampleCompleteVertices.Valid (IntegerPolynomialSampleInput.input (FlatAffineExceptionalSliceFrame.scalarSource F C h)) u a)
    (hn : ∀ j i, FlatAffineFullSourceTower.direction F u (F.depth u) j.succ i = 2 * FermatCoordinateCone.normal j i) :
    ∃ n : ℕ, ∃ cut : Fin (n+2) → ℝ, StrictMono cut ∧
      ∀ (E : Fin (n+2) → Type), (∀ j, Finite (E j)) →
        (∀ j, ClopenPathCover ((projection F u (FlatAffineExceptionalSliceFrame.parent F C u v hv) (h u)) ⁻¹'
          {FlatAffineExceptionalSliceFrame.scalar F C h u a+cut j}) (E j)) →
        ∃ I : Type, Finite I ∧ Nonempty (ClopenPathCover
          (coarseSlice F u (FlatAffineExceptionalSliceFrame.parent F C u v hv) (h u)) I) := by
  obtain ⟨z,φ,HF,HG,Hφ,_,_⟩ := FlatAffineExceptionalSelectedRealization.exists_correlated_slices
    F C h S u v a hm hh r hr hv ha hn
  obtain ⟨c⟩ := IntegralMixedRelativeCuts.exists_choices (state F C h S u (hm.trans (Nat.le_succ S))) hm
    (sweep F C h S u hm hh r hr) φ
  let α := FlatAffineExceptionalSliceFrame.scalar F C h u a
  let p := projection F u (FlatAffineExceptionalSliceFrame.parent F C u v hv) (h u)
  let : CompactSpace (coarseSlice F u (FlatAffineExceptionalSliceFrame.parent F C u v hv) (h u)) :=
    isCompact_iff_compactSpace.mp (FlatAffineShiftedSlice.coarse_compact F u _ (h u))
  have HP := (FlatAffineShiftedSlice.projection_proper F u (FlatAffineExceptionalSliceFrame.parent F C u v hv) (h u)).continuous
  obtain ⟨n,cut,HC,_,HB,HA⟩ := FiniteCriticalSweepCuts.exists_cuts (fun y => p y-α)
    (HP.sub continuous_const) (FlatAffineExceptionalSelectedPaths.bad F C h S u hm hh r hr φ c)
    (FlatAffineExceptionalSelectedPaths.finite_bad F C h S u hm hh r hr φ c)
  let seq : ℕ → ℝ := fun j => cut ⟨min j (n+1),by omega⟩
  have Hread (i : Fin (n+2)) : seq i.val = cut i := by
    apply congrArg cut
    apply Fin.ext
    dsimp [seq]
    have HI := i.isLt
    omega
  have HS : StrictMonoOn seq (Icc 0 (n+1)) := by
    intro i hi j hj hij
    apply HC
    change min i (n+1) < min j (n+1)
    have HI : i ≤ n+1 := hi.2
    have HJ : j ≤ n+1 := hj.2
    omega
  have HS0 : seq 0 = cut 0 := Hread 0
  have HSN : seq (n+1) = cut (Fin.last (n+1)) := Hread (Fin.last (n+1))
  have Havoid (i : Fin (n+1)) : ∀ t ∈ Ioo (seq i.val) (seq (i.val+1)),
      t ∉ FlatAffineExceptionalSelectedPaths.bad F C h S u hm hh r hr φ c := by
    have Hleft : seq i.val = cut i.castSucc := Hread i.castSucc
    have Hright : seq (i.val+1) = cut i.succ := Hread i.succ
    rw [Hleft,Hright]
    exact HA i
  have Hbound : ∀ y, p y ∈ Icc (α+seq 0) (α+seq (n+1)) := by
    intro y
    have HY := HB y
    rw [HS0,HSN]
    constructor <;> linarith [HY.1,HY.2]
  refine ⟨n,cut,HC,?_⟩
  intro E HE ends
  let : ∀ j, Finite (E j) := HE
  have Hends (j : Fin (n+2)) : ClopenPathCover (p ⁻¹' {α+seq j.val}) (E j) := by
    rw [Hread]
    exact ends j
  obtain ⟨HF,HD⟩ := FlatAffineExceptionalSelectedSweepCover.exists_component_cover
    F C h S u v a hm hh r hr hv z HF HG φ Hφ hn seq HS c Havoid E Hends Hbound
  exact ⟨_,HF,HD⟩

end LeanCanny.Connectivity.FlatAffineExceptionalRecursiveSweep
