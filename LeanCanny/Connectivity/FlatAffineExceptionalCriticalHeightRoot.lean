/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalCriticalHeight
public import LeanCanny.Algebra.IntegralMixedCoordinateRenameDerivative
public import LeanCanny.Connectivity.FlatAffineExceptionalSelectedSlice
/-! # The exact selected critical-height cut vanishes at full-slice singular candidates -/
@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineExceptionalCriticalHeightRoot
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation MvPolynomial
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineLastHeightRow (parentCone)
open FlatAffineExceptionalBankSource (births)
open FlatAffineExceptionalCoarseRule (frozen order state rule)
open IntegralMixedHistory
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem source_eval (F : Inputs) (h : (u : List Bool) → Fin (arity F u)) (u : List Bool) (y : Fin (arity F u) → ℝ) :
    (FermatCriticalHomogenization.polynomial
      (IntegralMixedCoordinateRename.spatial (FlatAffineExceptionalMixedHistory.spatialSource F u) (order F h u)).low
      (IntegralMixedCoordinateRename.spatial (FlatAffineExceptionalMixedHistory.spatialSource F u) (order F h u)).leading
      (IntegralMixedCoordinateRename.spatial (FlatAffineExceptionalMixedHistory.spatialSource F u) (order F h u)).degree).eval₂
      (Int.castRingHom ℝ) y = (BoundedFullCriticalSamples.polynomial F.source u).eval₂ (Int.castRingHom ℝ) (y ∘ (order F h u).symm) := by
  rw [IntegralMixedCoordinateRename.source_eval]
  exact congrArg (fun p : MvPolynomial (Fin (arity F u)) ℤ => p.eval₂ (Int.castRingHom ℝ) (y ∘ (order F h u).symm))
    (FlatAffinePowerPositive.source_eq F u).symm

theorem derivative_eval (F : Inputs) (h : (u : List Bool) → Fin (arity F u)) (u : List Bool)
    (i : Fin (arity F u)) (y : Fin (arity F u) → ℝ) :
    (pderiv i (FermatCriticalHomogenization.polynomial
      (IntegralMixedCoordinateRename.spatial (FlatAffineExceptionalMixedHistory.spatialSource F u) (order F h u)).low
      (IntegralMixedCoordinateRename.spatial (FlatAffineExceptionalMixedHistory.spatialSource F u) (order F h u)).leading
      (IntegralMixedCoordinateRename.spatial (FlatAffineExceptionalMixedHistory.spatialSource F u) (order F h u)).degree)).eval₂
      (Int.castRingHom ℝ) y = (pderiv (order F h u i) (BoundedFullCriticalSamples.polynomial F.source u)).eval₂
        (Int.castRingHom ℝ) (y ∘ (order F h u).symm) := by
  apply (IntegralMixedCoordinateRename.derivative_eval (FlatAffineExceptionalMixedHistory.spatialSource F u) (order F h u) i y).trans
  exact congrArg (fun p : MvPolynomial (Fin (arity F u)) ℤ => (pderiv (order F h u i) p).eval₂ (Int.castRingHom ℝ) (y ∘ (order F h u).symm))
    (FlatAffinePowerPositive.source_eq F u).symm

variable (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
  (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u v a : List Bool) (hm : births F u ≤ S)
  (hh : h u ∈ FlatAffineExceptionalOrderedRule.frozen F u)
  (hv : FlatAffineCompleteVertices.Valid F (parentCone F C) u v)
  (φ : (state F C h S u (hm.trans (Nat.le_succ S))).sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
  (H : ∀ j, φ ((FlatAffineExceptionalParentBank.bank F C h S u (hm.trans (Nat.le_succ S))).bank.numerator j) /
    ((FlatAffineExceptionalParentBank.bank F C h S u (hm.trans (Nat.le_succ S))).bank.denominator j : ℝ) =
      FlatAffineExceptionalParentBank.values F C h u v a hv j)
  (hn : ∀ j i, FlatAffineFullSourceTower.direction F u (F.depth u) j.succ i = 2 * FermatCoordinateCone.normal j i)

include H hn in
theorem relative_root (t : ℝ) (y : Fin (arity F u) → ℝ)
    (hy : y ∈ FlatAffineShiftedSlice.slice F u (FlatAffineExceptionalSliceFrame.parent F C u v hv) (h u)
      (FlatAffineExceptionalSliceFrame.scalar F C h u a + t))
    (hg : ∀ i, i ∉ FlatAffineExceptionalOrderedRule.frozen F u →
      (pderiv i (BoundedFullCriticalSamples.polynomial F.source u)).eval₂ (Int.castRingHom ℝ) y = 0) :
    (FlatAffineExceptionalCriticalHeight.relative F C h S u hm).eval₂ φ.toRingHom (y (h u)) = 0 := by
  let X := state F C h S u (hm.trans (Nat.le_succ S))
  let R := rule F h u
  have Hpoint : (y ∘ order F h u) ∘ (order F h u).symm = y := by
    funext i; simp only [Function.comp_apply, Equiv.apply_symm_apply]
  have HR := IntegralMixedCriticalRoot.root X hm R φ (y ∘ order F h u)
  have HF (i : Fin (arity F u)) (hi : i.val < R.offset.val) :
      ((data X hm R).scales i : ℝ) * (y ∘ order F h u) i = φ ((data X hm R).heights i) := by
    let j := order F h u i
    have HJ : j ∈ frozen F h u := (FrozenCoordinateOrdering.permutation_mem_iff (frozen F h u) i).mpr hi
    have HJs := Finset.mem_erase.mp HJ
    have HS := hy.2 j HJs.2
    rw [FlatAffineExceptionalSelectedSlice.normal_sum F u hn] at HS
    rw [ite_eq_right HJs.1, add_zero] at HS
    have HH := FlatAffineExceptionalParentBank.shiftedNumerator_eval F C h S u v a _ hv φ H j
    rw [ite_eq_right HJs.1, add_zero] at HH
    calc
      _ = ((2 * FlatAffineExceptionalParentBank.denominator F C h S u (hm.trans (Nat.le_succ S)) : ℤ) : ℝ) * y j :=
        congrArg (fun q : ℤ => (q : ℝ) * y j) (FlatAffineExceptionalCoarseRule.scale_eq F C h S u hm i)
      _ = (FlatAffineExceptionalParentBank.denominator F C h S u (hm.trans (Nat.le_succ S)) : ℝ) *
          (FlatAffineFullSourceTower.level F u (F.depth u) j).polynomial.eval₂ (Int.castRingHom ℝ)
            (FlatAffineExceptionalParentBank.ancestorValues F C u v hv) := by
        rw [Int.cast_mul, Int.cast_ofNat]
        rw [FlatAffineExceptionalParentBank.ancestorValues, ← HS]
        ring
      _ = φ (FlatAffineExceptionalParentBank.shiftedNumerator F C h S u (hm.trans (Nat.le_succ S)) j) := HH.symm
      _ = φ ((data X hm R).heights i) := (congrArg φ (FlatAffineExceptionalCoarseRule.height_eq F C h S u hm i)).symm
  have HP : (FermatCriticalHomogenization.polynomial
      (IntegralMixedCoordinateRename.spatial (FlatAffineExceptionalMixedHistory.spatialSource F u) (order F h u)).low
      (IntegralMixedCoordinateRename.spatial (FlatAffineExceptionalMixedHistory.spatialSource F u) (order F h u)).leading
      (IntegralMixedCoordinateRename.spatial (FlatAffineExceptionalMixedHistory.spatialSource F u) (order F h u)).degree).eval₂
      (Int.castRingHom ℝ) (y ∘ order F h u) = 0 := by
    exact (source_eval F h u (y ∘ order F h u)).trans
      ((congrArg (fun y => (BoundedFullCriticalSamples.polynomial F.source u).eval₂ (Int.castRingHom ℝ) y) Hpoint).trans hy.1)
  have HG (j : Fin (F.source.dim u+3-R.offset.val+1)) (hj : j ≠ IntegralMixedCriticalRoot.objective R) :
      (pderiv (ClearedCoordinateCritical.freeIndex R.offset.val (IntegralMixedCriticalRoot.fit R).le j)
        (FermatCriticalHomogenization.polynomial
          (IntegralMixedCoordinateRename.spatial (FlatAffineExceptionalMixedHistory.spatialSource F u) (order F h u)).low
          (IntegralMixedCoordinateRename.spatial (FlatAffineExceptionalMixedHistory.spatialSource F u) (order F h u)).leading
          (IntegralMixedCoordinateRename.spatial (FlatAffineExceptionalMixedHistory.spatialSource F u) (order F h u)).degree)).eval₂
        (Int.castRingHom ℝ) (y ∘ order F h u) = 0 := by
    let i := ClearedCoordinateCritical.freeIndex R.offset.val (IntegralMixedCriticalRoot.fit R).le j
    have HI : i.val ≥ (frozen F h u).card := by change (frozen F h u).card + j.val ≥ (frozen F h u).card; omega
    have HN : order F h u i ∉ frozen F h u := fun HI' => Nat.not_lt.mpr HI
      ((FrozenCoordinateOrdering.permutation_mem_iff (frozen F h u) i).mp HI')
    have HH : order F h u i ≠ h u := by
      intro HH
      have HE : i = (data X hm R).free := ((Equiv.eq_symm_apply _).mpr HH).trans (FlatAffineExceptionalCoarseRule.free_height F C h S u hm).symm
      apply hj
      apply Fin.ext
      have HV := congrArg Fin.val HE
      change R.offset.val+j.val = R.offset.val+(IntegralMixedCriticalRoot.objective R).val at HV
      omega
    have Hnot : order F h u i ∉ FlatAffineExceptionalOrderedRule.frozen F u := fun Hs => HN (Finset.mem_erase.mpr ⟨HH,Hs⟩)
    exact (derivative_eval F h u i (y ∘ order F h u)).trans
      ((congrArg (fun y => (pderiv (order F h u i) (BoundedFullCriticalSamples.polynomial F.source u)).eval₂ (Int.castRingHom ℝ) y) Hpoint).trans (hg _ Hnot))
  have HE : ClearedCoordinateCritical.freeIndex R.offset.val (IntegralMixedCriticalRoot.fit R).le
      (IntegralMixedCriticalRoot.coordinate R) = (order F h u).symm (h u) :=
    (show _ = (data X hm R).free from Fin.ext rfl).trans (FlatAffineExceptionalCoarseRule.free_height F C h S u hm)
  have Hroot := HR HF HP HG
  change (criticalPolynomial X hm R).eval₂ φ.toRingHom (y (h u)) = 0
  simpa only [HE, Function.comp_apply, Equiv.apply_symm_apply] using Hroot

end LeanCanny.Connectivity.FlatAffineExceptionalCriticalHeightRoot
