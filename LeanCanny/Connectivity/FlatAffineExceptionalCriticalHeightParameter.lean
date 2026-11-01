/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FlatAffineExceptionalCriticalHeightRoot
/-! # The cleared parameter cut vanishes at each coarse critical height -/
@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineExceptionalCriticalHeightParameter
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation MvPolynomial
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineLastHeightRow (parentCone)
open FlatAffineExceptionalBankSource (births)
open FlatAffineExceptionalCoarseRule (state rule)
open IntegralMixedHistory
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
  (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u v a : List Bool) (hm : births F u ≤ S)
  (hh : h u ∈ FlatAffineExceptionalOrderedRule.frozen F u)
  (hv : FlatAffineCompleteVertices.Valid F (parentCone F C) u v)
  (φ : (state F C h S u (hm.trans (Nat.le_succ S))).sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
  (H : ∀ j, φ ((FlatAffineExceptionalParentBank.bank F C h S u (hm.trans (Nat.le_succ S))).bank.numerator j) /
    ((FlatAffineExceptionalParentBank.bank F C h S u (hm.trans (Nat.le_succ S))).bank.denominator j : ℝ) =
      FlatAffineExceptionalParentBank.values F C h u v a hv j)
  (hn : ∀ j i, FlatAffineFullSourceTower.direction F u (F.depth u) j.succ i = 2 * FermatCoordinateCone.normal j i)

include hh H hn in
theorem cut_root (t : ℝ) (y : Fin (arity F u) → ℝ)
    (hy : y ∈ FlatAffineShiftedSlice.slice F u (FlatAffineExceptionalSliceFrame.parent F C u v hv) (h u)
      (FlatAffineExceptionalSliceFrame.scalar F C h u a + t))
    (hg : ∀ i, i ∉ FlatAffineExceptionalOrderedRule.frozen F u →
      (pderiv i (BoundedFullCriticalSamples.polynomial F.source u)).eval₂ (Int.castRingHom ℝ) y = 0) :
    (FlatAffineExceptionalCriticalHeight.cut F C h S u hm).eval₂ φ.toRingHom t = 0 := by
  let Q := FlatAffineExceptionalParentBank.denominator F C h S u (hm.trans (Nat.le_succ S))
  let p := FlatAffineExceptionalCriticalHeight.relative F C h S u hm
  let D := criticalDegree (state F C h S u (hm.trans (Nat.le_succ S))) hm (rule F h u)
  let A := FlatAffineExceptionalParentBank.shiftedNumerator F C h S u (hm.trans (Nat.le_succ S)) (h u)
  have HQ : (Q : ℝ) ≠ 0 := Int.cast_ne_zero.mpr (FlatAffineExceptionalParentBank.denominator_ne_zero F C h S u _)
  have Hq : φ.toRingHom ((2*Q : ℤ) : (state F C h S u (hm.trans (Nat.le_succ S))).sampler.scalarPrefix.carrier) ≠ 0 := by
    rw [map_intCast]
    exact Int.cast_ne_zero.mpr (mul_ne_zero (by decide) (FlatAffineExceptionalParentBank.denominator_ne_zero F C h S u _))
  have HS := hy.2 (h u) hh
  rw [FlatAffineExceptionalSelectedSlice.normal_sum F u hn] at HS
  simp only [ite_true] at HS
  have HV := FlatAffineExceptionalParentBank.shiftedNumerator_eval F C h S u v a _ hv φ H (h u)
  simp only [ite_true] at HV
  have Hfrac : (φ.toRingHom A + φ.toRingHom (Q : (state F C h S u (hm.trans (Nat.le_succ S))).sampler.scalarPrefix.carrier)*t) /
      φ.toRingHom ((2*Q : ℤ) : (state F C h S u (hm.trans (Nat.le_succ S))).sampler.scalarPrefix.carrier) = y (h u) := by
    simp only [map_intCast, Int.cast_mul, Int.cast_ofNat, map_mul, map_ofNat]
    apply (div_eq_iff (by exact mul_ne_zero (by norm_num : (2:ℝ) ≠ 0) HQ)).mpr
    change φ A + (Q : ℝ)*t = y (h u) * ((2:ℝ)*(Q:ℝ))
    calc
      _ = (Q : ℝ) * ((FlatAffineFullSourceTower.level F u (F.depth u) (h u)).polynomial.eval₂ (Int.castRingHom ℝ)
        (FlatAffineExceptionalParentBank.ancestorValues F C u v hv) + FlatAffineExceptionalSliceFrame.scalar F C h u a) + (Q : ℝ)*t :=
          congrArg (fun value : ℝ => value+(Q:ℝ)*t) HV
      _ = (Q : ℝ) * ((FlatAffineFullSourceTower.level F u (F.depth u) (h u)).polynomial.eval₂ (Int.castRingHom ℝ)
        (FlatAffineExceptionalParentBank.ancestorValues F C u v hv) + (FlatAffineExceptionalSliceFrame.scalar F C h u a+t)) := by ring
      _ = (Q : ℝ) * (2*y (h u)) := congrArg ((Q : ℝ) * ·) (by simpa only [FlatAffineExceptionalParentBank.ancestorValues] using HS.symm)
      _ = y (h u) * ((2:ℝ)*(Q:ℝ)) := by ring
  have HR := FlatAffineExceptionalCriticalHeightRoot.relative_root F C h S u v a hm hv φ H hn t y hy hg
  have HE := ClearedAffinePolynomial.eval φ.toRingHom D p A
    (Q : (state F C h S u (hm.trans (Nat.le_succ S))).sampler.scalarPrefix.carrier)
    ((2*Q : ℤ) : (state F C h S u (hm.trans (Nat.le_succ S))).sampler.scalarPrefix.carrier)
    (IntegralMixedCriticalRoot.degree_le _ _ _) Hq t
  exact HE.trans (by rw [Hfrac,HR,mul_zero])

end LeanCanny.Connectivity.FlatAffineExceptionalCriticalHeightParameter
