/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalOrderedRule
public import LeanCanny.Encoding.FlatAffineExceptionalBankCorrelation
public import LeanCanny.Connectivity.IntegralMixedSelectedCoordinateStatus
public import LeanCanny.Connectivity.FlatAffineExceptionalSliceRepresentation
/-! # Correlated exceptional frames are the exact selected mixed frozen slices

An explicit coordinate permutation orders an arbitrary frozen subset.
The old bank, its homomorphism and the parent/scalar labels remain fixed.
The sweep parameter adds to the represented scalar, including at zero.
-/
@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineExceptionalSelectedSlice
open Set LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open FlatAffineLastHeightRow (parentCone)
open FlatAffineExceptionalBankSource (births)
open FlatAffineExceptionalOrderedRule (frozen order state rule sweep)
open FlatAffineExceptionalBankCorrelation (JointIndex MatchesFrame Correlated)
open IntegralMixedHistory IntegralMixedCriticalSweep
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

noncomputable def spatial (F : Inputs) (u : List Bool) :=
  IntegralMixedCoordinateRename.spatial (FlatAffineExceptionalMixedHistory.spatialSource F u) (order F u)

noncomputable def source (F : Inputs) (u : List Bool) :=
  FermatCriticalHomogenization.polynomial (spatial F u).low (spatial F u).leading (spatial F u).degree

theorem source_eval (F : Inputs) (u : List Bool) (y : Fin (arity F u) → ℝ) :
    (source F u).eval₂ (Int.castRingHom ℝ) y =
      (BoundedFullCriticalSamples.polynomial F.source u).eval₂ (Int.castRingHom ℝ) (y ∘ (order F u).symm) := by
  rw [source, spatial, IntegralMixedCoordinateRename.source_eval]
  exact congrArg (fun p : MvPolynomial (Fin (arity F u)) ℤ => p.eval₂ (Int.castRingHom ℝ) (y ∘ (order F u).symm))
    (FlatAffinePowerPositive.source_eq F u).symm

noncomputable def selectedSlice (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u : List Bool) (hm : births F u ≤ S)
    (hh : h u ∈ frozen F u) (r : Fin (arity F u)) (hr : r ∉ frozen F u)
    (φ : (state F C h S u (hm.trans (Nat.le_succ S))).sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (t : ℝ) : Set (Fin (arity F u) → ℝ) :=
  {y | (source F u).eval₂ (Int.castRingHom ℝ) y = 0 ∧ ∀ i, i.val < (frozen F u).card →
    ((data (state F C h S u (hm.trans (Nat.le_succ S))) hm (rule F h u r hr)).scales i : ℝ) * y i =
      heightValue (state F C h S u (hm.trans (Nat.le_succ S))) (sweep F C h S u hm hh r hr) φ t i}

theorem height_eval_of_values (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u v a : List Bool) (hm : births F u ≤ S)
    (hh : h u ∈ frozen F u) (r : Fin (arity F u)) (hr : r ∉ frozen F u)
    (hv : FlatAffineCompleteVertices.Valid F (parentCone F C) u v)
    (φ : (state F C h S u (hm.trans (Nat.le_succ S))).sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (H : ∀ j, φ ((FlatAffineExceptionalParentBank.bank F C h S u (hm.trans (Nat.le_succ S))).bank.numerator j) /
      ((FlatAffineExceptionalParentBank.bank F C h S u (hm.trans (Nat.le_succ S))).bank.denominator j : ℝ) =
        FlatAffineExceptionalParentBank.values F C h u v a hv j) (t : ℝ) (i : Fin (arity F u)) :
    heightValue (state F C h S u (hm.trans (Nat.le_succ S))) (sweep F C h S u hm hh r hr) φ t i =
      (FlatAffineExceptionalParentBank.denominator F C h S u (hm.trans (Nat.le_succ S)) : ℝ) *
        ((FlatAffineFullSourceTower.level F u (F.depth u) (order F u i)).polynomial.eval₂ (Int.castRingHom ℝ)
          (FlatAffineExceptionalParentBank.ancestorValues F C u v hv) +
            if order F u i = h u then FlatAffineExceptionalSliceFrame.scalar F C h u a + t else 0) := by
  unfold heightValue
  rw [show expression (state F C h S u (hm.trans (Nat.le_succ S)))
      ((sweep F C h S u hm hh r hr).critical.heights i) = _ from
        FlatAffineExceptionalOrderedRule.rule_height F C h S u hm r hr i]
  have HV := FlatAffineExceptionalParentBank.shiftedNumerator_eval F C h S u v a _ hv φ H (order F u i)
  apply (congrArg (fun value : ℝ => value + if i = (sweep F C h S u hm hh r hr).height then
    ((sweep F C h S u hm hh r hr).slope : ℝ) * t else 0) HV).trans
  by_cases hi : order F u i = h u
  · have HE : i = (order F u).symm (h u) := (Equiv.eq_symm_apply _).mpr hi
    simp only [sweep, HE, Equiv.apply_symm_apply, ite_true]
    ring
  · have HE : i ≠ (order F u).symm (h u) := fun HE => hi ((Equiv.eq_symm_apply _).mp HE)
    simp only [sweep, hi, HE, ite_false, add_zero]

theorem normal_sum (F : Inputs) (u : List Bool)
    (hn : ∀ j i, FlatAffineFullSourceTower.direction F u (F.depth u) j.succ i = 2 * FermatCoordinateCone.normal j i)
    (y : Fin (arity F u) → ℝ) (j : Fin (arity F u)) :
    (∑ i, (FlatAffineFullSourceTower.direction F u (F.depth u) j.succ i : ℝ) * y i) = 2 * y j := by
  simp [hn, FermatCoordinateCone.normal]

theorem equation_iff (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u v a : List Bool) (hm : births F u ≤ S)
    (hh : h u ∈ frozen F u) (r : Fin (arity F u)) (hr : r ∉ frozen F u)
    (hv : FlatAffineCompleteVertices.Valid F (parentCone F C) u v)
    (φ : (state F C h S u (hm.trans (Nat.le_succ S))).sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (H : ∀ j, φ ((FlatAffineExceptionalParentBank.bank F C h S u (hm.trans (Nat.le_succ S))).bank.numerator j) /
      ((FlatAffineExceptionalParentBank.bank F C h S u (hm.trans (Nat.le_succ S))).bank.denominator j : ℝ) =
        FlatAffineExceptionalParentBank.values F C h u v a hv j) (t : ℝ) (y : Fin (arity F u) → ℝ) (i : Fin (arity F u)) :
    ((data (state F C h S u (hm.trans (Nat.le_succ S))) hm (rule F h u r hr)).scales i : ℝ) * y i =
        heightValue (state F C h S u (hm.trans (Nat.le_succ S))) (sweep F C h S u hm hh r hr) φ t i ↔
      2 * y i = (FlatAffineFullSourceTower.level F u (F.depth u) (order F u i)).polynomial.eval₂ (Int.castRingHom ℝ)
          (FlatAffineExceptionalParentBank.ancestorValues F C u v hv) +
            if order F u i = h u then FlatAffineExceptionalSliceFrame.scalar F C h u a + t else 0 := by
  rw [FlatAffineExceptionalOrderedRule.rule_scale, height_eval_of_values F C h S u v a hm hh r hr hv φ H t i]
  rw [Int.cast_mul, Int.cast_ofNat]
  rw [show (2 * (FlatAffineExceptionalParentBank.denominator F C h S u (hm.trans (Nat.le_succ S)) : ℝ)) * y i =
    (FlatAffineExceptionalParentBank.denominator F C h S u (hm.trans (Nat.le_succ S)) : ℝ) * (2 * y i) by ring]
  exact mul_right_inj' (show (FlatAffineExceptionalParentBank.denominator F C h S u (hm.trans (Nat.le_succ S)) : ℝ) ≠ 0 from
    Int.cast_ne_zero.mpr (FlatAffineExceptionalParentBank.denominator_ne_zero F C h S u _))

theorem slice_iff_of_values (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
    (h : (u : List Bool) → Fin (arity F u)) (S : ℕ) (u v a : List Bool) (hm : births F u ≤ S)
    (hh : h u ∈ frozen F u) (r : Fin (arity F u)) (hr : r ∉ frozen F u)
    (hv : FlatAffineCompleteVertices.Valid F (parentCone F C) u v)
    (φ : (state F C h S u (hm.trans (Nat.le_succ S))).sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (H : ∀ j, φ ((FlatAffineExceptionalParentBank.bank F C h S u (hm.trans (Nat.le_succ S))).bank.numerator j) /
      ((FlatAffineExceptionalParentBank.bank F C h S u (hm.trans (Nat.le_succ S))).bank.denominator j : ℝ) =
        FlatAffineExceptionalParentBank.values F C h u v a hv j)
    (hn : ∀ j i, FlatAffineFullSourceTower.direction F u (F.depth u) j.succ i = 2 * FermatCoordinateCone.normal j i)
    (t : ℝ) (y : Fin (arity F u) → ℝ) :
    y ∈ selectedSlice F C h S u hm hh r hr φ t ↔
      (y ∘ (order F u).symm) ∈ FlatAffineShiftedSlice.slice F u (FlatAffineExceptionalSliceFrame.parent F C u v hv)
        (h u) (FlatAffineExceptionalSliceFrame.scalar F C h u a + t) := by
  change (_ = 0 ∧ _) ↔ (_ = 0 ∧ _)
  rw [source_eval]
  apply and_congr_right
  intro _
  constructor
  · intro HY j hj
    have HI := (FlatAffineExceptionalOrderedRule.inverse_frozen F u j).mpr hj
    have HE := (equation_iff F C h S u v a hm hh r hr hv φ H t y ((order F u).symm j)).mp (HY _ HI)
    rw [normal_sum F u hn]
    simpa only [Function.comp_apply, Equiv.apply_symm_apply, FlatAffineExceptionalParentBank.ancestorValues] using HE
  · intro HY i hi
    apply (equation_iff F C h S u v a hm hh r hr hv φ H t y i).mpr
    have HE := HY (order F u i) ((FlatAffineExceptionalOrderedRule.ordered_frozen F u i).mpr hi)
    rw [normal_sum F u hn] at HE
    simpa only [Function.comp_apply, Equiv.symm_apply_apply, FlatAffineExceptionalParentBank.ancestorValues] using HE

theorem slice_iff_correlated (F : Inputs) (C : FlatAffinePowerPositive.ConeCertificate (next F))
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
    (t : ℝ) (y : Fin (arity F u) → ℝ) :
    y ∈ selectedSlice F C h S u hm hh r hr φ t ↔
      (y ∘ (order F u).symm) ∈ FlatAffineShiftedSlice.slice F u (FlatAffineExceptionalSliceFrame.parent F C u v hv)
        (h u) (FlatAffineExceptionalSliceFrame.scalar F C h u a + t) :=
  slice_iff_of_values F C h S u v a hm hh r hr hv φ
    (FlatAffineExceptionalBankCorrelation.recovery_of_correlated F C h S u v a _ hv z HF HG φ Hφ) hn t y

end LeanCanny.Connectivity.FlatAffineExceptionalSelectedSlice
