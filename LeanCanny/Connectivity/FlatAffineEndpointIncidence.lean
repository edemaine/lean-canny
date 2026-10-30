/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.FlatAffineEndpointMidpoint
public import LeanCanny.Connectivity.FiniteFiberMidpoint

/-! # Actual slab endpoint incidence from computed midpoint factors

Original cone exclusion gives finite endpoint fibers. The computed frozen
midpoint annihilators make matching stable on an adjacent retained interval,
so one sample decides whether an arc attaches to a given endpoint root.
Selecting and evaluating that sample natively remains separate.
-/

@[expose] public section
namespace LeanCanny.Connectivity.FlatAffineEndpointIncidence
open Set LeanCanny.Algebra LeanCanny.Encoding LeanCanny.Geometry
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open FlatAffineEndpointMidpoint (equation testPolynomial)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

theorem finite_fiber (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (r : List Bool) (a : ℝ) :
    Finite (FiniteFiberSlab.Fiber (equation F height r) a) := by
  let p := FlatAffinePowerPositive.system F (pairFst r)
  let c := fun i => if i = height (pairFst r) then (Polynomial.X : Polynomial ℤ) else 0
  have hf := AffineShiftCoordinates.finite_fiber p c (FlatAffinePowerPositive.degree F (pairFst r))
    (FlatAffinePowerPositive.polynomial_degree F (pairFst r)) (FlatAffinePowerPositive.degree_pos F (pairFst r))
    (FlatAffinePowerPositive.noInfinity F hcone (pairFst r)) a
  have H : {x | equation F height r a x}.Finite := by
    apply hf.subset
    intro x hx
    apply (AffineShiftCoordinates.roots_iff p c a x).mpr
    intro i
    have hi := hx i
    dsimp only [c]
    by_cases he : i = height (pairFst r)
    · simpa only [he, ite_true, SymbolicScaledSquarefree.scalarEvaluation,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X] using hi
    · simpa only [he, ite_false, SymbolicScaledSquarefree.scalarEvaluation,
        Polynomial.coe_eval₂RingHom, Polynomial.eval₂_zero] using hi
  exact H.to_subtype

theorem left_iff {J : Type*} [Finite J] (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (r : List Bool) (hr : FlatAffineEndpointValidity.Valid F height r)
    {a b : ℝ} (hab : a < b)
    (ha : SymbolicScaledSquarefree.scalarEvaluation a (FlatAffineHeightSlabExceptional.polynomial F height (pairFst r)) = 0)
    (curve : J → ℝ → Fin (count F (pairFst r)) → ℝ) (hc : ∀ j, ContinuousOn (curve j) (Icc a b))
    (hroot : ∀ j t, t ∈ Icc a b → equation F height r t (curve j t))
    (ht : ∀ i t, t ∈ Ioo a b → SymbolicScaledSquarefree.scalarEvaluation t (testPolynomial F height r i).trailingCoeff ≠ 0)
    (j : J) (x : FiniteFiberSlab.Fiber (equation F height r) a) (s : Ioo a b) :
    EndpointMidpoint.Matches {y | equation F height r a y} x.val (curve j s.val) ↔
      FiniteFiberSlab.Edge (equation F height r) curve a b (.inl j) (.inr (.inl x)) := by
  have : Finite (FiniteFiberSlab.Fiber (equation F height r) a) := finite_fiber F hcone height r a
  apply FiniteFiberSlab.left_midpoint_iff_of_stable (equation F height r) hab curve hc hroot j x s.val
  intro t ht'
  exact FlatAffineEndpointMidpoint.matches_iff F height r hr a ha (curve j) (hc j)
    (fun v hv => hroot j v (Ioo_subset_Icc_self hv)) x.val x.property ht ⟨t, ht'⟩ s

theorem right_iff {J : Type*} [Finite J] (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F)
    (height : (u : List Bool) → Fin (count F u)) (r : List Bool) (hr : FlatAffineEndpointValidity.Valid F height r)
    {a b : ℝ} (hab : a < b)
    (hb : SymbolicScaledSquarefree.scalarEvaluation b (FlatAffineHeightSlabExceptional.polynomial F height (pairFst r)) = 0)
    (curve : J → ℝ → Fin (count F (pairFst r)) → ℝ) (hc : ∀ j, ContinuousOn (curve j) (Icc a b))
    (hroot : ∀ j t, t ∈ Icc a b → equation F height r t (curve j t))
    (ht : ∀ i t, t ∈ Ioo a b → SymbolicScaledSquarefree.scalarEvaluation t (testPolynomial F height r i).trailingCoeff ≠ 0)
    (j : J) (x : FiniteFiberSlab.Fiber (equation F height r) b) (s : Ioo a b) :
    EndpointMidpoint.Matches {y | equation F height r b y} x.val (curve j s.val) ↔
      FiniteFiberSlab.Edge (equation F height r) curve a b (.inl j) (.inr (.inr x)) := by
  have : Finite (FiniteFiberSlab.Fiber (equation F height r) b) := finite_fiber F hcone height r b
  apply FiniteFiberSlab.right_midpoint_iff_of_stable (equation F height r) hab curve hc hroot j x s.val
  intro t ht'
  exact FlatAffineEndpointMidpoint.matches_iff F height r hr b hb (curve j) (hc j)
    (fun v hv => hroot j v (Ioo_subset_Icc_self hv)) x.val x.property ht ⟨t, ht'⟩ s

end LeanCanny.Connectivity.FlatAffineEndpointIncidence
