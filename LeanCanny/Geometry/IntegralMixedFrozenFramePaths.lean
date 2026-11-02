/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFrozenFrameRegularity
public import LeanCanny.Geometry.RegularFiberComponentPaths

/-! # The actual height cut gives paths in each full-fiber component -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra IntegralMixedHistory Set
open scoped Classical BigOperators
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

noncomputable def constraintMap (P : SpatialSource n) (F : Frame n) :
    (Fin (n+1)→ℝ)→Option F.frozen→ℝ := fun y j=>
  (FlatAffineCriticalExtremum.constraint (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)
    F.frozen (coordinateNormals F) j).eval₂ (Int.castRingHom ℝ) y

noncomputable def constraintTarget {k : ℕ} (F : Frame n) (values : Fin k→ℝ) (h : Fin (n+1)) (t : ℝ) :
    Option F.frozen→ℝ
  | none=>0
  | some j=>(F.heights j.val).evaluate values+if j.val=h then t else 0

theorem constraintMap_some (P : SpatialSource n) (F : Frame n) (y : Fin (n+1)→ℝ) (j : F.frozen) :
    constraintMap P F y (some j)=(F.scales j.val:ℝ)*y j.val := by
  change (AffineHeightPolynomial.polynomial (coordinateNormals F j.val.succ) id).eval₂ (Int.castRingHom ℝ) y=_
  rw [AffineHeightPolynomial.eval]
  simp [coordinateNormals]

theorem constraintMap_contDiff (P : SpatialSource n) (F : Frame n) : ContDiff ℝ ⊤ (constraintMap P F) :=
  contDiff_pi.mpr (fun j=>ProjectionCritical.contDiff_eval (Int.castRingHom ℝ)
    (FlatAffineCriticalExtremum.constraint (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)
      F.frozen (coordinateNormals F) j))

theorem constraintMap_derivative (P : SpatialSource n) (F : Frame n) (y : Fin (n+1)→ℝ) :
    fderiv ℝ (constraintMap P F) y=FlatAffineCriticalExtremum.derivative (Int.castRingHom ℝ)
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree) F.frozen (coordinateNormals F) y := by
  apply HasFDerivAt.fderiv
  exact hasFDerivAt_pi.mpr (fun j=>PolynomialCalculus.hasFDerivAt (Int.castRingHom ℝ)
    (FlatAffineCriticalExtremum.constraint (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)
      F.frozen (coordinateNormals F) j) y)

theorem shiftedSlice_eq_fiber {k : ℕ} (P : SpatialSource n) (F : Frame n) (values : Fin k→ℝ)
    (h : Fin (n+1)) (t : ℝ) :
    shiftedSlice P F values h t={y | constraintMap P F y=constraintTarget F values h t} := by
  ext y
  constructor
  · intro hy
    funext j
    cases j with
    | none=>exact hy.1
    | some j=>exact (constraintMap_some P F y j).trans (hy.2 j.val j.property)
  · intro hy
    refine ⟨congrFun hy none,?_⟩
    intro i hi
    exact (constraintMap_some P F y ⟨i,hi⟩).symm.trans (congrFun hy (some ⟨i,hi⟩))

theorem locallyPathConnected_of_heightCut (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F : Frame n) (h : Fin (n+1)) (hh : h∈F.frozen)
    (values : Fin m→ℝ) (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (t : ℝ) (ht : (heightCut x hm F h).eval₂ φ.toRingHom t≠0) :
    LocallyPathConnectedSpace (shiftedSlice P F values h t) := by
  have HE:=shiftedSlice_eq_fiber P F values h t
  let : LocallyPathConnectedSpace (RegularFiber.Fiber (constraintMap P F) (constraintTarget F values h t)) :=
    RegularFiber.locallyPathConnected (constraintMap P F) (constraintTarget F values h t)
      (fun _=>(constraintMap_contDiff P F).contDiffAt.of_le (by simp))
      (fun y=>by
        rw [constraintMap_derivative]
        exact regular_of_heightCut x hm φ F h hh values H t ht y.val (HE ▸ y.property))
  exact (Homeomorph.setCongr HE).symm.locallyPathConnectedSpace

theorem joinedIn_of_heightCut (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F : Frame n) (h : Fin (n+1)) (hh : h∈F.frozen)
    (values : Fin m→ℝ) (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (t : ℝ) (ht : (heightCut x hm F h).eval₂ φ.toRingHom t≠0)
    (y : Fin (n+1)→ℝ) (hy : y∈shiftedSlice P F values h t) (z : Fin (n+1)→ℝ)
    (hz : z∈connectedComponentIn (shiftedSlice P F values h t) y) :
    JoinedIn (shiftedSlice P F values h t) y z := by
  let : LocallyPathConnectedSpace (shiftedSlice P F values h t):=
    locallyPathConnected_of_heightCut x hm φ F h hh values H t ht
  exact RegularFiberComponentPaths.joinedIn_of_component _ y hy z hz

end LeanCanny.Geometry.IntegralMixedFrozenFrame
