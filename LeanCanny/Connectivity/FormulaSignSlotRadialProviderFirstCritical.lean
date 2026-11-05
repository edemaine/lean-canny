/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderMarkedGeometry
public import LeanCanny.Geometry.IntegralMixedFrozenFrameComponentCritical
public import LeanCanny.Geometry.PolynomialComponentPaths
public import LeanCanny.Geometry.IntegralMixedOriginalFrameRecord
/-! # A genuine global critical point in any provider-source component -/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignSlotRadialProviderFirstCritical
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Encoding LeanCanny.Computation
open IntegralMixedHistory IntegralMixedFrozenFrame
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def CriticalInComponent {n : ℕ} (P : SpatialSource n) (z : Fin (n+1)→ℝ) : Prop :=
  ∃ p : Fin (n+1)→ℝ,
    (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) p=0 ∧
    (∀i,i.val≠0→(MvPolynomial.pderiv i
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂ (Int.castRingHom ℝ) p=0) ∧
    JoinedIn {x | (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) x=0} z p

private theorem from_proper {n : ℕ} (P : SpatialSource n)
    (HProper : IsProperMap (fun p : Fin (n+1)→ℝ =>
      (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) p))
    (z : Fin (n+1)→ℝ)
    (hz : (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) z=0) :
    CriticalInComponent P z := by
  let F : Frame n := originalFrame ∅ (fun _=>false)
    (fun _=>IntegralMixedCausalRowConstructor.Row.single (none : IntegralMixedCausalRowConstructor.Atom 0))
  let old : Fin 0→ℝ := Fin.elim0
  have HS : z∈slice P F old := ⟨hz,fun i hi=>False.elim (Finset.notMem_empty i hi)⟩
  obtain ⟨p,HP,HG⟩ := exists_component_critical_of_proper P F old 0 (Finset.notMem_empty _) HProper z HS
  let q := FermatCriticalHomogenization.polynomial P.low P.leading P.degree
  have HE : slice P F old={x | q.eval₂ (Int.castRingHom ℝ) x=0} := by
    ext x
    exact ⟨fun h=>h.1,fun h=>⟨h,fun i hi=>False.elim (Finset.notMem_empty i hi)⟩⟩
  rw [HE] at HP
  have HJ : JoinedIn {x | q.eval₂ (Int.castRingHom ℝ) x=0} z p := by
    simpa only [CoerciveComponentSampling.Zeros,MvPolynomial.eval_map] using
      PolynomialComponentPaths.joinedIn_of_component (q.map (Int.castRingHom ℝ)) z
        (by simpa only [CoerciveComponentSampling.Zeros,MvPolynomial.eval_map,Set.mem_ofPred_eq] using hz) p
        (by simpa only [CoerciveComponentSampling.Zeros,MvPolynomial.eval_map] using HP)
  refine ⟨p,(connectedComponentIn_subset _ _ HP),?_,HJ⟩
  intro i hi
  apply HG i (Finset.notMem_empty _)
  intro he
  exact hi (congrArg Fin.val he)

theorem exists_critical (c : List Bool)
    (z : Fin (FormulaSignSlotRadialProviderMarkedGeometry.number c+4)→ℝ)
    (hz : z∈FormulaSignSlotRadialProviderMarkedGeometry.zeroSet c) :
    CriticalInComponent (FormulaSignSlotRadialProviderIntegerPlan.spatial c) z :=
  from_proper _ (FormulaSignSlotRadialProviderMarkedGeometry.proper c) z hz

theorem exists_marked_critical (c : List Bool)
    (a : BoundedZeroSource.Bounded (FormulaSignSlotRadialProviderMarkedGeometry.equation c)
      (FormulaSignSlotRadialProviderMarkedGeometry.radius c)) :
    CriticalInComponent (FormulaSignSlotRadialProviderIntegerPlan.spatial c)
      (BoundedRegularSource.markedLift (FormulaSignSlotRadialProviderMarkedGeometry.equation c)
        (FormulaSignSlotRadialProviderMarkedGeometry.allowance c) (FormulaSignSlotRadialProviderMarkedGeometry.allowance c)
        (FormulaSignSlotRadialProviderMarkedGeometry.radius c) a).val.val :=
  exists_critical c _ (FormulaSignSlotRadialProviderMarkedGeometry.markedLift_mem c a)

end LeanCanny.Connectivity.FormulaSignSlotRadialProviderFirstCritical
