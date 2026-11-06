/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppendPrefix
public import LeanCanny.Connectivity.FormulaSignSlotRadialProviderFirstCritical
/-! # Genuine global padding critical points for the same prepared provider source -/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation
open IntegralMixedHistory
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem exists_padding_critical (old : List Bool) (e : ℕ)
    (p : Fin (FormulaSignSlotRadialProviderRecordPlan.parameters.ambient (preparedRoot old e)+1)→ℝ)
    (hp : (FermatCriticalHomogenization.polynomial
      (FormulaSignSlotRadialProviderRecordPlan.spatial (preparedRoot old e)).low
      (FormulaSignSlotRadialProviderRecordPlan.spatial (preparedRoot old e)).leading
      (FormulaSignSlotRadialProviderRecordPlan.spatial (preparedRoot old e)).degree).eval₂ (Int.castRingHom ℝ) p=0) :
    ∃p0 : Fin (FormulaSignSlotRadialProviderRecordPlan.parameters.ambient (preparedRoot old e)+1)→ℝ,
      (FermatCriticalHomogenization.polynomial
        (FormulaSignSlotRadialProviderRecordPlan.spatial (preparedRoot old e)).low
        (FormulaSignSlotRadialProviderRecordPlan.spatial (preparedRoot old e)).leading
        (FormulaSignSlotRadialProviderRecordPlan.spatial (preparedRoot old e)).degree).eval₂ (Int.castRingHom ℝ) p0=0 ∧
      ∀i,i≠0→(MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial
        (FormulaSignSlotRadialProviderRecordPlan.spatial (preparedRoot old e)).low
        (FormulaSignSlotRadialProviderRecordPlan.spatial (preparedRoot old e)).leading
        (FormulaSignSlotRadialProviderRecordPlan.spatial (preparedRoot old e)).degree)).eval₂ (Int.castRingHom ℝ) p0=0 := by
  obtain ⟨p0,hp0,hg0,_⟩ := LeanCanny.Connectivity.FormulaSignSlotRadialProviderFirstCritical.exists_critical
    (FormulaSignSlotRadialProviderRecordPlan.providerContext (preparedRoot old e)) p hp
  refine ⟨p0,hp0,fun i hi=>hg0 i ?_⟩
  intro h
  apply hi
  exact Fin.ext h

end LeanCanny.Encoding.FormulaSignSlotRadialProviderRetainedAppend
