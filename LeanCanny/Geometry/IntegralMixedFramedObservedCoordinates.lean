/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedObservedInterpretation
public import LeanCanny.Algebra.IntegralMixedFramedSlackMatrices

/-! # One observed natural tuple supplies a selected block of original coordinates -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFramedObservedCoordinates
open LeanCanny.Algebra LeanCanny.Encoding IntegralCriticalHistoryTask UniformIntegralPrefix
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open IntegralMixedFramedSlackMatrixBits (elementAt commonAt)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem exists_interpretation (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (key : List Bool) (hkey : IntegralMixedFramedClearedMatrixBits.Active P key) (m : ℕ)
    (hm : m<(family P D H).birth key) (z : ℕ→ℝ)
    (hz : RootsAt ((family P D H).state key).sampler.scalarPrefix z) (a : Fin m→ℝ)
    (ha : ∀i : Fin m,(IntegralMixedFramedBankObservation.ofState ((family P D H).state key)).point z (m-i.val)=a i) :
    ∃φ : ((family P D H).state key).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      ∀i : Fin m,φ (elementAt P D H key (m-i.val))=(commonAt P D H key : ℝ)*a i := by
  obtain ⟨φ,hφ⟩:=IntegralMixedObservedInterpretation.exists_interpretation ((family P D H).state key)
    (IntegralMixedFramedHistoryFamilyBits.family_canonical P D H key) z hz
  refine ⟨φ,fun i=>?_⟩
  have hi : m-i.val<(family P D H).birth key := by omega
  rw [elementAt,ite_eq_left hkey,dite_eq_left hi]
  exact (hφ ⟨m-i.val,hi⟩).trans (congrArg (fun r : ℝ=>(commonAt P D H key : ℝ)*r) (ha i))

end LeanCanny.Geometry.IntegralMixedFramedObservedCoordinates
