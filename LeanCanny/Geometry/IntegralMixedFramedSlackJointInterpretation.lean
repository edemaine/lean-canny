/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFramedSlackInterpretation
public import LeanCanny.Geometry.IntegralMixedCanonicalBankPoint
public import LeanCanny.Algebra.IntegralMixedHistorySemantics

/-! # One actual joint root constructs the old slack interpretation

Every cleared original coordinate is interpreted through the same raw tuple.
The caller supplies coordinate readback equalities, not an interpreting hom.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFramedSlackJointInterpretation
open LeanCanny.Algebra LeanCanny.Encoding IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedSlackMatrixBits
open IntegralMixedFramedClearedMatrixBits (family Active)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem exists_coordinate_interpretation (P : Parameters) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) (ha : Active P key)
    (N : ℕ) (hN : N<(family P D H).birth key)
    (z : Fin ((family P D H).birth key)→ℝ)
    (hz : ∀ i,(((family P D H).state key).sampler.scalarPrefix.rows i).eval₂ (Int.castRingHom ℝ) z=0)
    (x : Fin N→ℝ)
    (hx : ∀ i : Fin N,IntegralMixedCanonicalBankPoint.point ((family P D H).state key) z
      ⟨N-i.val,by omega⟩=x i) :
    ∃ φ : ((family P D H).state key).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ,
      ∀ i : Fin N,φ (elementAt P D H key (N-i.val))=(commonAt P D H key : ℝ)*x i := by
  obtain ⟨φ,_,hφ⟩:=IntegralMixedCanonicalBankPoint.interprets ((family P D H).state key)
    (IntegralMixedFramedHistoryFamilyBits.family_canonical P D H key) z hz
  refine ⟨φ,fun i=>?_⟩
  have hi : N-i.val<(family P D H).birth key:=by omega
  rw [elementAt,ite_eq_left ha,dite_eq_left hi]
  exact (IntegralMixedHistory.cleared_recover ((family P D H).state key) φ
    (IntegralMixedCanonicalBankPoint.point ((family P D H).state key) z) hφ ⟨N-i.val,hi⟩).trans
      (congrArg (fun r : ℝ=>(commonAt P D H key : ℝ)*r) (hx i))

end LeanCanny.Geometry.IntegralMixedFramedSlackJointInterpretation
