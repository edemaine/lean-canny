/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCurrentQSquarefreeCuts
public import LeanCanny.Algebra.IntegralMixedCurrentQValueCuts
public import LeanCanny.Connectivity.IntegralMixedSelectedCriticalCuts
/-! # The actual three-class slab bad set is invariant under retained commands

The fourth ABI kind, limitCoordinate, is deliberately absent from this
bad-set claim. Its extra Q powers change the physical root parameter.
The unused limit choice in Choices is freshly validated instead.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCurrentQCoordinateScaling
open IntegralMixedHistory IntegralMixedFullHistoryScript IntegralMixedCriticalSweep Polynomial
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
variable (x : State P S B m ι) (hm : m≤S) (c : Command P B) (hn : m+1≤S)
    (r : Rule n) (hr : r.slope=commonDenominator x)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (ψ : (step x hm c).sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (values : Fin m→ℝ) (a : ℝ)
    (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (HN : ∀ i,ψ ((step x hm c).bank.numerator i)/((step x hm c).bank.denominator i:ℝ)=
      (Fin.cons a values : Fin (m+1)→ℝ) i)

include hr H HN


noncomputable def retainedChoices (old : IntegralMixedRelativeCuts.Choices x hm r φ) :
    IntegralMixedRelativeCuts.Choices (step x hm c) hn (shiftRule x hm c r) ψ where
  coordinateIndex:=old.coordinateIndex
  coordinateValid:=fun j=>(coordinate_valid_iff x hm c hn r hr φ ψ values a H HN j _).mpr (old.coordinateValid j)
  squarefreeIndex:=old.squarefreeIndex
  squarefreeValid:=fun j=>(squarefree_valid_iff x hm c hn r hr φ ψ values a H HN j _).mpr (old.squarefreeValid j)
  valueIndex:=old.valueIndex
  valueValid:=fun j=>(value_valid_iff x hm c hn r hr φ ψ values a H HN j _).mpr (old.valueValid j)
  limitIndex:=fun j=>Classical.choose (IntegralMixedLimitCoordinate.exists_valid (step x hm c) hn (shiftRule x hm c r) j ψ)
  limitValid:=fun j=>Classical.choose_spec (IntegralMixedLimitCoordinate.exists_valid (step x hm c) hn (shiftRule x hm c r) j ψ)

theorem retained_cut_root_iff (old : IntegralMixedRelativeCuts.Choices x hm r φ)
    (j : LeanCanny.Connectivity.IntegralMixedSelectedCriticalCuts.Tag r) (t : ℝ) :
    (LeanCanny.Connectivity.IntegralMixedSelectedCriticalCuts.cut (step x hm c) hn (shiftRule x hm c r) ψ
      (retainedChoices x hm c hn r hr φ ψ values a H HN old) j).eval₂ ψ.toRingHom t=0 ↔
      (LeanCanny.Connectivity.IntegralMixedSelectedCriticalCuts.cut x hm r φ old j).eval₂ φ.toRingHom t=0 :=by
  rcases j with ⟨tag,j⟩
  fin_cases tag
  · change (IntegralMixedCoordinateTrailing.factor (step x hm c) hn (shiftRule x hm c r) j (old.coordinateIndex j)).eval₂ ψ.toRingHom t=0 ↔
      (IntegralMixedCoordinateTrailing.factor x hm r j (old.coordinateIndex j)).eval₂ φ.toRingHom t=0
    exact coordinate_factor_root_iff x hm c hn r hr φ ψ values a H HN j _ t
  · change (IntegralMixedCoordinateSquarefree.exceptional (step x hm c) hn (shiftRule x hm c r) j (old.squarefreeIndex j)).eval₂ ψ.toRingHom t=0 ↔
      (IntegralMixedCoordinateSquarefree.exceptional x hm r j (old.squarefreeIndex j)).eval₂ φ.toRingHom t=0
    exact squarefree_factor_root_iff x hm c hn r hr φ ψ values a H HN j _ t
  · change (IntegralMixedValueTrailing.factor (step x hm c) hn (shiftRule x hm c r) j (old.valueIndex j)).eval₂ ψ.toRingHom t=0 ↔
      (IntegralMixedValueTrailing.factor x hm r j (old.valueIndex j)).eval₂ φ.toRingHom t=0
    exact value_factor_root_iff x hm c hn r hr φ ψ values a H HN j _ (old.valueValid j) t

theorem retained_bad_iff (old : IntegralMixedRelativeCuts.Choices x hm r φ) (t : ℝ) :
    t∈LeanCanny.Connectivity.IntegralMixedSelectedCriticalCuts.bad (step x hm c) hn (shiftRule x hm c r) ψ
      (retainedChoices x hm c hn r hr φ ψ values a H HN old) ↔
      t∈LeanCanny.Connectivity.IntegralMixedSelectedCriticalCuts.bad x hm r φ old :=by
  constructor
  · rintro ⟨j,Hj⟩
    exact ⟨j,(retained_cut_root_iff x hm c hn r hr φ ψ values a H HN old j t).mp Hj⟩
  · rintro ⟨j,Hj⟩
    exact ⟨j,(retained_cut_root_iff x hm c hn r hr φ ψ values a H HN old j t).mpr Hj⟩

end LeanCanny.Algebra.IntegralMixedCurrentQCoordinateScaling
