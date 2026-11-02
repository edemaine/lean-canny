/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedFrozenFrameRelative
public import LeanCanny.Algebra.ClearedAffinePolynomial

/-! # Finite actual affine-height cuts for the current coarse frame

An ordinary relative coordinate polynomial on the coarse slice is cleared
at the literal current-bank affine height. No inverse occurs in the cut,
no initial-bank denominator is substituted, and spatial degree stays fixed.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedFrozenFrame
open LeanCanny.Algebra IntegralMixedHistory Set
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

noncomputable def heightRelative (x : State P S B m ι) (hm : m≤S) (F : Frame n) (h : Fin (n+1)) : Polynomial x.sampler.scalarPrefix.carrier :=
  criticalPolynomial (IntegralMixedCoordinateRename.state x
    (FrozenCoordinateOrdering.permutation (coarse F h).frozen)) hm
    (coordinateRule (coarse F h) h (Finset.notMem_erase h F.frozen))

noncomputable def heightDegree (x : State P S B m ι) (hm : m≤S) (F : Frame n) (h : Fin (n+1)) : ℕ :=
  criticalDegree (IntegralMixedCoordinateRename.state x
    (FrozenCoordinateOrdering.permutation (coarse F h).frozen)) hm
    (coordinateRule (coarse F h) h (Finset.notMem_erase h F.frozen))

noncomputable def heightCut (x : State P S B m ι) (hm : m≤S) (F : Frame n) (h : Fin (n+1)) : Polynomial x.sampler.scalarPrefix.carrier :=
  ClearedAffinePolynomial.polynomial (heightDegree x hm F h) (heightRelative x hm F h)
    (expression x (F.heights h)) (commonDenominator x : x.sampler.scalarPrefix.carrier)
    ((commonDenominator x*F.scales h : ℤ) : x.sampler.scalarPrefix.carrier)

theorem heightRelative_degree (x : State P S B m ι) (hm : m≤S) (F : Frame n) (h : Fin (n+1)) :
    (heightRelative x hm F h).natDegree≤heightDegree x hm F h :=
  IntegralMixedCriticalRoot.degree_le _ _ _

theorem heightRelative_nonzero (x : State P S B m ι) (hm : m≤S) (F : Frame n) (h : Fin (n+1))
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) : (heightRelative x hm F h).map φ.toRingHom≠0 :=
  IntegralMixedCriticalRoot.selected_nonzero
    (IntegralMixedCoordinateRename.state x (FrozenCoordinateOrdering.permutation (coarse F h).frozen)) hm
    (coordinateRule (coarse F h) h (Finset.notMem_erase h F.frozen)) φ

theorem heightCut_degree (x : State P S B m ι) (hm : m≤S) (F : Frame n) (h : Fin (n+1)) :
    (heightCut x hm F h).natDegree≤heightDegree x hm F h :=
  (ClearedAffinePolynomial.degree_le _ _ _ _ _).trans (IntegralMixedCriticalRoot.degree_le _ _ _)

theorem heightCut_cap (x : State P S B m ι) (hm : m≤S) (F : Frame n) (h : Fin (n+1)) :
    (heightCut x hm F h).natDegree≤2^B :=
  (heightCut_degree x hm F h).trans (criticalDegree_cap _ _ _)

theorem heightCut_nonzero (x : State P S B m ι) (hm : m≤S) (F : Frame n) (h : Fin (n+1))
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) :
    (heightCut x hm F h).map φ.toRingHom≠0 := by
  change (ClearedAffinePolynomial.polynomial (heightDegree x hm F h) (heightRelative x hm F h)
    (expression x (F.heights h)) (commonDenominator x : x.sampler.scalarPrefix.carrier)
    ((commonDenominator x*F.scales h : ℤ) : x.sampler.scalarPrefix.carrier)).map φ.toRingHom≠0
  apply ClearedAffinePolynomial.selected_nonzero φ.toRingHom (heightDegree x hm F h) (heightRelative x hm F h)
    (expression x (F.heights h)) (commonDenominator x : x.sampler.scalarPrefix.carrier)
    ((commonDenominator x*F.scales h : ℤ) : x.sampler.scalarPrefix.carrier)
    (heightRelative_degree x hm F h) (heightRelative_nonzero x hm F h φ)
  · rw [map_intCast]
    exact Int.cast_ne_zero.mpr (commonDenominator_ne_zero x)
  · rw [map_intCast]
    exact Int.cast_ne_zero.mpr (mul_ne_zero (commonDenominator_ne_zero x) (F.scales_ne_zero h))

theorem heightCut_finite (x : State P S B m ι) (hm : m≤S) (F : Frame n) (h : Fin (n+1))
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) :
    {t : ℝ | (heightCut x hm F h).eval₂ φ.toRingHom t=0}.Finite := by
  simpa only [Polynomial.IsRoot,Polynomial.eval_map] using
    Polynomial.finite_setOfPred_isRoot (heightCut_nonzero x hm F h φ)

theorem heightCut_root (x : State P S B m ι) (hm : m≤S)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ) (F : Frame n) (h : Fin (n+1)) (hh : h∈F.frozen)
    (values : Fin m→ℝ) (H : ∀ i,φ (x.bank.numerator i)/(x.bank.denominator i:ℝ)=values i)
    (t : ℝ) (y : Fin (n+1)→ℝ) (hy : y∈shiftedSlice P F values h t)
    (hgrad : ∀ i, i∉F.frozen→
      (MvPolynomial.pderiv i (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂
        (Int.castRingHom ℝ) y=0) :
    (heightCut x hm F h).eval₂ φ.toRingHom t=0 := by
  have HY : y∈slice P (coarse F h) values :=
    ((Set.ext_iff.mp (shiftedSlice_fiber P F values h hh t) y).mp hy).1
  have HR : (heightRelative x hm F h).eval₂ φ.toRingHom (y h)=0 :=
    relative_coordinate_root x hm φ (coarse F h) h (Finset.notMem_erase h F.frozen) values H y HY
      (fun i hi hih=>hgrad i (fun Hmem=>hi (Finset.mem_erase.mpr ⟨hih,Hmem⟩)))
  have HQ : (commonDenominator x:ℝ)≠0:=Int.cast_ne_zero.mpr (commonDenominator_ne_zero x)
  have HS : (F.scales h:ℝ)≠0:=Int.cast_ne_zero.mpr (F.scales_ne_zero h)
  have HE:=expression_recover x φ values H (F.heights h)
  have HH:=hy.2 h hh
  rw [ite_eq_left (rfl : h=h)] at HH
  have Hfrac : (φ (expression x (F.heights h))+(commonDenominator x:ℝ)*t)/
      ((commonDenominator x:ℝ)*(F.scales h:ℝ))=y h := by
    apply (div_eq_iff (mul_ne_zero HQ HS)).mpr
    rw [HE]
    calc
      _=(commonDenominator x:ℝ)*((F.heights h).evaluate values+t) := by ring
      _=(commonDenominator x:ℝ)*((F.scales h:ℝ)*y h) := congrArg ((commonDenominator x:ℝ)*·) HH.symm
      _=y h*((commonDenominator x:ℝ)*(F.scales h:ℝ)) := by ring
  have Hq : φ.toRingHom ((commonDenominator x*F.scales h:ℤ):x.sampler.scalarPrefix.carrier)≠0 := by
    rw [map_intCast,Int.cast_mul]
    exact mul_ne_zero HQ HS
  have HA:=ClearedAffinePolynomial.eval φ.toRingHom (heightDegree x hm F h) (heightRelative x hm F h)
    (expression x (F.heights h)) (commonDenominator x : x.sampler.scalarPrefix.carrier)
    ((commonDenominator x*F.scales h:ℤ):x.sampler.scalarPrefix.carrier)
    (heightRelative_degree x hm F h) Hq t
  change (heightCut x hm F h).eval₂ φ.toRingHom t=_ at HA
  simp only [map_mul,map_intCast,Int.cast_mul] at HA
  change (heightCut x hm F h).eval₂ φ.toRingHom t=
    ((commonDenominator x:ℝ)*(F.scales h:ℝ))^heightDegree x hm F h *
      (heightRelative x hm F h).eval₂ φ.toRingHom
        ((φ (expression x (F.heights h))+(commonDenominator x:ℝ)*t)/
          ((commonDenominator x:ℝ)*(F.scales h:ℝ))) at HA
  rw [Hfrac,HR,mul_zero] at HA
  exact HA

end LeanCanny.Geometry.IntegralMixedFrozenFrame
