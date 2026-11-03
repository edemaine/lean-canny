/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedSelectedCoordinateHeadWidth
public import LeanCanny.Algebra.RationalMonomialBivariateShift
/-! # Exact coordinate degree after shifting eta at one selected old hom

The endpoint and clearing factor may come from the retained bank. They stay
fixed while delta varies; the same old interpreting hom is used throughout.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedSelectedCoordinateAffineDegree
open Polynomial IntegralMixedHistory
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

noncomputable def shift (a : ℝ) (negative : Bool) : ℝ[X]→+*ℝ[X] :=
  Polynomial.eval₂RingHom Polynomial.C (Polynomial.C a+if negative then -Polynomial.X else Polynomial.X)

theorem shift_evaluate (a δ : ℝ) (negative : Bool) :
    (Polynomial.evalRingHom δ).comp (shift a negative)=Polynomial.evalRingHom (a+if negative then -δ else δ) :=by
  cases negative <;> ext r <;> simp [shift]

noncomputable def head (x : State P S B m ι) (hm : m≤S) (r : IntegralMixedCriticalSweep.Rule n)
    (j : Fin (n-r.critical.offset.val+1)) (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (a : ℝ) (negative : Bool) (Q : ℤ) (allowance : ℕ) : (ℝ[X])[X] :=
  Polynomial.C (Polynomial.C ((Q:ℝ)^(2*allowance)))*
    (IntegralMixedCriticalSweep.selected x hm r j φ).map (shift a negative)

theorem evaluated_degree (x : State P S B m ι) (hm : m≤S) (r : IntegralMixedCriticalSweep.Rule n)
    (j : Fin (n-r.critical.offset.val+1)) (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (a : ℝ) (negative : Bool) (Q : ℤ) (hQ : Q≠0) (allowance : ℕ) (δ : ℝ) :
    ((head x hm r j φ a negative Q allowance).map (Polynomial.evalRingHom δ)).natDegree=
      PurePowerReductionBounds.dimension (n-r.critical.offset.val+1) P.degree :=by
  unfold head
  rw [Polynomial.map_mul,Polynomial.map_C,Polynomial.coe_evalRingHom,Polynomial.eval_C,
    Polynomial.map_map,shift_evaluate,Polynomial.natDegree_C_mul (pow_ne_zero _ (Int.cast_ne_zero.mpr hQ))]
  exact IntegralMixedCriticalSweep.specialized_degree x hm r j φ _

theorem head_degree (x : State P S B m ι) (hm : m≤S) (r : IntegralMixedCriticalSweep.Rule n)
    (j : Fin (n-r.critical.offset.val+1)) (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (a : ℝ) (negative : Bool) (Q : ℤ) (hQ : Q≠0) (allowance : ℕ) :
    (head x hm r j φ a negative Q allowance).natDegree=
      PurePowerReductionBounds.dimension (n-r.critical.offset.val+1) P.degree :=by
  apply le_antisymm
  · exact (Polynomial.natDegree_C_mul_le _ _).trans
      (Polynomial.natDegree_map_le.trans (Polynomial.natDegree_map_le.trans
        (IntegralMixedCriticalSweep.coordinate_degree x hm r j)))
  · rw [←evaluated_degree x hm r j φ a negative Q hQ allowance 0]
    exact Polynomial.natDegree_map_le

end LeanCanny.Algebra.IntegralMixedSelectedCoordinateAffineDegree
