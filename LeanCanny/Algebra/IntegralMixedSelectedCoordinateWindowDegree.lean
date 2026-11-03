/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedSelectedCoordinateAffineDegree
public import LeanCanny.Algebra.WindowTarskiSeedDegree
/-! # Exact head and seed degrees in delta-before-epsilon layout

An independent epsilon supplies the highest nonzero query coefficient.
Swapping the coefficient axes preserves the polynomial degree in Y.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedSelectedCoordinateWindowDegree
open Polynomial
open scoped Classical

noncomputable def head (p : (ℝ[X])[X]) : ((ℝ[X])[X])[X] :=
  (p.map Polynomial.C).map Polynomial.Bivariate.swap.toRingHom
noncomputable def query (y scale : ℝ) (negative : Bool) (e : Fin 3) : ((ℝ[X])[X])[X] :=
  ((WindowTarskiSeedDegree.affineQuery (Polynomial.C (Polynomial.C scale)*(Polynomial.X-Polynomial.C (Polynomial.C y)) : (ℝ[X])[X])
    (Polynomial.C (if negative then -scale else scale)))^e.val).map Polynomial.Bivariate.swap.toRingHom

theorem head_degree (p : (ℝ[X])[X]) : (head p).natDegree=p.natDegree :=by
  rw [head,Polynomial.natDegree_map_eq_of_injective (f:=Polynomial.Bivariate.swap.toRingHom) Polynomial.Bivariate.swap.injective,
    Polynomial.natDegree_map_eq_of_injective Polynomial.C_injective]

theorem seed_degree (p : (ℝ[X])[X]) (d : ℕ) (hd : 0<d) (hp : p.natDegree=d)
    (y scale : ℝ) (hs : scale≠0) (negative : Bool) (e : Fin 3) :
    (PseudoRemainder.seed (head p) (query y scale negative e) d (d+2)).natDegree=d-1 :=by
  unfold head query
  rw [PseudoRemainder.seed_map,
    Polynomial.natDegree_map_eq_of_injective (f:=Polynomial.Bivariate.swap.toRingHom) Polynomial.Bivariate.swap.injective]
  apply WindowTarskiSeedDegree.ternary_seed_degree p _ (Polynomial.C (if negative then -scale else scale)) _ e d hd hp
  · exact (Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_X_sub_C_le _)
  · exact Polynomial.C_ne_zero.mpr (by cases negative <;> simpa using hs)


theorem query_degree (y scale : ℝ) (negative : Bool) (e : Fin 3) :
    (query y scale negative e).natDegree≤2 :=by
  unfold query
  apply Polynomial.natDegree_map_le.trans
  apply Polynomial.natDegree_pow_le.trans
  have HQ : (WindowTarskiSeedDegree.affineQuery (Polynomial.C (Polynomial.C scale)*
      (Polynomial.X-Polynomial.C (Polynomial.C y)) : (ℝ[X])[X])
        (Polynomial.C (if negative then -scale else scale))).natDegree≤1 :=
    WindowTarskiSeedDegree.affineQuery_degree _ _
      ((Polynomial.natDegree_C_mul_le _ _).trans (Polynomial.natDegree_X_sub_C_le _))
  exact (Nat.mul_le_mul_left e.val HQ).trans (by have HE:=e.isLt;omega)

theorem input_degree (p : (ℝ[X])[X]) (d : ℕ) (hp : p.natDegree=d)
    (y scale : ℝ) (negative : Bool) (e : Fin 3) :
    (query y scale negative e*(head p).derivative).natDegree≤d+2 :=by
  have HH : (head p).natDegree=d:=(head_degree p).trans hp
  have HD:=Polynomial.natDegree_derivative_le (head p)
  have HQ:=query_degree y scale negative e
  exact Polynomial.natDegree_mul_le.trans (by rw [HH] at HD;omega)


theorem selected_seed_degree {n S B m : ℕ} {P : IntegralMixedHistory.SpatialSource n} {ι : Type}
    (x : IntegralMixedHistory.State P S B m ι) (hm : m≤S) (r : IntegralMixedCriticalSweep.Rule n)
    (j : Fin (n-r.critical.offset.val+1)) (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (a : ℝ) (negativeEta : Bool) (Q : ℤ) (hQ : Q≠0) (allowance : ℕ)
    (y scale : ℝ) (hs : scale≠0) (negativeEpsilon : Bool) (e : Fin 3) :
    (PseudoRemainder.seed
      (head (IntegralMixedSelectedCoordinateAffineDegree.head x hm r j φ a negativeEta Q allowance))
      (query y scale negativeEpsilon e)
      (PurePowerReductionBounds.dimension (n-r.critical.offset.val+1) P.degree)
      (PurePowerReductionBounds.dimension (n-r.critical.offset.val+1) P.degree+2)).natDegree=
        PurePowerReductionBounds.dimension (n-r.critical.offset.val+1) P.degree-1 :=
  seed_degree _ _ (pow_pos (Nat.two_pow_pos _) _)
    (IntegralMixedSelectedCoordinateAffineDegree.head_degree x hm r j φ a negativeEta Q hQ allowance)
    y scale hs negativeEpsilon e

end LeanCanny.Algebra.IntegralMixedSelectedCoordinateWindowDegree
