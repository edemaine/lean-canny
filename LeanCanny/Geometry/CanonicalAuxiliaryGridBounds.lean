/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.CanonicalAuxiliaryFiniteGrid
public import LeanCanny.Algebra.IntegralMixedLimitCoordinateRootCount
public import Mathlib.Data.ENat.BigOperators
/-! # The actual selected auxiliary grid has a bounded number of points

Each free coordinate has at most 2^B possible values at the same old real hom.
Frozen coordinates contribute one value. This is a semantic bound for the
actual grid; effective point encoding and validity remain separate tasks.
-/
@[expose] public section
namespace LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
open LeanCanny.Algebra LeanCanny.ETR IntegralMixedHistory IntegralMixedCriticalSweep
open AuxiliaryTiltedTerm FrozenAuxiliaryComponentSampling IntegralMixedCanonicalDilation
open Set Polynomial
open scoped Classical BigOperators
variable {n k D S B m G : ℕ} {t : Term} {ht : (term n t).degreeBound≤D} {ι : Type}

theorem coordinateRoots_ncard_le_width (x : State (source k D t ht m B G) S B m ι) (hm : m≤S)
    (select : Fin k → Fin m) (hk : k≤n) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (j : Fin (n+1)) (hj : k≤j.val) : (coordinateRoots x hm select hk φ j hj).ncard≤2^B := by
  simpa only [coordinateRoots,IntegralMixedLimitCoordinate.roots] using
    IntegralMixedLimitCoordinate.roots_ncard_le_width x hm (rule (by omega : k≤n+1) select)
      (coordinateIndex (by omega : k≤n+1) select j hj) φ

theorem grid_ncard_le_width (x : State (source k D t ht m B G) S B m ι) (hm : m≤S)
    (select : Fin k → Fin m) (hk : k≤n) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (a : Fin n → ℝ) :
    (grid x hm select hk φ a).ncard≤2^(B*(n+1)) := by
  let A := fun j : Fin (n+1) => if hj : j.val<k then {a ⟨j.val,by omega⟩}
    else coordinateRoots x hm select hk φ j (by omega)
  have HE : (grid x hm select hk φ a).ncard = ∏ j : Fin (n+1), (A j).ncard := by
    simp only [grid,Set.ncard_def,Set.encard_pi_eq_prod_encard,ENat.toNat_prod,A]
  rw [HE]
  calc
    ∏ j : Fin (n+1), (A j).ncard ≤ ∏ _j : Fin (n+1), 2^B := by
      apply Finset.prod_le_prod
      intro j _
      dsimp only [A]
      split_ifs
      · simpa only [Set.ncard_singleton] using Nat.one_le_two_pow (n := B)
      · exact coordinateRoots_ncard_le_width x hm select hk φ j _
    _ = 2^(B*(n+1)) := by simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,pow_mul]

theorem grid_ncard_size_le (x : State (source k D t ht m B G) S B m ι) (hm : m≤S)
    (select : Fin k → Fin m) (hk : k≤n) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (a : Fin n → ℝ) :
    (grid x hm select hk φ a).ncard.size≤B*(n+1)+1 :=
  (Nat.size_le_size (grid_ncard_le_width x hm select hk φ a)).trans_eq Nat.size_pow

theorem grid_bounded_codes (x : State (source k D t ht m B G) S B m ι) (hm : m≤S)
    (select : Fin k → Fin m) (hk : k≤n) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (a : Fin n → ℝ) :
    ∃ code : grid x hm select hk φ a → Fin (2^(B*(n+1))), Function.Injective code := by
  let := (finite_grid x hm select hk φ a).fintype
  have HC : Fintype.card (grid x hm select hk φ a)≤2^(B*(n+1)) :=
    (Set.fintypeCard_eq_ncard _).trans_le (grid_ncard_le_width x hm select hk φ a)
  exact ⟨fun p => Fin.castLE HC ((Fintype.equivFin _) p),
    (Fin.castLE_injective HC).comp (Fintype.equivFin _).injective⟩

end LeanCanny.Geometry.CanonicalAuxiliaryTrajectory
