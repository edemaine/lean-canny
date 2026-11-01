/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedCriticalSweep
public import LeanCanny.Geometry.AlgebraicBranchSign

/-! # Selected-component coordinate trailing cuts for a mixed sweep

The finite choice index is validated by exact coefficient-zero tests after
specializing the old algebra. The chosen relative coefficient is precisely
the trailing factor of the selected real coordinate equation, so its cuts
are finite and its avoidance makes actual coordinate zero/sign tests constant
on connected critical branches. Other algebra components are unrestricted.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCoordinateTrailing
open LeanCanny.Encoding LeanCanny.Computation IntegralMixedHistory IntegralMixedCriticalSweep
open Polynomial
open scoped Classical
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

abbrev ChoiceBound (P : SpatialSource n) (r : Rule n) :=
  PurePowerReductionBounds.dimension (n - r.critical.offset.val + 1) P.degree + 1

def Valid (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n - r.critical.offset.val + 1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (i : Fin (ChoiceBound P r)) : Prop :=
  (∀ k < i.val, ((coordinate x hm r j).coeff k).map φ.toRingHom = 0) ∧
    ((coordinate x hm r j).coeff i.val).map φ.toRingHom ≠ 0

noncomputable def factor (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n - r.critical.offset.val + 1)) (i : Fin (ChoiceBound P r)) : Polynomial x.sampler.scalarPrefix.carrier :=
  (coordinate x hm r j).coeff i.val

theorem valid_iff (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n - r.critical.offset.val + 1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (i : Fin (ChoiceBound P r)) : Valid x hm r j φ i ↔ i.val = (selected x hm r j φ).natTrailingDegree := by
  have HP := selected_ne_zero x hm r j φ
  have HC (k : ℕ) : (selected x hm r j φ).coeff k = ((coordinate x hm r j).coeff k).map φ.toRingHom :=
    Polynomial.coeff_map _ _
  constructor
  · rintro ⟨Hlow, Htop⟩
    apply Nat.le_antisymm
    · apply Polynomial.le_natTrailingDegree HP
      intro k hk
      rw [HC]
      exact Hlow k hk
    · apply Polynomial.natTrailingDegree_le_of_ne_zero
      rw [HC]
      exact Htop
  · intro H
    constructor
    · intro k hk
      rw [H] at hk
      have HE := Polynomial.coeff_eq_zero_of_lt_natTrailingDegree hk
      rw [HC] at HE
      exact HE
    · have HE := Polynomial.coeff_natTrailingDegree_ne_zero.mpr HP
      rw [← H, HC] at HE
      exact HE

theorem exists_valid (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n - r.critical.offset.val + 1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) :
    ∃ i : Fin (ChoiceBound P r), Valid x hm r j φ i := by
  have HD : (selected x hm r j φ).natTrailingDegree < ChoiceBound P r :=
    (Polynomial.natTrailingDegree_le_natDegree _).trans_lt (Nat.lt_succ_of_le
      (Polynomial.natDegree_map_le.trans (coordinate_degree x hm r j)))
  exact ⟨⟨_, HD⟩, (valid_iff x hm r j φ ⟨_, HD⟩).mpr rfl⟩

theorem factor_specialization (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n - r.critical.offset.val + 1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (i : Fin (ChoiceBound P r)) (hi : Valid x hm r j φ i) :
    (factor x hm r j i).map φ.toRingHom = (selected x hm r j φ).trailingCoeff := by
  have HE := (valid_iff x hm r j φ i).mp hi
  change _ = (selected x hm r j φ).coeff (selected x hm r j φ).natTrailingDegree
  rw [← HE]
  exact (Polynomial.coeff_map (p := coordinate x hm r j) (Polynomial.mapRingHom φ.toRingHom) i.val).symm

theorem factor_nonzero (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n - r.critical.offset.val + 1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (i : Fin (ChoiceBound P r)) (hi : Valid x hm r j φ i) : (factor x hm r j i).map φ.toRingHom ≠ 0 := hi.2

theorem factor_degree (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n - r.critical.offset.val + 1)) (i : Fin (ChoiceBound P r)) :
    (factor x hm r j i).natDegree ≤ parameterDegree P.degree r := coordinate_coefficient_degree x hm r j i.val

theorem finite_cuts (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n - r.critical.offset.val + 1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (i : Fin (ChoiceBound P r)) (hi : Valid x hm r j φ i) :
    {t : ℝ | (factor x hm r j i).eval₂ φ.toRingHom t = 0}.Finite := by
  simpa only [Polynomial.IsRoot, Polynomial.eval_map] using
    Polynomial.finite_setOfPred_isRoot (factor_nonzero x hm r j φ i hi)

variable {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]

theorem zero_iff (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n - r.critical.offset.val + 1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (i : Fin (ChoiceBound P r)) (hi : Valid x hm r j φ i)
    (parameter : X → ℝ) (y : X → Fin (n + 1) → ℝ) (ht : Continuous parameter) (hy : Continuous y)
    (hfrozen : ∀ z k, k.val < r.critical.offset.val →
      ((data x hm r.critical).scales k : ℝ) * y z k = heightValue x r φ (parameter z) k)
    (hp : ∀ z, (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) (y z) = 0)
    (hg : ∀ z (k : Fin (n - r.critical.offset.val + 1)), k ≠ objective r →
      (MvPolynomial.pderiv (ClearedCoordinateCritical.freeIndex r.critical.offset.val (fit r).le k)
        (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂ (Int.castRingHom ℝ) (y z) = 0)
    (havoid : ∀ z, (factor x hm r j i).eval₂ φ.toRingHom (parameter z) ≠ 0) (a b : X) :
    y a (ClearedCoordinateCritical.freeIndex r.critical.offset.val (fit r).le j) = 0 ↔
      y b (ClearedCoordinateCritical.freeIndex r.critical.offset.val (fit r).le j) = 0 := by
  apply LeanCanny.Geometry.AlgebraicBranchZero.zero_iff (selected x hm r j φ) parameter
    (fun z => y z (ClearedCoordinateCritical.freeIndex r.critical.offset.val (fit r).le j)) ht
    ((continuous_apply _).comp hy)
  · intro z
    exact coordinate_root x hm r j φ (parameter z) (y z) (hfrozen z) (hp z) (hg z)
  · intro z
    rw [← factor_specialization x hm r j φ i hi, Polynomial.eval_map]
    exact havoid z

end LeanCanny.Algebra.IntegralMixedCoordinateTrailing
