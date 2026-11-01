/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedHistorySemantics
public import LeanCanny.Algebra.ClearedCoordinateParameterDegree

/-! # Relative coordinate equations on the actual mixed frozen sweep

One frozen affine height varies with a real sweep parameter. The original
integer spatial source, integer coordinate scales, and retained algebra
are unchanged. The coordinate equations are constructed by pure-power
reduction over the old algebra with a formal sweep parameter. Their
relative spatial and parameter degrees do not contain the old algebra rank.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCriticalSweep
open LeanCanny.Encoding LeanCanny.Computation IntegralMixedHistory IntegralHistorySampler
open Polynomial
open scoped Classical

structure Rule (n : ℕ) where
  critical : CriticalRule n
  height : Fin (n + 1)
  height_frozen : height.val < critical.offset.val
  slope : ℤ
  slope_ne_zero : slope ≠ 0

variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type}

noncomputable def heights (x : State P S B m ι) (r : Rule n) (i : Fin (n + 1)) :
    Polynomial x.sampler.scalarPrefix.carrier :=
  C (expression x (r.critical.heights i)) + if i = r.height then C (r.slope : x.sampler.scalarPrefix.carrier) * X else 0

noncomputable def evaluation (x : State P S B m ι) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (t : ℝ) :
    Polynomial x.sampler.scalarPrefix.carrier →+* ℝ :=
  (Polynomial.evalRingHom t).comp (Polynomial.mapRingHom φ.toRingHom)

noncomputable def heightValue (x : State P S B m ι) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (t : ℝ) (i : Fin (n + 1)) : ℝ :=
  φ (expression x (r.critical.heights i)) + if i = r.height then (r.slope : ℝ) * t else 0

theorem evaluation_heights (x : State P S B m ι) (r : Rule n)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (t : ℝ) (i : Fin (n + 1)) :
    evaluation x φ t (heights x r i) = heightValue x r φ t i := by
  by_cases hi : i = r.height <;> simp [heights, heightValue, evaluation, Polynomial.coe_mapRingHom, hi]

theorem fit (r : Rule n) : r.critical.offset.val + (n - r.critical.offset.val + 1) = n + 1 := by
  have H := r.critical.offset.isLt
  omega

def objective (r : Rule n) : Fin (n - r.critical.offset.val + 1) :=
  ⟨r.critical.objective % (n - r.critical.offset.val + 1), Nat.mod_lt _ (by omega)⟩

noncomputable def coordinate (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n - r.critical.offset.val + 1)) : Polynomial (Polynomial x.sampler.scalarPrefix.carrier) :=
  CoordinateFrozenCriticalElimination.polynomial P.degree (data x hm r.critical).scales (heights x r)
    r.critical.offset.val (fit r)
    (P.low.map (Int.castRingHom (Polynomial x.sampler.scalarPrefix.carrier)))
    (P.leading : Polynomial x.sampler.scalarPrefix.carrier) (objective r) j

noncomputable def selected (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n - r.critical.offset.val + 1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) :
    Polynomial (Polynomial ℝ) := (coordinate x hm r j).map (Polynomial.mapRingHom φ.toRingHom)

theorem evaluation_integer_source (x : State P S B m ι)
    (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (t : ℝ)
    (q : MvPolynomial (Fin (n + 1)) ℤ) (y : Fin (n + 1) → ℝ) :
    (q.map (Int.castRingHom (Polynomial x.sampler.scalarPrefix.carrier))).eval₂ (evaluation x φ t) y =
      q.eval₂ (Int.castRingHom ℝ) y := by
  rw [MvPolynomial.eval₂_map]
  have H : (evaluation x φ t).comp (Int.castRingHom (Polynomial x.sampler.scalarPrefix.carrier)) = Int.castRingHom ℝ :=
    RingHom.ext_int _ _
  rw [H]

theorem coordinate_root (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n - r.critical.offset.val + 1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ)
    (t : ℝ) (y : Fin (n + 1) → ℝ)
    (hfrozen : ∀ i, i.val < r.critical.offset.val →
      ((data x hm r.critical).scales i : ℝ) * y i = heightValue x r φ t i)
    (hp : (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).eval₂ (Int.castRingHom ℝ) y = 0)
    (hg : ∀ i : Fin (n - r.critical.offset.val + 1), i ≠ objective r →
      (MvPolynomial.pderiv (ClearedCoordinateCritical.freeIndex r.critical.offset.val (fit r).le i)
        (FermatCriticalHomogenization.polynomial P.low P.leading P.degree)).eval₂ (Int.castRingHom ℝ) y = 0) :
    (selected x hm r j φ).eval₂ (Polynomial.evalRingHom t)
      (y (ClearedCoordinateCritical.freeIndex r.critical.offset.val (fit r).le j)) = 0 := by
  rw [selected, Polynomial.eval₂_map]
  have HS : FermatCriticalHomogenization.polynomial
      (P.low.map (Int.castRingHom (Polynomial x.sampler.scalarPrefix.carrier)))
      (P.leading : Polynomial x.sampler.scalarPrefix.carrier) P.degree =
        (FermatCriticalHomogenization.polynomial P.low P.leading P.degree).map
          (Int.castRingHom (Polynomial x.sampler.scalarPrefix.carrier)) :=
    (FermatCriticalHomogenization.map_polynomial (Int.castRingHom (Polynomial x.sampler.scalarPrefix.carrier)) P.low P.leading P.degree).symm
  apply CoordinateFrozenCriticalElimination.root (evaluation x φ t) P.degree P.degree_two
    (data x hm r.critical).scales (data x hm r.critical).scales_ne (heights x r)
    r.critical.offset.val (fit r) _ _
    ((PolynomialMapDegree.degree_le _ P.low).trans_lt P.low_degree)
    (objective r) y
  · intro i hi
    rw [evaluation_heights]
    exact hfrozen i hi
  · rw [HS, evaluation_integer_source]
    exact hp
  · intro i hi
    rw [HS, MvPolynomial.pderiv_map, evaluation_integer_source]
    exact hg i hi

theorem specialized_degree (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n - r.critical.offset.val + 1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) (t : ℝ) :
    ((selected x hm r j φ).map (Polynomial.evalRingHom t)).natDegree =
      PurePowerReductionBounds.dimension (n - r.critical.offset.val + 1) P.degree := by
  rw [selected, Polynomial.map_map]
  exact CoordinateFrozenCriticalElimination.specialized_degree (evaluation x φ t) P.degree
    (by have H := P.degree_two; omega) (data x hm r.critical).scales (data x hm r.critical).scales_ne
    (heights x r) r.critical.offset.val (fit r) _ _
    (by rw [map_intCast]; exact Int.cast_ne_zero.mpr P.leading_ne_zero) _ j

theorem selected_ne_zero (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n - r.critical.offset.val + 1)) (φ : x.sampler.scalarPrefix.carrier →ₐ[ℤ] ℝ) : selected x hm r j φ ≠ 0 := by
  intro HZ
  have H := specialized_degree x hm r j φ 0
  rw [HZ, Polynomial.map_zero, Polynomial.natDegree_zero] at H
  have HP : 0 < PurePowerReductionBounds.dimension (n - r.critical.offset.val + 1) P.degree :=
    pow_pos (Nat.two_pow_pos _) _
  omega

theorem heights_degree (x : State P S B m ι) (r : Rule n) (i : Fin (n + 1)) :
    (heights x r i).natDegree ≤ 1 := by
  unfold heights
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le
  · simp only [Polynomial.natDegree_C, Nat.zero_le]
  · split_ifs
    · exact Polynomial.natDegree_mul_le.trans (by simp)
    · simp only [Polynomial.natDegree_zero, Nat.zero_le]

def parameterDegree (D : ℕ) (r : Rule n) : ℕ :=
  PurePowerReductionBounds.dimension (n - r.critical.offset.val + 1) D *
    ((PurePowerReductionBounds.bound (n - r.critical.offset.val + 1) D + 1) * D)

theorem coordinate_coefficient_degree (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n - r.critical.offset.val + 1)) (k : ℕ) :
    ((coordinate x hm r j).coeff k).natDegree ≤ parameterDegree P.degree r := by
  have Hlow : PolynomialCoefficientDegree.Bound
      (P.low.map (Int.castRingHom (Polynomial x.sampler.scalarPrefix.carrier))) 0 := by
    intro e
    rw [MvPolynomial.coeff_map]
    exact (Polynomial.natDegree_intCast _).le
  have HH (i : ℕ) : (CoordinateFrozenCriticalElimination.numerators
      (data x hm r.critical).scales (heights x r) i).natDegree ≤ 1 := by
    unfold CoordinateFrozenCriticalElimination.numerators
    split_ifs with hi
    · unfold CommonIntegerDenominator.numerator
      exact Polynomial.natDegree_mul_le.trans (by
        rw [Polynomial.natDegree_intCast, Nat.add_zero]
        exact heights_degree x r ⟨i, hi⟩)
    · simp only [Polynomial.natDegree_zero, Nat.zero_le]
  have H := ClearedCoordinateParameterDegree.coefficient P.degree
    ((CoordinateFrozenCriticalElimination.denominator (data x hm r.critical).scales : ℤ) : x.sampler.scalarPrefix.carrier)
    (P.leading : x.sampler.scalarPrefix.carrier)
    (CoordinateFrozenCriticalElimination.numerators (data x hm r.critical).scales (heights x r))
    r.critical.offset.val (fit r).le 0 1
    (P.low.map (Int.castRingHom (Polynomial x.sampler.scalarPrefix.carrier)))
    ((PolynomialMapDegree.degree_le _ P.low).trans P.low_degree.le) Hlow HH (objective r) j k
  have HQ : ((CoordinateFrozenCriticalElimination.denominator (data x hm r.critical).scales : ℤ) : Polynomial x.sampler.scalarPrefix.carrier) =
      C ((CoordinateFrozenCriticalElimination.denominator (data x hm r.critical).scales : ℤ) : x.sampler.scalarPrefix.carrier) :=
    (Polynomial.C_eq_intCast _).symm
  have HA : (P.leading : Polynomial x.sampler.scalarPrefix.carrier) = C (P.leading : x.sampler.scalarPrefix.carrier) :=
    (Polynomial.C_eq_intCast _).symm
  unfold coordinate CoordinateFrozenCriticalElimination.polynomial
  rw [HQ, HA]
  simpa only [Nat.mul_one, Nat.zero_add, parameterDegree] using H

theorem coordinate_degree (x : State P S B m ι) (hm : m ≤ S) (r : Rule n)
    (j : Fin (n - r.critical.offset.val + 1)) :
    (coordinate x hm r j).natDegree ≤ PurePowerReductionBounds.dimension (n - r.critical.offset.val + 1) P.degree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  unfold coordinate CoordinateFrozenCriticalElimination.polynomial ClearedCoordinateCritical.annihilator
    PurePowerRelativeAnnihilator.polynomial
  rw [ScaledGradedReductionAnnihilator.coefficient,
    Polynomial.coeff_eq_zero_of_natDegree_lt, zero_mul]
  rw [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  exact hk

end LeanCanny.Algebra.IntegralMixedCriticalSweep
