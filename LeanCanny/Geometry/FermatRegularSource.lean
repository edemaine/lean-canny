/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.CriticalRegularLevel
public import LeanCanny.Algebra.FermatBoundedCriticalDirection
public import LeanCanny.Algebra.FermatGenericSliceDirection

/-! # Constructed regular rational sources with bounded critical directions

Shifting an integer pure-power leading polynomial by the explicitly selected
dyadic level supplies the extension-field regularity needed by the bounded
direction theorem. No regular-level or direction certificate is assumed.
-/

@[expose] public section
namespace LeanCanny.Geometry.FermatRegularSource
open MvPolynomial
open LeanCanny.Algebra
open FermatCriticalHomogenization
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

def width (n N : ℕ) : ℕ :=
  (Macaulay.level (AffineCoordinateSystem.degrees (CriticalValueSystem.degrees (n + 1) N))).size

theorem width_eq (n N : ℕ) : width n N = (N - 1 + (n + 1) * (N - 1 - 1) + 1).size := by
  unfold width Macaulay.level
  rw [Fin.sum_univ_succ]
  simp only [AffineCoordinateSystem.degrees, Fin.cons_zero, Fin.cons_succ, Nat.sub_self, Nat.zero_add]
  rw [Fin.sum_univ_succ]
  simp [CriticalValueSystem.degrees]

theorem width_le (n N : ℕ) (hN : 1 < N) : width n N ≤ (n + 3).size + N.size + 1 := by
  let d := AffineCoordinateSystem.degrees (CriticalValueSystem.degrees (n + 1) N)
  have hd (j : Fin (n + 3)) : d j ≤ N := by
    refine Fin.cases (by simpa [d, AffineCoordinateSystem.degrees] using hN.le)
      (fun j => ?_) j
    exact Fin.cases le_rfl (fun _ => Nat.sub_le N 1) j
  have hsum : (∑ j : Fin (n + 3), (d j - 1)) ≤ (n + 3) * N :=
    (Finset.sum_le_sum fun j _ => (Nat.sub_le _ _).trans (hd j)).trans_eq (by simp)
  have hprod : (n + 3) * N < 2 ^ ((n + 3).size + N.size) := by
    rw [pow_add]
    exact (Nat.mul_le_mul_right N (Nat.lt_size_self _).le).trans_lt
      (Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self N) (by positivity))
  have hlevel : Macaulay.level d ≤ (n + 3) * N + 1 := Nat.add_le_add_right hsum 1
  apply Nat.size_le.mpr
  change Macaulay.level d < _
  rw [pow_succ]
  have hpos : 0 < 2 ^ ((n + 3).size + N.size) := by positivity
  omega

theorem exponent_size_le (n N b : ℕ) (hN : 1 < N) :
    (CriticalRegularLevel.exponent (n + 1) N (width n N) b).size ≤
      4 * ((n + 3) * (n + N.size + 4)) + b.size + N.size + 24 := by
  have hw := width_le n N hN
  have hn : (n + 3).size ≤ n + 3 := Nat.size_le.mpr Nat.lt_two_pow_self
  have hwidth : width n N ≤ n + N.size + 4 := by omega
  exact (CriticalRegularLevel.exponent_size_le (n + 1) N (width n N) b).trans
    (Nat.add_le_add_right (Nat.add_le_add_right
      (Nat.add_le_add_right (Nat.mul_le_mul_left 4 (Nat.mul_le_mul_left (n + 3) hwidth)) _) _) _)

noncomputable def lower (low : MvPolynomial (Fin (n + 1)) ℤ) (N b : ℕ) :
    MvPolynomial (Fin (n + 1)) ℚ :=
  low.map (Int.castRingHom ℚ) - C (CriticalRegularLevel.level (n + 1) N (width n N) b)

theorem mass_le (low : MvPolynomial (Fin (n + 1)) ℤ) (a : ℤ) (N b : ℕ)
    (hlow : MvMass.mass low ≤ 2 ^ b) (ha : a.natAbs ≤ 2 ^ b) :
    MvMass.mass (polynomial low a N) ≤ 2 ^ (b + (n + 2).size) := by
  have hs : MvMass.mass (∑ j : Fin (n + 1), (X j : MvPolynomial (Fin (n + 1)) ℤ) ^ N) ≤ n + 1 := by
    apply (MvMass.sum_le _ _).trans
    apply (Finset.sum_le_sum fun j _ => MvMass.pow_le (X j) N).trans
    simp
  have hCa : MvMass.mass (C a : MvPolynomial (Fin (n + 1)) ℤ) ≤ 2 ^ b := by
    simpa only [MvMass.C] using ha
  apply (MvMass.add_le _ _).trans
  apply (Nat.add_le_add hlow ((MvMass.mul_le _ _).trans (Nat.mul_le_mul hCa hs))).trans
  calc
    2 ^ b + 2 ^ b * (n + 1) = (n + 2) * 2 ^ b := by ring
    _ ≤ 2 ^ (n + 2).size * 2 ^ b := Nat.mul_le_mul_right _ (Nat.lt_size_self _).le
    _ = _ := by rw [← pow_add, Nat.add_comm]

theorem square_mass_le (q : MvPolynomial (Fin (n + 1)) ℤ) (a : ℤ) (N b : ℕ)
    (hq : MvMass.mass q ≤ 2 ^ b) (ha : a.natAbs ≤ 2 ^ b) :
    MvMass.mass (polynomial (q ^ 2) a N) ≤ 2 ^ (2 * b + (n + 2).size) := by
  apply mass_le
  · exact (MvMass.pow_le q 2).trans ((Nat.pow_le_pow_left hq 2).trans_eq (by rw [← pow_mul]; congr 1; omega))
  · exact ha.trans (Nat.pow_le_pow_right (by decide) (by omega))

theorem lower_degree (low : MvPolynomial (Fin (n + 1)) ℤ) (N b : ℕ)
    (hlow : low.totalDegree < N) : (lower low N b).totalDegree < N := by
  apply (totalDegree_sub _ _).trans_lt
  apply max_lt
  · exact (PolynomialMapDegree.degree_le _ low).trans_lt hlow
  · simp only [totalDegree_C]
    omega

theorem polynomial_eq (low : MvPolynomial (Fin (n + 1)) ℤ) (a : ℤ) (N b : ℕ) :
    polynomial (lower low N b) (a : ℚ) N =
      (polynomial low a N).map (Int.castRingHom ℚ) -
        C (CriticalRegularLevel.level (n + 1) N (width n N) b) := by
  rw [map_polynomial]
  simp only [polynomial, lower, Int.coe_castRingHom]
  ring

theorem regular {K : Type*} [Field K] [Algebra ℚ K]
    (low : MvPolynomial (Fin (n + 1)) ℤ) (a : ℤ) (N b : ℕ)
    (hlow : low.totalDegree < N) (ha : a ≠ 0) (hN : 1 < N)
    (hp : MvMass.mass (polynomial low a N) ≤ 2 ^ b)
    (x : Fin (n + 1) → K) (hx : aeval x (polynomial (lower low N b) (a : ℚ) N) = 0) :
    ∃ j, aeval x (pderiv j (polynomial (lower low N b) (a : ℚ) N)) ≠ 0 := by
  have hm : (algebraMap ℚ K).comp (Int.castRingHom ℚ) = Int.castRingHom K :=
    RingHom.ext_int _ _
  have heval (q : MvPolynomial (Fin (n + 1)) ℤ) :
      aeval x (q.map (Int.castRingHom ℚ)) = q.eval₂ (Int.castRingHom K) x := by
    change eval₂ (algebraMap ℚ K) x (q.map (Int.castRingHom ℚ)) = _
    rw [eval₂_map, hm]
  rw [polynomial_eq, map_sub, aeval_C, heval] at hx
  obtain ⟨j, hj⟩ := CriticalRegularLevel.regular low a N (width n N) b hlow ha hN
    (Nat.lt_size_self _) hp x (sub_eq_zero.mp hx)
  refine ⟨j, ?_⟩
  rwa [polynomial_eq, map_sub, pderiv_C, sub_zero, pderiv_map, heval]

/-- The integer direction bound now applies to a constructed regular source. -/
theorem exists_bounded_direction (low : MvPolynomial (Fin (n + 1)) ℤ) (a : ℤ) (N b : ℕ)
    (hlow : low.totalDegree < N) (ha : a ≠ 0) (hN : 1 < N)
    (hp : MvMass.mass (polynomial low a N) ≤ 2 ^ b) :
    ∃ v : Fin n → ℕ, (∀ i, v i ≤ FermatBoundedCriticalDirection.allowance n N) ∧
      ∀ (L : Type) [Field L] [Algebra ℚ L] (x : Fin (n + 1) → L),
        (∀ j, (FermatCriticalBadSystem.equations (lower low N b) (a : ℚ) N j).eval₂
          (eval₂Hom (algebraMap ℚ L) (fun i => (v i : L))) x = 0) →
        (FermatCriticalBadSystem.jacobian (lower low N b) (a : ℚ) N).eval₂
          (eval₂Hom (algebraMap ℚ L) (fun i => (v i : L))) x ≠ 0 :=
  FermatBoundedCriticalDirection.exists_bounded (lower low N b) (a : ℚ) (Int.cast_ne_zero.mpr ha)
    N (lower_degree low N b hlow) hN (fun _ _ _ => regular low a N b hlow ha hN hp)

/-- The same source construction supplies a bounded direction for its
generic coordinate slices, in one fewer spatial dimension. -/
theorem exists_bounded_slice_direction (low : MvPolynomial (Fin (n + 2)) ℤ) (a : ℤ) (N b : ℕ)
    (hlow : low.totalDegree < N) (ha : a ≠ 0) (hN : 1 < N)
    (hp : MvMass.mass (polynomial low a N) ≤ 2 ^ b) :
    let F := FermatGenericSliceDirection.GenericField ℚ
    let low' := FermatGenericSliceDirection.lower (lower low N b) (a : ℚ) N
    ∃ v : Fin n → ℕ, (∀ i, v i ≤ FermatBoundedCriticalDirection.allowance n N) ∧
      ∀ (L : Type) [Field L] [Algebra F L] (x : Fin (n + 1) → L),
        (∀ j, (FermatCriticalBadSystem.equations low' (algebraMap ℚ F a) N j).eval₂
          (eval₂Hom (algebraMap F L) (fun i => (v i : L))) x = 0) →
        (FermatCriticalBadSystem.jacobian low' (algebraMap ℚ F a) N).eval₂
          (eval₂Hom (algebraMap F L) (fun i => (v i : L))) x ≠ 0 := by
  dsimp only
  obtain ⟨v, hv, hgood⟩ := FermatGenericSliceDirection.exists_bounded (lower low N b) (a : ℚ) (Int.cast_ne_zero.mpr ha)
    N (lower_degree low N b hlow) hN (fun _ _ _ => regular low a N b hlow ha hN hp)
  refine ⟨v, hv, ?_⟩
  intro L _ _ x hx
  simp only [map_intCast] at hgood hx ⊢
  exact hgood L x hx

end LeanCanny.Geometry.FermatRegularSource
