/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CoerciveCriticalFibers
public import LeanCanny.Algebra.HomogenizationLayout
public import LeanCanny.Algebra.PolynomialMapDegree
public import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Projective equations for coercive critical coordinates

The gradient rows have pure leading powers, so no projective zero lies at
infinity when the perturbation parameter is nonzero. A coordinate row adds
T X₀−Xᵢ. The parameter coefficient ring is ℤ[T][s].
-/

@[expose] public section
namespace LeanCanny.Algebra.CoerciveCriticalHomogenization
open MvPolynomial
open scoped BigOperators Classical

abbrev Coefficient := Polynomial (Polynomial ℤ)
noncomputable def sParameter : Coefficient := Polynomial.X
noncomputable def tParameter : Coefficient := Polynomial.C Polynomial.X

variable {σ R : Type*} [Fintype σ] [CommRing R]

def nativeDegree (D : ℕ) : Option σ → ℕ
  | none => 1
  | some _ => 2 * D + 1

noncomputable def nativeSystem (q : MvPolynomial σ R) (D : ℕ) (s t : R)
    (coordinate : σ) : Option σ → MvPolynomial (Option σ) R
  | none => C t * X none - X (some coordinate)
  | some j => WeightedHomogenization.homogenize (fun _ => 1) (2 * D + 1) (pderiv j (q ^ 2)) +
      monomial (Finsupp.single (some j) (2 * D + 1)) (((2 * D + 2 : ℕ) : R) * s)

noncomputable def system (q : MvPolynomial σ ℤ) (D : ℕ) (coordinate : σ) :
    Option σ → MvPolynomial (Option σ) Coefficient :=
  nativeSystem (q.map (Int.castRingHom Coefficient)) D sParameter tParameter coordinate

noncomputable def parameterMap {K : Type*} [CommRing K] (s t : K) : Coefficient →+* K :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Int.castRingHom K) t) s

@[simp] theorem parameterMap_s {K : Type*} [CommRing K] (s t : K) :
    parameterMap s t sParameter = s := by simp [parameterMap, sParameter]
@[simp] theorem parameterMap_t {K : Type*} [CommRing K] (s t : K) :
    parameterMap s t tParameter = t := by simp [parameterMap, tParameter]

theorem homogeneous (q : MvPolynomial σ R) (D : ℕ) (s t : R) (coordinate : σ) (j : Option σ) :
    (nativeSystem q D s t coordinate j).IsHomogeneous (nativeDegree D j) := by
  cases j with
  | none => exact ((isHomogeneous_X R none).C_mul t).sub (isHomogeneous_X R (some coordinate))
  | some j =>
    apply IsHomogeneous.add
    · have h := WeightedHomogenization.homogeneous (fun _ : σ => 1) (2 * D + 1) (pderiv j (q ^ 2))
      have hw : WeightedHomogenization.weights (fun _ : σ => 1) = 1 := by
        funext i; cases i <;> rfl
      simpa only [IsHomogeneous, hw, nativeDegree] using h
    · exact isHomogeneous_monomial _ (Finsupp.degree_single _ _)

theorem map_nativeSystem {K : Type*} [CommRing K] (φ : R →+* K)
    (q : MvPolynomial σ R) (D : ℕ) (s t : R) (coordinate : σ) (j : Option σ) :
    (nativeSystem q D s t coordinate j).map φ =
      nativeSystem (q.map φ) D (φ s) (φ t) coordinate j := by
  cases j <;> simp [nativeSystem, WeightedHomogenization.map_homogenize, pderiv_map, map_ofNat]

theorem map_system {K : Type*} [CommRing K] (q : MvPolynomial σ ℤ) (D : ℕ)
    (coordinate : σ) (s t : K) (j : Option σ) :
    (system q D coordinate j).map (parameterMap s t) =
      nativeSystem (q.map (Int.castRingHom K)) D s t coordinate j := by
  rw [system, map_nativeSystem, parameterMap_s, parameterMap_t, MvPolynomial.map_map]
  have he : (parameterMap s t).comp (Int.castRingHom Coefficient) = Int.castRingHom K := Subsingleton.elim _ _
  rw [he]

/-- A lower degree polynomial vanishes at infinity after homogenization. -/
theorem homogenize_eval_infinity {K : Type*} [CommSemiring K] (p : MvPolynomial σ K)
    (N : ℕ) (hp : p.totalDegree < N) (x : Option σ → K) (hx : x none = 0) :
    eval x (WeightedHomogenization.homogenize (fun _ => 1) N p) = 0 := by
  rw [WeightedHomogenization.homogenize, map_sum]
  apply Finset.sum_eq_zero
  intro e he
  have hdeg := MvPolynomial.le_totalDegree (Finset.mem_filter.mp he).1
  change e.degree ≤ p.totalDegree at hdeg
  have hw := WeightedHomogenization.weight_le_degree (fun _ : σ => 1) (by simp) e
  have hn : N - Finsupp.weight (fun _ : σ => 1) e ≠ 0 := by omega
  rw [eval_monomial, Finsupp.prod_option_index]
  · simp [WeightedHomogenization.exponent, hx, zero_pow hn]
  · intro i; simp
  · intro i a b; exact pow_add _ _ _

omit [Fintype σ] in
/-- Evaluation of a homogeneous polynomial respects scalar multiplication. -/
theorem eval_scale {K : Type*} [CommSemiring K] (p : MvPolynomial σ K) (N : ℕ)
    (hp : p.IsHomogeneous N) (a : K) (x : σ → K) :
    eval (fun i => a * x i) p = a ^ N * eval x p := by
  conv_lhs => rw [p.as_sum, map_sum]
  conv_rhs => rw [p.as_sum, map_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  simp only [eval_monomial, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, ← hp.degree_eq_sum_deg_support he]
  ring

section Field
variable {K : Type*} [Field K]

theorem eval_chart (q : MvPolynomial σ K) (D : ℕ) (hD : q.totalDegree ≤ D)
    (s t : K) (coordinate : σ) (x : σ → K) (j : σ) :
    eval (fun i => i.elim 1 x) (nativeSystem q D s t coordinate (some j)) =
      eval x (pderiv j (CoerciveCriticalFibers.polynomial q D s)) := by
  have hp (e) (he : e ∈ (pderiv j (q ^ 2)).support) : Finsupp.weight (fun _ : σ => 1) e ≤ 2 * D + 1 :=
    (WeightedHomogenization.weight_le_degree _ (by simp) e).trans
      ((MvPolynomial.le_totalDegree he).trans (Nat.le_of_lt (CoerciveCriticalFibers.lower_degree q D hD j)))
  simp only [nativeSystem, map_add, CoerciveCriticalFibers.gradient_eq, eval_monomial,
    Finsupp.prod_single_index, pow_zero, CoerciveCriticalFibers.leadingScalar]
  have hc := WeightedHomogenization.eval_chart _ _ _ hp (RingHom.id K) x
  simp only [eval₂_id] at hc
  rw [hc]
  simp only [Option.elim_some]
  ring

theorem eval_infinity (q : MvPolynomial σ K) (D : ℕ) (hD : q.totalDegree ≤ D)
    (s t : K) (coordinate : σ) (x : Option σ → K) (hx : x none = 0) (j : σ) :
    eval x (nativeSystem q D s t coordinate (some j)) =
      (((2 * D + 2 : ℕ) : K) * s) * x (some j) ^ (2 * D + 1) := by
  simp only [nativeSystem, map_add,
    homogenize_eval_infinity _ _ (CoerciveCriticalFibers.lower_degree q D hD j) x hx,
    zero_add, eval_monomial, Finsupp.prod_single_index, pow_zero]

theorem no_zero_at_infinity [CharZero K] (q : MvPolynomial σ K) (D : ℕ)
    (hD : q.totalDegree ≤ D) (s t : K) (hs : s ≠ 0) (coordinate : σ)
    (x : Option σ → K) (hx : x none = 0)
    (hroot : ∀ j, eval x (nativeSystem q D s t coordinate j) = 0) : x = 0 := by
  funext j
  cases j with
  | none => exact hx
  | some j =>
    have h := hroot (some j)
    rw [eval_infinity q D hD s t coordinate x hx j] at h
    exact (pow_eq_zero_iff (by omega)).mp (mul_eq_zero.mp h |>.resolve_left
      (CoerciveCriticalFibers.leadingScalar_ne_zero D s hs))
/-- Over an infinite characteristic-zero field, a coordinate value can be
chosen outside the finite critical fiber, excluding every projective zero. -/
theorem exists_no_projective_root [CharZero K] [Infinite K]
    (q : MvPolynomial σ K) (D : ℕ) (hD : q.totalDegree ≤ D) (coordinate : σ) :
    ∃ t : K, ∀ x : Option σ → K,
      (∀ j, eval x (nativeSystem q D 1 t coordinate j) = 0) → x = 0 := by
  let S : Set (σ → K) := {x | ∀ j, eval x (pderiv j (CoerciveCriticalFibers.polynomial q D 1)) = 0}
  have hS : S.Finite := CoerciveCriticalFibers.finite_critical_points q D hD 1 one_ne_zero
  obtain ⟨t, ht⟩ := (hS.image (fun x => x coordinate)).exists_notMem
  refine ⟨t, ?_⟩
  intro y hy
  by_cases hzero : y none = 0
  · exact no_zero_at_infinity q D hD 1 t one_ne_zero coordinate y hzero hy
  · exfalso
    let x : σ → K := fun j => (y none)⁻¹ * y (some j)
    have hchart : (fun j : Option σ => (y none)⁻¹ * y j) = fun j => j.elim 1 x := by
      funext j
      cases j with
      | none => exact inv_mul_cancel₀ hzero
      | some j => rfl
    have hn (j : Option σ) : eval (fun j => j.elim 1 x) (nativeSystem q D 1 t coordinate j) = 0 := by
      rw [← hchart, eval_scale _ _ (homogeneous q D 1 t coordinate j), hy j, mul_zero]
    have hcritical : x ∈ S := by
      intro j
      rw [← eval_chart q D hD 1 t coordinate x j]
      exact hn (some j)
    have hcoord : x coordinate = t := by
      have hc := hn none
      simp only [nativeSystem, map_sub, map_mul, eval_C, eval_X, Option.elim_none,
        Option.elim_some, mul_one, sub_eq_zero] at hc
      exact hc.symm
    exact ht ⟨x, hcritical, hcoord⟩

end Field

section FinLayout
variable {n : ℕ}

def layout : Option (Fin n) ≃ Fin (n + 1) := HomogenizationLayout.variableEquiv (Equiv.refl _)
def finDegree (D : ℕ) (j : Fin (n + 1)) : ℕ := nativeDegree D (layout.symm j)
noncomputable def finSystem (q : MvPolynomial (Fin n) ℤ) (D : ℕ) (coordinate : Fin n)
    (j : Fin (n + 1)) : MvPolynomial (Fin (n + 1)) Coefficient :=
  rename layout (system q D coordinate (layout.symm j))

theorem finSystem_homogeneous (q : MvPolynomial (Fin n) ℤ) (D : ℕ) (coordinate : Fin n)
    (j : Fin (n + 1)) : (finSystem q D coordinate j).IsHomogeneous (finDegree D j) :=
  (homogeneous _ D sParameter tParameter coordinate (layout.symm j)).rename_isHomogeneous

theorem finDegree_pos (D : ℕ) (j : Fin (n + 1)) : 0 < finDegree D j := by
  unfold finDegree
  cases layout.symm j <;> simp [nativeDegree]

def finPoint {K : Type*} [One K] (x : Fin n → K) (j : Fin (n + 1)) : K :=
  (layout.symm j).elim 1 x

@[simp] theorem finPoint_homogeneous_coordinate {K : Type*} [One K] (x : Fin n → K) :
    finPoint x (layout none) = 1 := by simp [finPoint]

theorem finPoint_nonzero {K : Type*} [Zero K] [One K] [NeZero (1 : K)] (x : Fin n → K) :
    ∃ j, finPoint x j ≠ 0 := ⟨layout none, by simp⟩

theorem finDegree_le (D : ℕ) (j : Fin (n + 1)) : finDegree D j ≤ 2 * D + 1 := by
  unfold finDegree
  cases layout.symm j <;> simp [nativeDegree]

/-- Every actual critical point supplies a common projective zero at its
chosen coordinate parameter, with homogenizing coordinate equal to one. -/
theorem finSystem_critical_root {K : Type*} [Field K]
    (q : MvPolynomial (Fin n) ℤ) (D : ℕ) (hD : q.totalDegree ≤ D)
    (coordinate : Fin n) (s : K) (x : Fin n → K)
    (hx : ∀ i, eval x (pderiv i
      (CoerciveCriticalFibers.polynomial (q.map (Int.castRingHom K)) D s)) = 0)
    (j : Fin (n + 1)) :
    eval₂ (parameterMap s (x coordinate)) (finPoint x) (finSystem q D coordinate j) = 0 := by
  have hdc : (q.map (Int.castRingHom K)).totalDegree ≤ D :=
    (PolynomialMapDegree.degree_le _ _).trans hD
  simp only [finSystem, eval₂_rename, Function.comp_def, finPoint, Equiv.symm_apply_apply]
  rw [← eval_map, map_system]
  cases hj : layout.symm j with
  | none => simp [nativeSystem]
  | some i =>
    rw [eval_chart _ D hdc s (x coordinate) coordinate x i]
    exact hx i

/-- The actual integer parameter family has a complex specialization with no
nonzero projective common root. -/
theorem finSystem_exists_no_projective_root (q : MvPolynomial (Fin n) ℤ) (D : ℕ)
    (hD : q.totalDegree ≤ D) (coordinate : Fin n) :
    ∃ t : ℂ, ∀ x : Fin (n + 1) → ℂ,
      (∀ j, eval₂ (parameterMap 1 t) x (finSystem q D coordinate j) = 0) → x = 0 := by
  have hdc : (q.map (Int.castRingHom ℂ)).totalDegree ≤ D :=
    (PolynomialMapDegree.degree_le _ _).trans hD
  obtain ⟨t, ht⟩ := exists_no_projective_root (q.map (Int.castRingHom ℂ)) D hdc coordinate
  refine ⟨t, ?_⟩
  intro x hx
  have hy : (fun i => x (layout i)) = 0 := by
    apply ht
    intro j
    have hh := hx (layout j)
    simp only [finSystem, Equiv.symm_apply_apply, eval₂_rename] at hh
    rw [← eval_map, map_system] at hh
    exact hh
  funext j
  simpa only [Equiv.apply_symm_apply, Pi.zero_apply] using congrFun hy (layout.symm j)
/-- A real coordinate parameter can avoid every complex critical coordinate.
This permits real positive-definite Gram matrix specializations while retaining
the complex projective root criterion. -/
theorem finSystem_exists_real_no_complex_projective_root
    (q : MvPolynomial (Fin n) ℤ) (D : ℕ) (hD : q.totalDegree ≤ D) (coordinate : Fin n) :
    ∃ t : ℝ, ∀ x : Fin (n + 1) → ℂ,
      (∀ j, eval₂ (parameterMap 1 (t : ℂ)) x (finSystem q D coordinate j) = 0) → x = 0 := by
  let qc := q.map (Int.castRingHom ℂ)
  have hdc : qc.totalDegree ≤ D := (PolynomialMapDegree.degree_le _ _).trans hD
  let S : Set (Fin n → ℂ) := {x | ∀ j, eval x
    (pderiv j (CoerciveCriticalFibers.polynomial qc D 1)) = 0}
  have hS : S.Finite := CoerciveCriticalFibers.finite_critical_points qc D hdc 1 one_ne_zero
  have hcoords := hS.image (fun x => x coordinate)
  have hreal : ((fun t : ℝ => (t : ℂ)) ⁻¹' ((fun x => x coordinate) '' S)).Finite :=
    hcoords.preimage Complex.ofReal_injective.injOn
  obtain ⟨t, ht⟩ := hreal.exists_notMem
  have hnative : ∀ y : Option (Fin n) → ℂ,
      (∀ j, eval y (nativeSystem qc D 1 (t : ℂ) coordinate j) = 0) → y = 0 := by
    intro y hy
    by_cases hzero : y none = 0
    · exact no_zero_at_infinity qc D hdc 1 (t : ℂ) one_ne_zero coordinate y hzero hy
    · exfalso
      let z : Fin n → ℂ := fun j => (y none)⁻¹ * y (some j)
      have hchart : (fun j : Option (Fin n) => (y none)⁻¹ * y j) = fun j => j.elim 1 z := by
        funext j
        cases j with
        | none => exact inv_mul_cancel₀ hzero
        | some j => rfl
      have hn (j : Option (Fin n)) :
          eval (fun j => j.elim 1 z) (nativeSystem qc D 1 (t : ℂ) coordinate j) = 0 := by
        rw [← hchart, eval_scale _ _ (homogeneous qc D 1 (t : ℂ) coordinate j), hy j, mul_zero]
      have hcritical : z ∈ S := by
        intro j
        rw [← eval_chart qc D hdc 1 (t : ℂ) coordinate z j]
        exact hn (some j)
      have hcoord : z coordinate = (t : ℂ) := by
        have hc := hn none
        simp only [nativeSystem, map_sub, map_mul, eval_C, eval_X, Option.elim_none,
          Option.elim_some, mul_one, sub_eq_zero] at hc
        exact hc.symm
      exact ht ⟨z, hcritical, hcoord⟩
  refine ⟨t, ?_⟩
  intro x hx
  have hy : (fun i => x (layout i)) = 0 := by
    apply hnative
    intro j
    have hh := hx (layout j)
    simp only [finSystem, Equiv.symm_apply_apply, eval₂_rename] at hh
    rw [← eval_map, map_system] at hh
    exact hh
  funext j
  simpa only [Equiv.apply_symm_apply, Pi.zero_apply] using congrFun hy (layout.symm j)

end FinLayout

end LeanCanny.Algebra.CoerciveCriticalHomogenization
