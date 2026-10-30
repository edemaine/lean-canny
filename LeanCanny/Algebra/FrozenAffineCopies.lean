/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.RetainedParameterPolynomial
public import LeanCanny.Algebra.HomogenizationAtInfinity
public import LeanCanny.Algebra.HomogenizationRename
public import LeanCanny.Algebra.AffineFiniteCoordinates
public import Mathlib.Algebra.Polynomial.EraseLead
public import Mathlib.Logic.Equiv.Fin.Basic

/-! # Affine copies with one algebraically frozen height

One retained parameter equation freezes the common height of selected copies
of an affine system. A separate copy may still vary with an external height.
This supplies the integer systems for endpoint midpoint comparisons.
-/

@[expose] public section
namespace LeanCanny.Algebra.FrozenAffineCopies
open MvPolynomial WeightedHomogenization
open scoped Classical
set_option maxHeartbeats 300000
variable {n m : ℕ}

def block (k : Fin m) (i : Fin n) : Fin (m * n + 1) := (finProdFinEquiv (k, i)).succ

theorem block_eq_iff (k l : Fin m) (i j : Fin n) : block k i = block l j ↔ k = l ∧ i = j := by
  change (finProdFinEquiv (k, i)).succ = (finProdFinEquiv (l, j)).succ ↔ _
  rw [Fin.succ_inj, Equiv.apply_eq_iff_eq, Prod.mk.injEq]

def point {K : Type*} (a : K) (x : Fin m → Fin n → K) : Fin (m * n + 1) → K :=
  Fin.cons a (fun j => x (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2)

@[simp] theorem point_zero {K : Type*} (a : K) (x : Fin m → Fin n → K) : point a x 0 = a := rfl

@[simp] theorem point_block {K : Type*} (a : K) (x : Fin m → Fin n → K) (k : Fin m) (i : Fin n) :
    point a x (block k i) = x k i := by
  simp only [point, block, Fin.cons_succ, Equiv.symm_apply_apply]

noncomputable def row (p : Fin n → MvPolynomial (Fin n) ℤ) (h : Fin n)
    (frozen : Fin m → Bool) (k : Fin m) (i : Fin n) : MvPolynomial (Fin (m * n + 1)) ℤ :=
  rename (block k) (p i) - if frozen k = true ∧ i = h then X 0 else 0

noncomputable def system (p : Fin n → MvPolynomial (Fin n) ℤ) (E : Polynomial ℤ)
    (h : Fin n) (frozen : Fin m → Bool) :
    Fin (m * n + 1) → MvPolynomial (Fin (m * n + 1)) ℤ :=
  Fin.cons (IndexedMultivariateRational.parameter (m * n) E)
    (fun j => row p h frozen (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2)

def degrees (d : Fin n → ℕ) (e : ℕ) : Fin (m * n + 1) → ℕ :=
  Fin.cons e (fun j => d (finProdFinEquiv.symm j).2)

theorem system_zero (p : Fin n → MvPolynomial (Fin n) ℤ) (E : Polynomial ℤ)
    (h : Fin n) (frozen : Fin m → Bool) : system p E h frozen 0 = IndexedMultivariateRational.parameter (m * n) E := rfl

theorem system_block (p : Fin n → MvPolynomial (Fin n) ℤ) (E : Polynomial ℤ)
    (h : Fin n) (frozen : Fin m → Bool) (k : Fin m) (i : Fin n) :
    system p E h frozen (block k i) = row p h frozen k i := by
  simp only [system, block, Fin.cons_succ, Equiv.symm_apply_apply]

theorem row_eval {K : Type*} [CommRing K] (phi : ℤ →+* K)
    (p : Fin n → MvPolynomial (Fin n) ℤ) (h : Fin n) (frozen : Fin m → Bool)
    (k : Fin m) (i : Fin n) (z : Fin (m * n + 1) → K) :
    (row p h frozen k i).eval₂ phi z =
      (p i).eval₂ phi (z ∘ block k) - if frozen k = true ∧ i = h then z 0 else 0 := by
  simp only [row, eval₂_sub, eval₂_rename]
  split_ifs <;> simp only [eval₂_X, eval₂_zero]

theorem row_degree (p : Fin n → MvPolynomial (Fin n) ℤ) (h : Fin n)
    (frozen : Fin m → Bool) (d : Fin n → ℕ) (hp : ∀ i, (p i).totalDegree ≤ d i)
    (hd : ∀ i, 0 < d i) (k : Fin m) (i : Fin n) : (row p h frozen k i).totalDegree ≤ d i := by
  apply (totalDegree_sub _ _).trans
  apply max_le
  · exact (totalDegree_rename_le _ _).trans (hp i)
  · split_ifs
    · simp only [totalDegree_X]
      exact hd i
    · simp

theorem degree_bound (p : Fin n → MvPolynomial (Fin n) ℤ) (E : Polynomial ℤ) (h : Fin n)
    (frozen : Fin m → Bool) (d : Fin n → ℕ) (hp : ∀ i, (p i).totalDegree ≤ d i) (hd : ∀ i, 0 < d i)
    (j : Fin (m * n + 1)) : (system p E h frozen j).totalDegree ≤ degrees d E.natDegree j := by
  refine Fin.cases ?_ (fun r => ?_) j
  · exact IndexedMultivariateRational.parameter_degree _ _
  · exact row_degree p h frozen d hp hd _ _

theorem degrees_pos (d : Fin n → ℕ) (e : ℕ) (hd : ∀ i, 0 < d i) (he : 0 < e)
    (j : Fin (m * n + 1)) : 0 < degrees d e j :=
  Fin.cases he (fun r => hd (finProdFinEquiv.symm r).2) j

theorem zero_iff {K : Type*} [CommRing K] (phi : ℤ →+* K)
    (p : Fin n → MvPolynomial (Fin n) ℤ) (E : Polynomial ℤ) (h : Fin n)
    (frozen : Fin m → Bool) (z : Fin (m * n + 1) → K) :
    (∀ j, (system p E h frozen j).eval₂ phi z = 0) ↔
      E.eval₂ phi (z 0) = 0 ∧ ∀ k i, (p i).eval₂ phi (z ∘ block k) =
        if frozen k = true ∧ i = h then z 0 else 0 := by
  constructor
  · intro H
    constructor
    · simpa only [system_zero, IndexedMultivariateRational.eval_parameter] using H 0
    · intro k i
      have Hi := H (block k i)
      rwa [system_block, row_eval, sub_eq_zero] at Hi
  · rintro ⟨hE, hp⟩ j
    refine Fin.cases ?_ (fun r => ?_) j
    · simpa only [system_zero, IndexedMultivariateRational.eval_parameter] using hE
    · change (row p h frozen (finProdFinEquiv.symm r).1 (finProdFinEquiv.symm r).2).eval₂ phi z = 0
      rw [row_eval, sub_eq_zero]
      exact hp _ _

noncomputable def midpoint (i : Fin n) : MvPolynomial (Fin (3 * n + 1)) ℤ :=
  C 2 * X (block (0 : Fin 3) i) - X (block (1 : Fin 3) i) - X (block (2 : Fin 3) i)

theorem midpoint_eval {K : Type*} [CommRing K] (phi : ℤ →+* K) (i : Fin n) (z : Fin (3 * n + 1) → K) :
    (midpoint i).eval₂ phi z =
      2 * z (block (0 : Fin 3) i) - z (block (1 : Fin 3) i) - z (block (2 : Fin 3) i) := by
  simp [midpoint]

theorem midpoint_degree (i : Fin n) : (midpoint i).totalDegree ≤ 1 := by
  apply (totalDegree_sub _ _).trans
  apply max_le _ (by simp)
  apply (totalDegree_sub _ _).trans
  apply max_le _ (by simp)
  apply (totalDegree_mul _ _).trans
  simp only [totalDegree_C, totalDegree_X, zero_add, le_refl]

theorem parameter_at_infinity (E : Polynomial ℤ) (hE : 0 < E.natDegree)
    (y : Option (Fin (n + 1)) → ℂ) (hy : y none = 0) :
    (homogenize (fun _ => 1) E.natDegree (IndexedMultivariateRational.parameter n E)).eval₂
      (Int.castRingHom ℂ) y = (E.leadingCoeff : ℂ) * y (some 0) ^ E.natDegree := by
  have hlow : (IndexedMultivariateRational.parameter n E.eraseLead).totalDegree < E.natDegree := by
    apply (IndexedMultivariateRational.parameter_degree _ _).trans_lt
    by_cases hz : E.eraseLead = 0
    · simpa only [hz, Polynomial.natDegree_zero] using hE
    · exact Polynomial.lt_natDegree_of_mem_eraseLead_support (Polynomial.natDegree_mem_support_of_nonzero hz)
  have he : IndexedMultivariateRational.parameter n E =
      C E.leadingCoeff * X 0 ^ E.natDegree + IndexedMultivariateRational.parameter n E.eraseLead := by
    have H := congrArg (IndexedMultivariateRational.parameter n) E.eraseLead_add_C_mul_X_pow
    simp only [map_add, map_mul, map_pow, IndexedMultivariateRational.parameter,
      Polynomial.coe_eval₂RingHom, Polynomial.eval₂_C, Polynomial.eval₂_X] at H
    exact H.symm.trans (add_comm _ _)
  have hH : (C E.leadingCoeff * X (0 : Fin (n + 1)) ^ E.natDegree).IsHomogeneous E.natDegree := by
    simpa only [one_mul] using ((isHomogeneous_X (R := ℤ) (0 : Fin (n + 1))).pow E.natDegree).C_mul E.leadingCoeff
  rw [he, HomogenizationAtInfinity.eval_leading (Int.castRingHom ℂ) _ _ _ hlow hH y hy]
  simp only [eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, Int.coe_castRingHom, Function.comp_apply]

theorem homogenized_variable_zero (D : ℕ) (a : Fin (n + 1)) (y : Option (Fin (n + 1)) → ℂ)
    (ha : y (some a) = 0) :
    (homogenize (fun _ => 1) D (X a : MvPolynomial (Fin (n + 1)) ℤ)).eval₂ (Int.castRingHom ℂ) y = 0 := by
  change (homogenize (fun _ => 1) D (monomial (Finsupp.single a 1) 1)).eval₂ (Int.castRingHom ℂ) y = 0
  rw [homogenize_monomial]
  simp only [Finsupp.weight_single, smul_eq_mul, mul_one]
  split_ifs
  · simp only [eval₂_monomial, exponent, Finsupp.weight_single, smul_eq_mul, mul_one, map_one]
    rw [Finsupp.prod_option_index]
    · simp only [Finsupp.optionElim_apply_none, Finsupp.some_optionElim]
      rw [Finsupp.prod_single_index (h := fun i e => y (some i) ^ e) (pow_zero _)]
      simp only [pow_one, ha, mul_zero]
    · intro i
      exact pow_zero _
    · intro i a b
      exact pow_add _ _ _
  · simp only [eval₂_zero]

theorem noInfinity (p : Fin n → MvPolynomial (Fin n) ℤ) (E : Polynomial ℤ)
    (h : Fin n) (frozen : Fin m → Bool) (d : Fin n → ℕ)
    (hE : 0 < E.natDegree) (hp : AffineFiniteCoordinates.NoInfinity p d) :
    AffineFiniteCoordinates.NoInfinity (system p E h frozen) (degrees d E.natDegree) := by
  intro y hy hz
  have ha : y (some 0) = 0 := by
    have H := hz 0
    change (homogenize (fun _ => 1) E.natDegree (IndexedMultivariateRational.parameter (m * n) E)).eval₂
      (Int.castRingHom ℂ) y = 0 at H
    rw [parameter_at_infinity E hE y hy] at H
    have he : E ≠ 0 := Polynomial.ne_zero_of_natDegree_gt hE
    have hl : (E.leadingCoeff : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (Polynomial.leadingCoeff_ne_zero.mpr he)
    exact (pow_eq_zero_iff hE.ne').mp ((mul_eq_zero.mp H).resolve_left hl)
  have hb (k : Fin m) : (fun j : Option (Fin n) => j.elim (y none) (fun i => y (some (block k i)))) = 0 := by
    apply hp
    · exact hy
    · intro i
      have H := hz (block k i)
      have hd : degrees d E.natDegree (block k i) = d i := by
        simp only [degrees, block, Fin.cons_succ, Equiv.symm_apply_apply]
      rw [system_block, hd, row, homogenize_sub, eval₂_sub] at H
      have hs : (homogenize (fun _ => 1) (d i)
          (if frozen k = true ∧ i = h then X 0 else 0 : MvPolynomial (Fin (m * n + 1)) ℤ)).eval₂
          (Int.castRingHom ℂ) y = 0 := by
        split_ifs
        · exact homogenized_variable_zero _ _ _ ha
        · rw [homogenize_zero, eval₂_zero]
      rw [hs, sub_zero, homogenize_rename, eval₂_rename] at H
      have he : y ∘ Option.map (block k) =
          (fun j : Option (Fin n) => j.elim (y none) (fun i => y (some (block k i)))) := by
        funext j
        cases j <;> rfl
      rwa [he] at H
  funext j
  cases j with
  | none => exact hy
  | some j =>
    refine Fin.cases ha (fun r => ?_) j
    let k := (finProdFinEquiv.symm r).1
    let i := (finProdFinEquiv.symm r).2
    have H := congrFun (hb k) (some i)
    change y (some (finProdFinEquiv (finProdFinEquiv.symm r)).succ) = 0 at H
    simpa only [Equiv.apply_symm_apply, Pi.zero_apply] using H

end LeanCanny.Algebra.FrozenAffineCopies
