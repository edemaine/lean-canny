/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ClearedCoordinateCriticalBounds
public import LeanCanny.Algebra.CommonIntegerDenominator
public import LeanCanny.Algebra.PhysicalPowerCriticalCone

/-! # Relative scalar candidates at actual frozen critical points

Nonzero integer coordinate scales give one common denominator. The frozen
slice reconstructs the exact original point. Its relative coordinate
annihilator consequently vanishes at every free critical coordinate, with
specialized degree independent of the old algebra rank and scalar powers.
-/

@[expose] public section
namespace LeanCanny.Algebra.CoordinateFrozenCriticalElimination
open MvPolynomial
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {A K : Type*} [CommRing A] [Field K] [CharZero K] {n k : ℕ}

def denominator (scales : Fin (n + 1) → ℤ) : ℤ :=
  CommonIntegerDenominator.denominator Finset.univ scales

noncomputable def numerators (scales : Fin (n + 1) → ℤ) (H : Fin (n + 1) → A) (i : ℕ) : A :=
  if hi : i < n + 1 then CommonIntegerDenominator.numerator Finset.univ scales H ⟨i, hi⟩ else 0

theorem denominator_ne_zero (scales : Fin (n + 1) → ℤ) (hc : ∀ i, scales i ≠ 0) : denominator scales ≠ 0 :=
  CommonIntegerDenominator.denominator_ne_zero Finset.univ scales (fun i _ => hc i)

theorem point_eq (φ : A →+* K) (scales : Fin (n + 1) → ℤ) (hc : ∀ i, scales i ≠ 0)
    (H : Fin (n + 1) → A) (offset : ℕ) (hfit : offset + (k + 1) = n + 1) (x : Fin (n + 1) → K)
    (hx : ∀ i, i.val < offset → (scales i : K) * x i = φ (H i)) :
    ClearedCoordinateBlock.point φ (denominator scales : A) (numerators scales H) offset
      (fun j => x (ClearedCoordinateCritical.freeIndex offset hfit.le j)) = x := by
  funext i
  rw [ClearedCoordinateBlock.point]
  split_ifs with hi
  · apply congrArg x
    apply Fin.ext
    change offset + (i.val - offset) = i.val
    omega
  · have HF : i.val < offset := by have := i.isLt; omega
    rw [numerators, dite_eq_left i.isLt, map_intCast]
    have HE := CommonIntegerDenominator.recover φ Finset.univ scales H (fun j _ => hc j) i (Finset.mem_univ i)
    apply HE.trans
    rw [← hx i HF]
    exact mul_div_cancel_left₀ (x i) (Int.cast_ne_zero.mpr (hc i))

noncomputable def polynomial (D : ℕ) (scales : Fin (n + 1) → ℤ) (H : Fin (n + 1) → A)
    (offset : ℕ) (hfit : offset + (k + 1) = n + 1)
    (low : MvPolynomial (Fin (n + 1)) A) (a : A) (r j : Fin (k + 1)) : Polynomial A :=
  ClearedCoordinateCritical.annihilator D (denominator scales : A) (numerators scales H) offset hfit.le low a r j

theorem root [Nontrivial A] (φ : A →+* K) (D : ℕ) (hD : 2 ≤ D)
    (scales : Fin (n + 1) → ℤ) (hc : ∀ i, scales i ≠ 0) (H : Fin (n + 1) → A)
    (offset : ℕ) (hfit : offset + (k + 1) = n + 1) (low : MvPolynomial (Fin (n + 1)) A)
    (a : A) (hlow : low.totalDegree < D) (r : Fin (k + 1)) (x : Fin (n + 1) → K)
    (hfrozen : ∀ i, i.val < offset → (scales i : K) * x i = φ (H i))
    (hp : (FermatCriticalHomogenization.polynomial low a D).eval₂ φ x = 0)
    (hg : ∀ i : Fin (k + 1), i ≠ r →
      (pderiv (ClearedCoordinateCritical.freeIndex offset hfit.le i)
        (FermatCriticalHomogenization.polynomial low a D)).eval₂ φ x = 0) (j : Fin (k + 1)) :
    (polynomial D scales H offset hfit low a r j).eval₂ φ
      (x (ClearedCoordinateCritical.freeIndex offset hfit.le j)) = 0 := by
  have HE := point_eq φ scales hc H offset hfit x hfrozen
  have HQ : φ (denominator scales : A) ≠ 0 := by
    rw [map_intCast]
    exact Int.cast_ne_zero.mpr (denominator_ne_zero scales hc)
  exact ClearedCoordinateCritical.annihilator_root φ D (denominator scales : A) (numerators scales H)
    offset hfit.le low a hD hlow HQ r (fun i => x (ClearedCoordinateCritical.freeIndex offset hfit.le i))
    (by rw [HE]; exact hp) (fun i hi => by rw [HE]; exact hg i hi) j

theorem specialized_degree (φ : A →+* K) (D : ℕ) (hD : 0 < D)
    (scales : Fin (n + 1) → ℤ) (hc : ∀ i, scales i ≠ 0) (H : Fin (n + 1) → A)
    (offset : ℕ) (hfit : offset + (k + 1) = n + 1) (low : MvPolynomial (Fin (n + 1)) A)
    (a : A) (ha : φ a ≠ 0) (r j : Fin (k + 1)) :
    ((polynomial D scales H offset hfit low a r j).map φ).natDegree =
      PurePowerReductionBounds.dimension (k + 1) D := by
  apply ClearedCoordinateCritical.annihilator_specialized_degree φ D _ _ offset hfit.le low a hD ha
  rw [map_intCast]
  exact Int.cast_ne_zero.mpr (denominator_ne_zero scales hc)

omit [CharZero K] in
theorem free_gradient_zero (φ : ℤ →+* K) (p : MvPolynomial (Fin (n + 1)) ℤ)
    (b : ℤ) (scales : Fin (n + 1) → ℤ) (s : Finset (Fin (n + 1))) (r : Fin (n + 1))
    (x : Fin (n + 1) → K) (mu : Fin (n + 2) → K)
    (hg : ∀ i, (pderiv i p).eval₂ φ x =
      ∑ j, φ (PhysicalPowerCriticalRows.coordinateNormals b scales r j i) * mu j)
    (hm : ∀ i, i ∉ s → mu i.succ = 0) (i : Fin (n + 1)) (hi : i ∉ s) (hir : i ≠ r) :
    (pderiv i p).eval₂ φ x = 0 := by
  rw [hg i]
  have HE := PhysicalPowerCriticalRows.normal_power_sum φ b scales r i mu 1
  simp only [pow_one] at HE
  rw [HE, ite_eq_right hir, hm i hi, mul_zero, add_zero]

end LeanCanny.Algebra.CoordinateFrozenCriticalElimination
