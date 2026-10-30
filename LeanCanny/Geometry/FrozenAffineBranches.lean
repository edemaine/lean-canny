/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FrozenAffineCopies
public import LeanCanny.Geometry.AffineShiftCoordinates
public import Mathlib.Topology.Separation.Connected

/-! # Frozen coordinates stay constant on retained branches

A continuous branch satisfying a fixed nonzero parameter equation cannot
change its parameter root. Every frozen affine copy is then constant too,
since exclusion at infinity gives finite fibers, including singular ones.
-/

@[expose] public section
namespace LeanCanny.Geometry.FrozenAffineBranches
open Set LeanCanny.Algebra
open scoped Classical
set_option maxHeartbeats 300000

theorem eq_of_finite_image {E : Type*} [TopologicalSpace E] [T1Space E] {a b : ℝ}
    (f : ℝ → E) (hc : ContinuousOn f (Ioo a b)) (hf : (f '' Ioo a b).Finite)
    (s t : Ioo a b) : f s.val = f t.val := by
  by_contra hn
  have hp := isPreconnected_Ioo.image f hc
  exact hf.not_infinite (hp.infinite_of_nontrivial
    ⟨f s.val, ⟨s.val, s.property, rfl⟩, f t.val, ⟨t.val, t.property, rfl⟩, hn⟩)

theorem parameter_constant (E : Polynomial ℤ) (hE : E ≠ 0) {a b : ℝ}
    (f : ℝ → ℝ) (hc : ContinuousOn f (Ioo a b))
    (hr : ∀ t ∈ Ioo a b, E.eval₂ (Int.castRingHom ℝ) (f t) = 0) (s t : Ioo a b) : f s.val = f t.val := by
  have hn : E.map (Int.castRingHom ℝ) ≠ 0 :=
    (Polynomial.map_ne_zero_iff (Int.cast_injective (α := ℝ))).mpr hE
  apply eq_of_finite_image f hc ?_ s t
  apply (Polynomial.finite_setOfPred_isRoot hn).subset
  rintro x ⟨u, hu, rfl⟩
  simpa only [Set.mem_ofPred_eq, Polynomial.IsRoot, Polynomial.eval_map] using hr u hu

theorem copy_constant {n m : ℕ} (p : Fin n → MvPolynomial (Fin n) ℤ) (E : Polynomial ℤ)
    (hE : E ≠ 0) (height : Fin n) (frozen : Fin m → Bool) (d : Fin n → ℕ)
    (hdeg : ∀ i, (p i).totalDegree ≤ d i) (hd : ∀ i, 0 < d i)
    (hp : AffineFiniteCoordinates.NoInfinity p d) {a b : ℝ}
    (curve : ℝ → Fin (m * n + 1) → ℝ) (hc : ContinuousOn curve (Ioo a b))
    (he : ∀ t ∈ Ioo a b, E.eval₂ (Int.castRingHom ℝ) (curve t 0) = 0)
    (k : Fin m) (hk : frozen k = true)
    (hr : ∀ t ∈ Ioo a b, ∀ i, (FrozenAffineCopies.row p height frozen k i).eval₂ (Int.castRingHom ℝ) (curve t) = 0)
    (s t : Ioo a b) :
    curve s.val ∘ FrozenAffineCopies.block k = curve t.val ∘ FrozenAffineCopies.block k := by
  have hparameter : ∀ v : Ioo a b, curve v.val 0 = curve s.val 0 := by
    intro v
    exact parameter_constant E hE (fun u => curve u 0) ((continuous_apply 0).comp_continuousOn hc)
      he v s
  let c (i : Fin n) : Polynomial ℤ := if i = height then Polynomial.X else 0
  have hf := AffineShiftCoordinates.finite_fiber p c d hdeg hd hp (curve s.val 0)
  let f : ℝ → Fin n → ℝ := fun v => curve v ∘ FrozenAffineCopies.block k
  have hfc : ContinuousOn f (Ioo a b) := by
    apply continuousOn_pi.mpr
    intro i
    exact (continuous_apply (FrozenAffineCopies.block k i)).comp_continuousOn hc
  apply eq_of_finite_image f hfc ?_ s t
  apply hf.subset
  rintro x ⟨v, hv, rfl⟩
  change PolynomialGridValues.value (AffineShiftCoordinates.rows p c) (curve s.val 0, f v) = 0
  rw [AffineShiftCoordinates.roots_iff]
  intro i
  have H := hr v hv i
  rw [FrozenAffineCopies.row_eval, sub_eq_zero] at H
  simp only [hk, true_and] at H
  simp only [c, SymbolicScaledSquarefree.scalarEvaluation, Polynomial.coe_eval₂RingHom]
  rw [hparameter ⟨v, hv⟩] at H
  split_ifs with hi
  · simpa only [f, hi, ite_true, Polynomial.eval₂_X] using H
  · simpa only [f, hi, ite_false, Polynomial.eval₂_zero] using H

theorem copy_constant_varying_height {n : ℕ} (p : Fin n → MvPolynomial (Fin n) ℤ) (E : Polynomial ℤ)
    (hE : E ≠ 0) (height : Fin n) (frozen : Fin 3 → Bool) (d : Fin n → ℕ)
    (hdeg : ∀ i, (p i).totalDegree ≤ d i) (hd : ∀ i, 0 < d i)
    (hp : AffineFiniteCoordinates.NoInfinity p d) {a b : ℝ}
    (curve : ℝ → Fin (3 * n + 1) → ℝ) (hc : ContinuousOn curve (Ioo a b))
    (hr : ∀ t ∈ Ioo a b, PolynomialGridValues.value (AffineShiftCoordinates.rows
      (FrozenAffineCopies.system p E height frozen)
      (fun j => if j = FrozenAffineCopies.block (0 : Fin 3) height then Polynomial.X else 0)) (t, curve t) = 0)
    (k : Fin 3) (hk : frozen k = true) (hkn : k ≠ 0) (s t : Ioo a b) :
    curve s.val ∘ FrozenAffineCopies.block k = curve t.val ∘ FrozenAffineCopies.block k := by
  have hrows (v : ℝ) (hv : v ∈ Ioo a b) := (AffineShiftCoordinates.roots_iff
    (FrozenAffineCopies.system p E height frozen)
    (fun j => if j = FrozenAffineCopies.block (0 : Fin 3) height then Polynomial.X else 0) v (curve v)).mp (hr v hv)
  have he : ∀ v ∈ Ioo a b, E.eval₂ (Int.castRingHom ℝ) (curve v 0) = 0 := by
    intro v hv
    have H := hrows v hv 0
    have hn : (0 : Fin (3 * n + 1)) ≠ FrozenAffineCopies.block (0 : Fin 3) height := by
      intro heq
      have H := congrArg Fin.val heq
      change 0 = (finProdFinEquiv ((0 : Fin 3), height)).val + 1 at H
      omega
    rw [ite_eq_right hn, map_zero, FrozenAffineCopies.system_zero, IndexedMultivariateRational.eval_parameter] at H
    exact H
  apply copy_constant p E hE height frozen d hdeg hd hp curve hc he k hk ?_ s t
  intro v hv i
  have H := hrows v hv (FrozenAffineCopies.block k i)
  have hn : FrozenAffineCopies.block k i ≠ FrozenAffineCopies.block (0 : Fin 3) height := by
    intro heq
    exact hkn ((FrozenAffineCopies.block_eq_iff k 0 i height).mp heq).1
  rwa [ite_eq_right hn, map_zero, FrozenAffineCopies.system_block] at H

end LeanCanny.Geometry.FrozenAffineBranches
