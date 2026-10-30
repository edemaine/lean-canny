/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FlatAffineCoordinateCoarsening
public import Mathlib.Topology.Connected.TotallyDisconnected
public import Mathlib.Topology.Instances.Real.Lemmas

/-! # Zero objective multipliers cannot trace a varying coordinate height

Coarsening transfers a continuous singular critical branch into a finite
ordinary critical root set. Its entire prefix and newest ambient point are
therefore constant. In particular, the removed affine-height equation has a
constant value. No regularity of that point or of either critical system is
assumed.
-/

@[expose] public section
namespace LeanCanny.Geometry.FlatAffineSingularHeightCurves
open LeanCanny.Algebra MvPolynomial FlatAffineCriticalTower FlatAffineCriticalStage
open FlatAffineTowerCoarsening
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

variable {n k : ℕ} {T : Type*} [TopologicalSpace T]

theorem continuous_point (h : Fin n) (x : T → Fin (k * width n) → ℝ)
    (y : T → Fin n → ℝ) (mu : T → Fin (n + 1) → ℝ)
    (hx : Continuous x) (hy : Continuous y) (hmu : Continuous mu) :
    Continuous (fun t => point k h (x t) (y t) (mu t)) := by
  apply continuous_pi
  intro i
  change Continuous (fun t => Sum.elim (x t ∘ TriangularPolynomialIndexing.enumerate (width n) k)
    ((Sum.elim (y t) (FlatAffineCriticalCoarsening.multipliers (mu t) h)) ∘ (blockEquiv n).symm)
    ((TriangularPolynomialIndexing.enumerate (width n) (k + 1)).symm i))
  cases (TriangularPolynomialIndexing.enumerate (width n) (k + 1)).symm i with
  | inl v => exact (continuous_apply (TriangularPolynomialIndexing.enumerate (width n) k v)).comp hx
  | inr v =>
    dsimp only [Sum.elim_inr, Function.comp_apply]
    cases (blockEquiv n).symm v with
    | inl j => exact (continuous_apply j).comp hy
    | inr r =>
      refine Fin.cases ?_ (fun j => ?_) r
      · exact (continuous_apply h.succ).comp hmu
      · by_cases hj : j = h
        · simpa only [Sum.elim_inr, Function.comp_def, FlatAffineCriticalCoarsening.multipliers, Fin.cases_succ, ite_eq_left hj] using
            (continuous_const : Continuous (fun _ : T => (0 : ℝ)))
        · simpa only [Sum.elim_inr, Function.comp_def, FlatAffineCriticalCoarsening.multipliers, Fin.cases_succ, ite_eq_right hj] using
            (continuous_apply j.succ).comp hmu

variable [PreconnectedSpace T]

theorem constant (low : MvPolynomial (Fin n) ℤ) (c : ℤ) (hc : c ≠ 0)
    (D : ℕ) (hD : 1 < D) (hlow : low.totalDegree < D)
    (s : ℕ → Finset (Fin n)) (a : ℕ → Fin (n + 1) → Fin n → ℤ)
    (b : (j : ℕ) → Fin n → Level n j ℤ) (h : Fin n)
    (hnormal : ∀ j i, a k j.succ i = FermatCoordinateCone.normal j i)
    (hcone : ∀ t : Fin k, FlatAffinePowerTower.ConeRootFree (C c * ∑ i : Fin n, X i ^ D)
      (s t.val) (a t.val))
    (x : T → Fin (k * width n) → ℝ) (y : T → Fin n → ℝ) (mu : T → Fin (n + 1) → ℝ)
    (hx : Continuous x) (hy : Continuous y) (hmu : Continuous mu)
    (hprefix : ∀ t i, (FlatAffineCriticalTower.system (low + C c * ∑ i : Fin n, X i ^ D)
      s a b k i).eval₂ (Int.castRingHom ℝ) (x t) = 0)
    (hz : ∀ t, mu t 0 = 0)
    (hroot : ∀ t j, j ≠ Sum.inr h.succ →
      (row (low + C c * ∑ i : Fin n, X i ^ D) (s k) (a k) (fun i => (b k i).polynomial) j).eval₂
        (Int.castRingHom ℝ) (Sum.elim (x t ∘ TriangularPolynomialIndexing.enumerate (width n) k)
          (Sum.elim (y t) (mu t))) = 0) (u v : T) :
    x u = x v ∧ y u = y v := by
  let S := {z : Fin ((k + 1) * width n) → ℝ | ∀ i,
    (FlatAffineCriticalTower.system (low + C c * ∑ i : Fin n, X i ^ D)
      (active s k h) (directions a k h) b (k + 1) i).eval₂ (Int.castRingHom ℝ) z = 0}
  have HR (t : T) : point k h (x t) (y t) (mu t) ∈ S :=
    FlatAffineTowerCoarsening.roots (Int.castRingHom ℝ) _ s a b k h (x t) (y t) (mu t)
      (hprefix t) (hz t) (hroot t)
  let z : T → S := fun t => ⟨point k h (x t) (y t) (mu t), HR t⟩
  have HZ : Continuous z := (continuous_point h x y mu hx hy hmu).subtype_mk HR
  let : Finite S := (FlatAffineCoordinateCoarsening.finite_roots low c hc D hD hlow s a b h hnormal hcone).to_subtype
  let : TotallyDisconnectedSpace S := inferInstance
  have HE := congrArg (fun r : S => r.val) (TotallyDisconnectedSpace.eq_of_continuous z HZ u v)
  constructor
  · exact (point_prefix k h (x u) (y u) (mu u)).symm.trans
      ((congrArg (fun r => r ∘ TriangularPolynomialRows.prefixIndex (width n) k (k + 1) (by omega)) HE).trans
        (point_prefix k h (x v) (y v) (mu v)))
  · funext i
    exact (point_current k h (x u) (y u) (mu u) i).symm.trans
      ((congrFun HE (TriangularPolynomialRows.block (width n) k (k + 1) (by omega)
        (blockEquiv n (Sum.inl i)))).trans (point_current k h (x v) (y v) (mu v) i))

theorem height_value_eq {ι : Type*} (p : MvPolynomial (Fin n) ℤ) (s : Finset (Fin n))
    (a : Fin (n + 1) → Fin n → ℤ) (b : Fin n → MvPolynomial ι ℤ)
    (h : Fin n) (hs : h ∈ s) (x x' : ι → ℝ) (y y' : Fin n → ℝ)
    (mu mu' : Fin (n + 1) → ℝ) (hx : x = x') (hy : y = y') :
    (row p s a b (Sum.inr h.succ)).eval₂ (Int.castRingHom ℝ) (Sum.elim x (Sum.elim y mu)) =
      (row p s a b (Sum.inr h.succ)).eval₂ (Int.castRingHom ℝ) (Sum.elim x' (Sum.elim y' mu')) := by
  simp only [row, Fin.cases_succ, ite_eq_left hs, eval₂_sub, AffineHeightPolynomial.eval,
    eval₂_rename, Function.comp_def, ambient, Sum.elim_inr, Sum.elim_inl]
  rw [hx, hy]

end LeanCanny.Geometry.FlatAffineSingularHeightCurves
