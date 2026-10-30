/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.FlatAffineSingularHeightCurves

/-! # Finite coarser roots force zero-objective branches to be constant

This isolates the topological argument from the particular cone certificate.
Unit and scaled coordinate sources construct its finite-root premise from
their original leading equations.
-/

@[expose] public section
namespace LeanCanny.Geometry.FlatAffineCoarsenedCurveConstancy
open LeanCanny.Algebra MvPolynomial FlatAffineCriticalTower FlatAffineCriticalStage
open FlatAffineTowerCoarsening
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem constant {n k : ℕ} {T : Type*} [TopologicalSpace T] [PreconnectedSpace T]
    (p : MvPolynomial (Fin n) ℤ) (s : ℕ → Finset (Fin n))
    (a : ℕ → Fin (n + 1) → Fin n → ℤ) (b : (j : ℕ) → Fin n → Level n j ℤ) (h : Fin n)
    (hfinite : {z : Fin ((k + 1) * width n) → ℝ | ∀ i,
      (FlatAffineCriticalTower.system p (active s k h) (directions a k h) b (k + 1) i).eval₂ (Int.castRingHom ℝ) z = 0}.Finite)
    (x : T → Fin (k * width n) → ℝ) (y : T → Fin n → ℝ) (mu : T → Fin (n + 1) → ℝ)
    (hx : Continuous x) (hy : Continuous y) (hmu : Continuous mu)
    (hprefix : ∀ t i, (FlatAffineCriticalTower.system p s a b k i).eval₂ (Int.castRingHom ℝ) (x t) = 0)
    (hz : ∀ t, mu t 0 = 0)
    (hroot : ∀ t j, j ≠ Sum.inr h.succ →
      (row p (s k) (a k) (fun i => (b k i).polynomial) j).eval₂ (Int.castRingHom ℝ)
        (Sum.elim (x t ∘ TriangularPolynomialIndexing.enumerate (width n) k) (Sum.elim (y t) (mu t))) = 0)
    (u v : T) : x u = x v ∧ y u = y v := by
  let S := {z : Fin ((k + 1) * width n) → ℝ | ∀ i,
    (FlatAffineCriticalTower.system p (active s k h) (directions a k h) b (k + 1) i).eval₂ (Int.castRingHom ℝ) z = 0}
  have HR (t : T) : point k h (x t) (y t) (mu t) ∈ S :=
    FlatAffineTowerCoarsening.roots (Int.castRingHom ℝ) p s a b k h (x t) (y t) (mu t) (hprefix t) (hz t) (hroot t)
  let z : T → S := fun t => ⟨point k h (x t) (y t) (mu t), HR t⟩
  have HZ : Continuous z := (FlatAffineSingularHeightCurves.continuous_point h x y mu hx hy hmu).subtype_mk HR
  let : Finite S := hfinite.to_subtype
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

end LeanCanny.Geometry.FlatAffineCoarsenedCurveConstancy
