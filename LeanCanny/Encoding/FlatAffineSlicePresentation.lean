/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffineShiftedSliceProjection
public import LeanCanny.Encoding.FlatAffineCompleteComponentSamples

/-! # A shared presentation of original affine slice constraints

This interface keeps polynomial, normal, and level data explicit when
transporting a slice between native source records.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffineSlicePresentation
open Set LeanCanny.Algebra
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

noncomputable def set {n : ℕ} (p : MvPolynomial (Fin n) ℤ) (s : Finset (Fin n))
    (a : Fin n → Fin n → ℤ) (b : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {y | p.eval₂ (Int.castRingHom ℝ) y = 0 ∧ ∀ j ∈ s, ∑ i, (a j i : ℝ) * y i = b j}

theorem set_congr {n : ℕ} (p : MvPolynomial (Fin n) ℤ) {s t : Finset (Fin n)}
    {a c : Fin n → Fin n → ℤ} {b d : Fin n → ℝ} (hs : s = t) (ha : a = c) (hb : b = d) :
    set p s a b = set p t c d := by
  subst t
  subst c
  subst d
  rfl

noncomputable def rootOfSystemEq {n : ℕ} (p q : Fin n → MvPolynomial (Fin n) ℤ) (h : p = q)
    (x : {z : Fin n → ℝ // ∀ i, (p i).eval₂ (Int.castRingHom ℝ) z = 0}) :
    {z : Fin n → ℝ // ∀ i, (q i).eval₂ (Int.castRingHom ℝ) z = 0} :=
  ⟨x.val, fun i => (congrArg (fun f => (f i).eval₂ (Int.castRingHom ℝ) x.val) h).symm.trans (x.property i)⟩

theorem rootOfSystemEq_val {n : ℕ} (p q : Fin n → MvPolynomial (Fin n) ℤ) (h : p = q)
    (x : {z : Fin n → ℝ // ∀ i, (p i).eval₂ (Int.castRingHom ℝ) z = 0}) :
    (rootOfSystemEq p q h x).val = x.val := rfl

theorem coarse (F : FlatAffineFullSourceTower.Inputs) (u : List Bool)
    (x : FlatAffinePowerSampleInput.OriginalRoots F u) (h : Fin (FlatAffineFullSourceTower.arity F u)) :
    FlatAffineShiftedSlice.coarseSlice F u x h =
      set (BoundedFullCriticalSamples.polynomial F.source u)
        ((FlatAffineFullSourceTower.free F u (F.depth u)).erase h)
        (fun j i => FlatAffineFullSourceTower.direction F u (F.depth u) j.succ i)
        (fun j => (FlatAffineFullSourceTower.level F u (F.depth u) j).polynomial.eval₂ (Int.castRingHom ℝ)
          (x.val ∘ TriangularPolynomialIndexing.enumerate (FlatAffineFullSourceTower.stageWidth F u) (F.depth u))) := rfl

theorem original (F : FlatAffineFullSourceTower.Inputs) (u : List Bool)
    (x : FlatAffinePowerSampleInput.OriginalRoots F u) :
    FlatAffineCompleteComponentSamples.slice F u x =
      set (BoundedFullCriticalSamples.polynomial F.source u)
        (FlatAffineFullSourceTower.free F u (F.depth u))
        (fun j i => FlatAffineFullSourceTower.direction F u (F.depth u) j.succ i)
        (fun j => (FlatAffineFullSourceTower.level F u (F.depth u) j).polynomial.eval₂ (Int.castRingHom ℝ)
          (x.val ∘ TriangularPolynomialIndexing.enumerate (FlatAffineFullSourceTower.stageWidth F u) (F.depth u))) := rfl

end LeanCanny.Encoding.FlatAffineSlicePresentation
