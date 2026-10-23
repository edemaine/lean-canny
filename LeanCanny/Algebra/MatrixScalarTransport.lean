/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # Determinants through specialization and injective scalar extension -/

@[expose] public section

namespace LeanCanny.Algebra.MatrixScalarTransport
variable {R S T I : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Fintype I] [DecidableEq I]

theorem det_specialization (φ : R →+* S) (M : Matrix I I R) (hM : M.map φ = 1) :
    φ M.det = 1 := by
  rw [φ.map_det]
  change (M.map φ).det = 1
  rw [hM, Matrix.det_one]

theorem det_map_ne_zero_of_specialization [Nontrivial S] (φ : R →+* S) (ψ : R →+* T)
    (hψ : Function.Injective ψ) (M : Matrix I I R) (hM : φ M.det = 1) :
    (M.map ψ).det ≠ 0 := by
  intro hz
  have hzero : M.det = 0 := hψ (by simpa only [map_zero] using (ψ.map_det M).trans hz)
  rw [hzero, map_zero] at hM
  exact zero_ne_one hM

end LeanCanny.Algebra.MatrixScalarTransport
