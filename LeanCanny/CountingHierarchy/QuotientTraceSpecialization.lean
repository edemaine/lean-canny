/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.QuotientMultiplicationMatrix
public import LeanCanny.CountingHierarchy.PurePowerResidueMap

/-! # Specializing power traces without constructing specialized bases -/

public section

namespace LeanCanny.CountingHierarchy.PurePowerResidue

open MvPolynomial
open scoped Classical

set_option backward.isDefEq.respectTransparency false

variable {S T : Type*} [CommRing S] [CommRing T] {n : ℕ}

theorem jacobian_map (φ : S →+* T) (ell : ℕ) (r : Fin n → MvPolynomial (Fin n) S) :
    (jacobian ell r).map φ = jacobian ell (fun i => (r i).map φ) := by
  unfold jacobian
  rw [RingHom.map_det, RingHom.mapMatrix_apply]
  congr 1
  apply Matrix.ext
  intro i j
  change (pderiv j (X i ^ ell - r i)).map φ = _
  rw [← pderiv_map]
  simp only [map_sub, map_pow, map_X]

/-- The power traces of the source multiplication matrix specialize to
 the same finite residue formula. This avoids assuming a computational
 change of basis or identifying two quotient matrix representations. -/
theorem multiplicationMatrix_map_trace_pow (φ : S →+* T)
    (d : ℕ) (hd : 1 ≤ d)
    (r : Fin n → MvPolynomial (Fin n) S) (hr : ∀ i, (r i).totalDegree ≤ d)
    (v : MvPolynomial (Fin n) S) (k : ℕ) :
    (((multiplicationMatrix (by omega : 1 ≤ d + 1) r
      (fun i => (hr i).trans_lt (Nat.lt_succ_self d)) v).map φ) ^ k).trace =
        residue (d + 1) (fun i => (r i).map φ)
          ((v.map φ) ^ k * jacobian (d + 1) (fun i => (r i).map φ)) := by
  rw [← Matrix.map_pow, ← AddMonoidHom.map_trace,
    multiplicationMatrix_trace_pow d hd r hr v k,
    residue_map φ (by omega) r (fun i => (hr i).trans_lt (Nat.lt_succ_self d)),
    map_mul, map_pow, jacobian_map]

end LeanCanny.CountingHierarchy.PurePowerResidue
