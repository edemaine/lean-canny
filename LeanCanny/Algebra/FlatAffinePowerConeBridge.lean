/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FlatAffinePowerInfinity
public import LeanCanny.Algebra.AffineConeDirectionGeometry

/-! # Original cone certificates for finite power towers

The original Lagrange root-exclusion certificate specializes to the integer
source and signed normal table used by the full tower.
-/

@[expose] public section
namespace LeanCanny.Algebra.FlatAffinePowerTower
open MvPolynomial
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem coneRootFree_of_critical (H : MvPolynomial (Fin n) ℤ) (s : Finset (Fin n))
    (a : Fin (n + 1) → Fin n → ℤ)
    (h : AffineConeDirectionGeometry.CriticalRootFree (K := ℚ) (L := ℂ)
      (H.map (Int.castRingHom ℚ)) s (fun r i => (a r.succ i : ℚ)) (fun i => (a 0 i : ℂ))) :
    ConeRootFree H s a := by
  intro x mu hp hl hg hu
  have he : (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ := Subsingleton.elim _ _
  have ha (r : Fin (n + 1)) (i : Fin n) : algebraMap ℚ ℂ (a r i : ℚ) = (a r i : ℂ) := map_intCast _ _
  apply h x mu
  · simpa only [aeval_def, coe_eval₂Hom, eval₂_map, he] using hp
  · simpa only [ha] using hl
  · intro i
    rw [pderiv_map, aeval_def, eval₂_map, he]
    simpa only [Fin.sum_univ_succ, ha] using hg i
  · exact hu

end LeanCanny.Algebra.FlatAffinePowerTower
