/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.FlatAffineCriticalExtremum
public import LeanCanny.Algebra.FermatCoordinateCone

/-! # Unique critical lifts when all other coordinates are fixed

For a coordinate objective and every other coordinate normal, each feasible
point has exactly one multiplier vector. No regularity of the source or
slice point is assumed, so multiple roots are retained at the recursion base.
-/

@[expose] public section
open LeanCanny LeanCanny.Algebra LeanCanny.Geometry MvPolynomial
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
namespace LeanCanny.Geometry.CoordinateTerminalCritical
variable {n : ℕ} {ι : Type*}

noncomputable def table (r : Fin n) : Fin (n + 1) → Fin n → ℤ :=
  Fin.cases (FermatCoordinateCone.normal r) FermatCoordinateCone.normal
noncomputable def multipliers (p : MvPolynomial (Fin n) ℤ) (r : Fin n) (z : Fin n → ℝ) : Fin (n + 1) → ℝ :=
  Fin.cases ((pderiv r p).eval₂ (Int.castRingHom ℝ) z)
    (fun j => if j = r then 0 else (pderiv j p).eval₂ (Int.castRingHom ℝ) z)

lemma gradient_sum (r : Fin n) (mu : Fin (n + 1) → ℝ) (i : Fin n) :
    (∑ j, ((table r j i : ℤ) : ℝ) * mu j) = (if i = r then mu 0 else 0) + mu i.succ := by
  rw [Fin.sum_univ_succ]
  simp [table, FermatCoordinateCone.normal, eq_comm]

theorem exists_root (p : MvPolynomial (Fin n) ℤ) (r : Fin n) (b : Fin n → MvPolynomial ι ℤ)
    (x : ι → ℝ) (z : Fin n → ℝ) (hp : p.eval₂ (Int.castRingHom ℝ) z = 0)
    (hl : ∀ j ∈ Finset.univ.erase r, ∑ i, ((table r j.succ i : ℤ) : ℝ) * z i = (b j).eval₂ (Int.castRingHom ℝ) x) :
    ∀ j, (FlatAffineCriticalStage.row p (Finset.univ.erase r) (table r) b j).eval₂ (Int.castRingHom ℝ)
      (Sum.elim x (Sum.elim z (multipliers p r z))) = 0 := by
  apply (FlatAffineCriticalStage.roots_iff (Int.castRingHom ℝ) p (Finset.univ.erase r) (table r) b _).mpr
  refine ⟨hp, hl, ?_, ?_⟩
  · intro i
    change (pderiv i p).eval₂ (Int.castRingHom ℝ) z = ∑ j, (Int.castRingHom ℝ) (table r j i) * multipliers p r z j
    change _ = ∑ j, ((table r j i : ℤ) : ℝ) * multipliers p r z j
    rw [gradient_sum]
    by_cases hi : i = r <;> simp [multipliers, hi]
  · intro j hj
    have HE : j = r := by simpa only [Finset.mem_erase, Finset.mem_univ, and_true, not_not] using hj
    simp [FlatAffineCriticalStage.multiplier, multipliers, HE]

theorem unique_multipliers (p : MvPolynomial (Fin n) ℤ) (r : Fin n) (b : Fin n → MvPolynomial ι ℤ)
    (x : ι → ℝ) (z : Fin n → ℝ) (mu : Fin (n + 1) → ℝ)
    (hroot : ∀ j, (FlatAffineCriticalStage.row p (Finset.univ.erase r) (table r) b j).eval₂ (Int.castRingHom ℝ)
      (Sum.elim x (Sum.elim z mu)) = 0) : mu = multipliers p r z := by
  have H := (FlatAffineCriticalStage.roots_iff (Int.castRingHom ℝ) p (Finset.univ.erase r) (table r) b _).mp hroot
  have HM : mu r.succ = 0 := H.2.2.2 r (by simp)
  have HG (i : Fin n) : (pderiv i p).eval₂ (Int.castRingHom ℝ) z = (if i = r then mu 0 else 0) + mu i.succ := by
    have HR := H.2.2.1 i
    change (pderiv i p).eval₂ (Int.castRingHom ℝ) z = ∑ j, ((table r j i : ℤ) : ℝ) * mu j at HR
    rw [gradient_sum] at HR
    exact HR
  funext j
  refine Fin.cases ?_ (fun i => ?_) j
  · have HR := HG r
    simpa only [multipliers, Fin.cases_zero, ite_true, HM, add_zero] using HR.symm
  · by_cases hi : i = r
    · simp only [multipliers, Fin.cases_succ, hi, ite_true]
      exact HM
    · have HR := HG i
      simpa only [multipliers, Fin.cases_succ, hi, ite_false, zero_add] using HR.symm
end LeanCanny.Geometry.CoordinateTerminalCritical
