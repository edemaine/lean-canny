/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PhysicalPowerCriticalInfinity
public import LeanCanny.Algebra.FermatScaledPowerCone

/-! # Physical block exclusion at infinity for coordinate slices

An unused coordinate objective and nonzero coordinate-normal scalings force
all physical and multiplier coordinates to vanish. Old scalar parameters
may be arbitrary here; their own monic rows exclude their infinity roots.
-/

@[expose] public section
namespace LeanCanny.Algebra.PhysicalPowerCriticalRows
open MvPolynomial FlatAffineCriticalStage
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
variable {ι R K : Type*} {n : ℕ} [Fintype ι] [CommRing R] [Field K]

def coordinateNormals (b : R) (c : Fin (n + 1) → R) (r : Fin (n + 1)) :
    Fin (n + 2) → Fin (n + 1) → R :=
  Fin.cons (fun i => if i = r then b else 0) (fun j i => if i = j then c j else 0)

theorem normal_power_sum (φ : R →+* K) (b : R) (c : Fin (n + 1) → R) (r i : Fin (n + 1))
    (mu : Fin (n + 2) → K) (Q : ℕ) :
    (∑ j, φ (coordinateNormals b c r j i) * mu j ^ Q) =
      (if i = r then φ b * mu 0 ^ Q else 0) + φ (c i) * mu i.succ ^ Q := by
  simp [coordinateNormals, Fin.sum_univ_succ, apply_ite, eq_comm]

theorem normal_height_sum (φ : R →+* K) (b : R) (c : Fin (n + 1) → R) (r i : Fin (n + 1))
    (x : Fin (n + 1) → K) (W : ℕ) :
    (∑ j, φ (coordinateNormals b c r i.succ j) * x j ^ W) = φ (c i) * x i ^ W := by
  simp [coordinateNormals, apply_ite, eq_comm]

theorem physical_zero_of_nonzero_gradient (φ : R →+* K) (low : MvPolynomial (Fin (n + 1)) R) (a b : R)
    (c : Fin (n + 1) → R) (s : Finset (Fin (n + 1))) (r : Fin (n + 1)) (hr : r ∉ s)
    (H : Fin (n + 1) → MvPolynomial ι R) (w : ι → ℕ) (D W : ℕ)
    (hD : 2 ≤ D) (hW : 0 < W) (hlow : low.totalDegree < D)
    (ha : φ a ≠ 0) (hg : φ (a * (D : R)) ≠ 0) (hb : φ b ≠ 0) (hc : ∀ i, φ (c i) ≠ 0)
    (hH : ∀ i ∈ s, (CoordinatePowerSubstitution.substitute w (H i)).totalDegree < W)
    (y : Option (ι ⊕ Variables (n + 1)) → K) (hy : y none = 0)
    (hz : ∀ j, (WeightedHomogenization.homogenize (fun _ => 1) (degrees s D W j)
      (rows (FermatCriticalHomogenization.polynomial low a D) s (coordinateNormals b c r) H w D W j)).eval₂ φ y = 0) :
    (fun i => y (some (ambient i))) = 0 ∧ (fun j => y (some (multiplier j))) = 0 := by
  have HP := hz (Sum.inr 0)
  simp only [degrees, Fin.cases_zero] at HP
  rw [source_infinity φ low a s _ H w D W hlow hW y hy] at HP
  have HL : ∀ i ∈ s, φ (c i) * y (some (ambient i)) ^ W = 0 := by
    intro i hi
    have HI := hz (Sum.inr i.succ)
    simp only [degrees, Fin.cases_succ, ite_eq_left hi] at HI
    rw [height_infinity φ _ s _ H w D W y hy i hi (hH i hi), normal_height_sum] at HI
    exact HI
  have HG : ∀ i, φ (a * (D : R)) * y (some (ambient i)) ^ ((D - 1) * W) =
      (if i = r then φ b * y (some (multiplier 0)) ^ ((D - 1) * W) else 0) +
        φ (c i) * y (some (multiplier i.succ)) ^ ((D - 1) * W) := by
    intro i
    have HI := hz (Sum.inl i)
    simp only [degrees] at HI
    rw [gradient_infinity φ low a s _ H w D W hD hlow hW y hy i, normal_power_sum] at HI
    exact sub_eq_zero.mp HI
  have HU : ∀ i, i ∉ s → y (some (multiplier i.succ)) = 0 := by
    intro i hi
    have HI := hz (Sum.inr i.succ)
    simp only [degrees, Fin.cases_succ, ite_eq_right hi] at HI
    rw [inactive_infinity φ _ s _ H w D W y i hi] at HI
    exact (pow_eq_zero_iff (Nat.mul_pos (by omega : 0 < D - 1) hW).ne').mp HI
  exact FermatScaledPowerCone.root_zero (D * W) ((D - 1) * W) W (Nat.mul_pos (by omega) hW)
    (Nat.mul_pos (by omega) hW) hW (φ a) (φ (a * (D : R))) (φ b) ha hg hb (fun i => φ (c i)) hc s r hr
    (fun i => y (some (ambient i))) (fun j => y (some (multiplier j))) HP HL HG HU

theorem physical_zero [CharZero K] (φ : R →+* K) (low : MvPolynomial (Fin (n + 1)) R) (a b : R)
    (c : Fin (n + 1) → R) (s : Finset (Fin (n + 1))) (r : Fin (n + 1)) (hr : r ∉ s)
    (H : Fin (n + 1) → MvPolynomial ι R) (w : ι → ℕ) (D W : ℕ)
    (hD : 2 ≤ D) (hW : 0 < W) (hlow : low.totalDegree < D)
    (ha : φ a ≠ 0) (hb : φ b ≠ 0) (hc : ∀ i, φ (c i) ≠ 0)
    (hH : ∀ i ∈ s, (CoordinatePowerSubstitution.substitute w (H i)).totalDegree < W)
    (y : Option (ι ⊕ Variables (n + 1)) → K) (hy : y none = 0)
    (hz : ∀ j, (WeightedHomogenization.homogenize (fun _ => 1) (degrees s D W j)
      (rows (FermatCriticalHomogenization.polynomial low a D) s (coordinateNormals b c r) H w D W j)).eval₂ φ y = 0) :
    (fun i => y (some (ambient i))) = 0 ∧ (fun j => y (some (multiplier j))) = 0 := by
  apply physical_zero_of_nonzero_gradient φ low a b c s r hr H w D W hD hW hlow ha ?_ hb hc hH y hy hz
  rw [map_mul, map_natCast]
  exact mul_ne_zero ha (Nat.cast_ne_zero.mpr (by omega))

end LeanCanny.Algebra.PhysicalPowerCriticalRows
