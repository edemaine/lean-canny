/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FermatCoordinateCone

/-! # Nonzero scalings of coordinate cone normals

Scaling the objective and each height normal by nonzero constants preserves
cone exclusion over every characteristic-zero coefficient-field extension.
Doubled height normals allow integer equations for ancestral midpoints.
-/

@[expose] public section
namespace LeanCanny.Algebra.FermatScaledCoordinateCone
open MvPolynomial AffineConeDirectionGeometry FermatCoordinateCone
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
universe u
variable {K : Type u} {n : ℕ} [Field K] [CharZero K]
/-- Every unused coordinate is an admissible objective for coordinate slices. -/
theorem criticalRootFree {L : Type u} [Field L] [Algebra K L]
    (a : K) (ha : a ≠ 0) (D : ℕ) (hD : 1 < D)
    (b : K) (hb0 : b ≠ 0) (c : Fin n → K) (hc0 : ∀ i, c i ≠ 0)
    (s : Finset (Fin n)) (r : Fin n) (hr : r ∉ s) :
    CriticalRootFree (FermatAffineConeFlag.form a D) s (fun j i => c j * normal j i)
      (fun i => algebraMap K L (b * normal r i)) := by
  let _ : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  intro x mu hp hl hg hu
  have ha' : algebraMap K L a ≠ 0 := (map_ne_zero (algebraMap K L)).mpr ha
  have hb : algebraMap K L a * (D : L) ≠ 0 :=
    mul_ne_zero ha' (Nat.cast_ne_zero.mpr (by omega))
  have hb' : algebraMap K L b ≠ 0 := (map_ne_zero (algebraMap K L)).mpr hb0
  have hc' (i : Fin n) : algebraMap K L (c i) ≠ 0 := (map_ne_zero (algebraMap K L)).mpr (hc0 i)
  have hgrad (i : Fin n) : algebraMap K L a * (D : L) * x i ^ (D - 1) =
      (if i = r then algebraMap K L b * mu 0 else 0) + algebraMap K L (c i) * mu i.succ := by
    have H := hg i
    simpa [FermatAffineConeFlag.pderiv_form, normal, apply_ite, eq_comm] using H
  have hactive (i : Fin n) (hi : i ∈ s) : x i = 0 := by
    have H : algebraMap K L (c i) * x i = 0 := by simpa [normal, apply_ite, eq_comm] using hl i hi
    exact (mul_eq_zero.mp H).resolve_left (hc' i)
  have hother (i : Fin n) (hi : i ≠ r) : x i = 0 := by
    by_cases hs : i ∈ s
    · exact hactive i hs
    · have H := hgrad i
      rw [ite_eq_right hi, hu i hs, mul_zero, zero_add] at H
      exact (pow_eq_zero_iff (by omega : D - 1 ≠ 0)).mp ((mul_eq_zero.mp H).resolve_left hb)
  have hxr : x r = 0 := by
    have H : algebraMap K L a * x r ^ D = 0 := by
      have he : (∑ i, x i ^ D) = x r ^ D := by
        apply Finset.sum_eq_single r
        · intro i _ hi
          rw [hother i hi, zero_pow (by omega : D ≠ 0)]
        · simp
      simpa only [FermatAffineConeFlag.form, map_mul, aeval_C, map_sum, map_pow, aeval_X, he] using hp
    exact (pow_eq_zero_iff (by omega : D ≠ 0)).mp ((mul_eq_zero.mp H).resolve_left ha')
  have hx : x = 0 := by
    funext i
    by_cases hi : i = r
    · simpa only [hi, Pi.zero_apply] using hxr
    · exact hother i hi
  have hm0 : mu 0 = 0 := by
    have H := hgrad r
    rw [hx, Pi.zero_apply, zero_pow (by omega : D - 1 ≠ 0), mul_zero, ite_eq_left rfl,
      hu r hr, mul_zero, add_zero] at H
    exact (mul_eq_zero.mp H.symm).resolve_left hb'
  refine ⟨hx, ?_⟩
  funext j
  refine Fin.cases hm0 (fun i => ?_) j
  have H := hgrad i
  have H' : algebraMap K L (c i) * mu i.succ = 0 := by
    simpa only [hx, Pi.zero_apply, zero_pow (by omega : D - 1 ≠ 0), mul_zero, hm0,
      ite_self, zero_add] using H.symm
  exact (mul_eq_zero.mp H').resolve_left (hc' i)

end LeanCanny.Algebra.FermatScaledCoordinateCone
