/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.AffineCriticalDirectionGeometry

/-! # One bounded critical direction for a finite family of affine slices

All family members share dimension, degree allowance, and active slots.
Their sources, old normals, and fixed levels may differ. Avoiding a maximal
minor for every member costs the family cardinality in the integer allowance,
so only its logarithmic bound is added to the objective bit width.
-/

@[expose] public section
namespace LeanCanny.Algebra.AffineCriticalCommonDirection
open MvPolynomial AffineCriticalPowerBadSystem
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false
universe u
variable {K : Type u} {n : ℕ} [Field K] [CharZero K]

def allowance (n D count : ℕ) : ℕ := count * AffineCriticalBoundedDirection.allowance n D
def binaryWidth (n D countBits : ℕ) : ℕ := countBits + AffineCriticalBoundedDirection.binaryWidth n D

theorem allowance_lt_two_pow (n D count countBits : ℕ) (hc : count ≤ 2 ^ countBits) :
    allowance n D count < 2 ^ binaryWidth n D countBits := by
  unfold allowance binaryWidth
  calc
    _ ≤ 2 ^ countBits * AffineCriticalBoundedDirection.allowance n D := Nat.mul_le_mul_right _ hc
    _ < 2 ^ countBits * 2 ^ AffineCriticalBoundedDirection.binaryWidth n D :=
      Nat.mul_lt_mul_of_pos_left (AffineCriticalBoundedDirection.allowance_lt_two_pow n D) (by positivity)
    _ = _ := by rw [← pow_add]

theorem exists_common_root_free {σ : Type*} [Fintype σ]
    (low H : σ → MvPolynomial (Fin n) K) (D : ℕ) (hlow : ∀ t, (low t).totalDegree < D)
    (hH : ∀ t, (H t).IsHomogeneous D) (hD : 1 < D) (s : Finset (Fin n)) (hs : s.card < n)
    (A : σ → Fin n → Fin n → K) (β : σ → Fin n → K)
    (hcone : ∀ t, ∀ (L : Type u) [Field L] [Algebra K L], AffineConeFlag.Transverse (L := L) (H t) s (A t))
    (hslice : ∀ t, ∀ (L : Type u) [Field L] [Algebra K L] (x : Fin n → L), aeval x (low t + H t) = 0 →
      (∀ r ∈ s, ∑ i, algebraMap K L (A t r i) * x i = algebraMap K L (β t r)) →
      GenericAffineCriticalJacobian.ConstraintIndependent (low t + H t) s (A t) x) :
    ∃ v : Fin n → ℕ, (∀ i, v i ≤ allowance n D (Fintype.card σ)) ∧
      ∀ t, ∀ (L : Type u) [Field L] [Algebra K L] (z : Fin (2 * n + 2) → L),
        (∀ j, (nativeRows (low t + H t) D s (A t) (β t) j).eval₂
          (eval₂Hom (algebraMap K L) (fun i => (v i : L))) z = 0) → z = 0 := by
  let R := MvPolynomial (Fin n) K
  let F := FractionRing R
  let L := AlgebraicClosure F
  let φ : R →+* L := (algebraMap F L).comp (algebraMap R F)
  let _ : Algebra K L := (φ.comp C).toAlgebra
  have hinj : Function.Injective φ := (algebraMap F L).injective.comp (IsFractionRing.injective R F)
  have hφ : φ.comp C = algebraMap K L := rfl
  have hr (t : σ) (z : Fin (2 * n + 2) → L)
      (hz : ∀ j, (nativeRows (low t + H t) D s (A t) (β t) j).eval₂ φ z = 0) : z = 0 :=
    native_no_root φ hφ hinj (low t) (H t) D (hlow t) (hH t) hD s hs (A t) (β t) (hcone t L) (hslice t L) z hz
  exact ProjectiveDirectionFamily.exists_common_bounded
    (fun t => nativeRows (low t + H t) D s (A t) (β t)) (nativeDegrees D s)
    (AffineCriticalBoundedDirection.width n D) (2 * n + 1) (AffineCriticalBoundedDirection.level_lt_width D hD s)
    (fun t => native_homogeneous (low t + H t) D s (A t) (β t))
    (fun j => degrees_pos D hD s ((layout n).symm j))
    (fun t => native_parameter_degree (low t + H t) D s (A t) (β t)) φ hr

/-- One integer objective makes every original critical stage regular and
preserves every leading-cone flag in the family. -/
theorem exists_common {σ : Type*} [Fintype σ]
    (low H : σ → MvPolynomial (Fin n) K) (D : ℕ) (hlow : ∀ t, (low t).totalDegree < D)
    (hH : ∀ t, (H t).IsHomogeneous D) (hD : 1 < D) (s : Finset (Fin n)) (hs : s.card < n)
    (A : σ → Fin n → Fin n → K) (β : σ → Fin n → K)
    (hcone : ∀ t, ∀ (L : Type u) [Field L] [Algebra K L], AffineConeFlag.Transverse (L := L) (H t) s (A t))
    (hslice : ∀ t, ∀ (L : Type u) [Field L] [Algebra K L] (x : Fin n → L), aeval x (low t + H t) = 0 →
      (∀ r ∈ s, ∑ i, algebraMap K L (A t r i) * x i = algebraMap K L (β t r)) →
      GenericAffineCriticalJacobian.ConstraintIndependent (low t + H t) s (A t) x)
    (countBits : ℕ) (hcount : Fintype.card σ ≤ 2 ^ countBits) :
    ∃ v : Fin n → ℕ, (∀ i, v i < 2 ^ binaryWidth n D countBits) ∧
      ∀ t, ∀ (L : Type u) [Field L] [Algebra K L],
        AffineCriticalDirectionGeometry.CriticalRegular (low t + H t) s (A t) (β t) (fun i => (v i : L)) ∧
        AffineConeDirectionGeometry.CriticalRootFree (H t) s (A t) (fun i => (v i : L)) := by
  obtain ⟨v, hv, hfree⟩ := exists_common_root_free low H D hlow hH hD s hs A β hcone hslice
  refine ⟨v, fun i => (hv i).trans_lt (allowance_lt_two_pow n D _ countBits hcount), ?_⟩
  intro t L _ _
  exact ⟨AffineCriticalDirectionGeometry.regular_of_native (low t) (H t) D (hlow t) (hH t) hD s (A t) (β t) v (hfree t) L,
    AffineCriticalDirectionGeometry.cone_free_of_native (low t) (H t) D (hlow t) (hH t) hD s (A t) (β t) v (hfree t) L⟩

end LeanCanny.Algebra.AffineCriticalCommonDirection
