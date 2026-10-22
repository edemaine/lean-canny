/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulWeightProjection
public import LeanCanny.Algebra.KoszulProjectiveExact

/-! # Exactness of every finite weighted Koszul piece

Project an arbitrary exterior-degree preimage onto the desired total
weight. The projection commutes with the differential and fixes the target,
so positive exactness of the polynomial complex descends to each finite
weighted complex. Projective root exclusion supplies that exactness.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulWeighted
variable {n : ℕ} {R : Type*} [CommRing R]

theorem weighted_exact_of_graded_exact (p : Fin n → Poly n R) (d : Fin n → ℕ) (L W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : L < 2 ^ W)
    (hex : ∀ k, LinearMap.ker (KoszulExterior.gradedDifferential p k) =
      LinearMap.range (KoszulExterior.gradedDifferential p (k + 1))) (k : ℕ) :
    LinearMap.ker (differential p d L W hp hW k) =
      LinearMap.range (differential p d L W hp hW (k + 1)) := by
  apply le_antisymm
  · intro x hx
    let z : ExteriorAlgebra.exteriorPower (Poly n R) (k + 1) (Fin n → Poly n R) :=
      ⟨x.val, space_le_exteriorGrade d L W (k + 1) x.property⟩
    have hz : z ∈ LinearMap.ker (KoszulExterior.gradedDifferential p k) := by
      apply Subtype.ext
      exact congrArg (fun w : space (R := R) d L W k => w.val) hx
    rw [hex k] at hz
    obtain ⟨y, hy⟩ := hz
    refine ⟨⟨weightProjection d L y.val, weightProjection_exteriorGrade_mem d L W (k + 2) hW y⟩, ?_⟩
    apply Subtype.ext
    change KoszulExterior.differential p (weightProjection d L y.val) = x.val
    rw [← weightProjection_differential p d L hp]
    have he : KoszulExterior.differential p y.val = x.val := congrArg Subtype.val hy
    rw [he, weightProjection_space d L L W (k + 1) x.val x.property, ite_eq_left rfl]
  · rintro x ⟨y, rfl⟩
    have he := LinearMap.congr_fun (differential_comp p d L W hp hW k) y
    exact he


variable {K : Type*} [Field K] [IsAlgClosed K]

theorem weighted_exact_of_no_nonzero_root (p : Fin n → Poly n K) (d : Fin n → ℕ) (L W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hd : ∀ i, 0 < d i) (hW : L < 2 ^ W)
    (hroot : ∀ x : Fin n → K, (∀ i, MvPolynomial.eval x (p i) = 0) → x = 0) (k : ℕ) :
    LinearMap.ker (differential p d L W hp hW k) =
      LinearMap.range (differential p d L W hp hW (k + 1)) :=
  weighted_exact_of_graded_exact p d L W hp hW
    (KoszulExterior.graded_exact_of_no_nonzero_root p d hp hd hroot) k

end LeanCanny.Algebra.KoszulWeighted
