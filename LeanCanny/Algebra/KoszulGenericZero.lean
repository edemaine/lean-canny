/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulGenericExact

/-! # Degree-zero surjectivity of the finite generic shifted complex

The proved full Macaulay matrix surjectivity transfers through the canonical
index equivalences and then through the canonical coordinate bases.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulWeighted
open scoped Classical Matrix
variable {n : ℕ} {R : Type*} [CommRing R] [IsDomain R]

theorem genericShift_matrix_zero_surjective (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) :
    Function.Surjective (fun v => Matrix.vecMul v (canonicalMatrix (Macaulay.genericShift p d) d (Macaulay.level d) W
      (Macaulay.genericShift_homogeneous p d hp) hW 0)) := by
  intro v
  let M := canonicalMatrix (Macaulay.genericShift p d) d (Macaulay.level d) W
    (Macaulay.genericShift_homogeneous p d hp) hW 0
  let es := macaulaySourceEquiv d W
  let et := macaulayTargetEquiv d W
  obtain ⟨w, hw⟩ := Macaulay.genericShift_vecMul_surjective p d W (v ∘ et)
  change Matrix.vecMul w (Macaulay.fullMatrix (Macaulay.genericShift p d) d W) = v ∘ et at hw
  refine ⟨w ∘ es.symm, ?_⟩
  have hm : M.submatrix es et = Macaulay.fullMatrix (Macaulay.genericShift p d) d W :=
    canonicalMatrix_macaulay _ _ _ _ _
  have he := Matrix.submatrix_vecMul_equiv M w es et
  rw [hm, hw] at he
  funext i
  have hi := congrFun he (et.symm i)
  simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hi.symm

theorem genericShift_weighted_zero_surjective (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) :
    Function.Surjective (differential (Macaulay.genericShift p d) d (Macaulay.level d) W
      (Macaulay.genericShift_homogeneous p d hp) hW 0) :=
  (weighted_surjective_iff_matrix _ d (Macaulay.level d) W _ hW 0).mpr
    (genericShift_matrix_zero_surjective p d W hp hW)

end LeanCanny.Algebra.KoszulWeighted
