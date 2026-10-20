/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.KoszulWeightedComplex

/-! # Recovering the Macaulay multiplication entries from the weighted complex

The degree-one word for a multiplier row has exactly the existing multiplier
weight. Its exterior differential is the scalar image of that polynomial
row. Scalar retraction and coefficient extraction recover every entry of the
full rectangular Macaulay matrix.
-/

@[expose] public section

namespace LeanCanny.Algebra.KoszulWeighted
variable {n : ℕ} {R : Type*} [CommRing R]

theorem blade_one (i : Fin n) :
    blade (R := R) (fun _ : Fin 1 => i) = ExteriorAlgebra.ι (Poly n R) (Pi.single i 1 : Fin n → Poly n R) := by
  rw [blade_succ, blade_zero, mul_one]

noncomputable def macaulaySourceIndex (d : Fin n → ℕ) (W : ℕ) (a : Macaulay.MultiplierIndex d W) :
    Index d (Macaulay.level d) W 1 := by
  refine ⟨(fun _ : Fin 1 => a.1), a.2.val, ?_⟩
  rw [mem_indices]
  have hg := (Macaulay.mem_multiplierIndices d W a.1 a.2.val).mp a.2.property
  simpa only [wordWeight, Fin.sum_univ_one] using hg

theorem differential_macaulay_generator (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (a : Macaulay.MultiplierIndex d W) :
    KoszulExterior.differential p (generator (R := R) d (Macaulay.level d) W 1 (macaulaySourceIndex d W a)) =
      algebraMap (Poly n R) (Total n R) (Macaulay.sourceRow p d W a) := by
  have hi : KoszulExterior.differential p (ExteriorAlgebra.ι (Poly n R) (Pi.single a.1 1 : Fin n → Poly n R)) =
      algebraMap (Poly n R) (Total n R) (p a.1) := by
    rw [KoszulExterior.differential_ι]
    exact congrArg (algebraMap (Poly n R) (Total n R)) (KoszulExterior.linearForm_single p a.1)
  change KoszulExterior.differential p (monomialBlade (R := R) (fun _ : Fin 1 => a.1)
    (FixedWidthPolynomial.vector n W a.2.val)) = _
  rw [monomialBlade, blade_one, map_smul, hi, Algebra.smul_def, ← map_mul]
  rfl

theorem weightedDifferential_macaulay_generator (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W) (a : Macaulay.MultiplierIndex d W) :
    (differential p d (Macaulay.level d) W hp hW 0
      ⟨generator (R := R) d (Macaulay.level d) W 1 (macaulaySourceIndex d W a), generator_mem _ _ _ _ _⟩).val =
      algebraMap (Poly n R) (Total n R) (Macaulay.sourceRow p d W a) :=
  differential_macaulay_generator p d W a

theorem weightedDifferential_macaulay_entry (p : Fin n → Poly n R) (d : Fin n → ℕ) (W : ℕ)
    (hp : ∀ i, (p i).IsHomogeneous (d i)) (hW : Macaulay.level d < 2 ^ W)
    (a : Macaulay.MultiplierIndex d W) (r : Macaulay.activeIndices d W) :
    (ExteriorAlgebra.algebraMapInv
      (differential p d (Macaulay.level d) W hp hW 0
        ⟨generator (R := R) d (Macaulay.level d) W 1 (macaulaySourceIndex d W a), generator_mem _ _ _ _ _⟩).val).coeff
          (FixedWidthPolynomial.vector n W r.val) = Macaulay.fullMatrix p d W a r := by
  rw [weightedDifferential_macaulay_generator]
  have h := ExteriorAlgebra.algebraMap_leftInverse (Fin n → Poly n R) (Macaulay.sourceRow p d W a)
  rw [h]
  rfl

end LeanCanny.Algebra.KoszulWeighted
