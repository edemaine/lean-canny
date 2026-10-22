/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Geometry.TubeFiniteRoots
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.Data.Rat.Encodable

/-! # A countable coefficient field for each specialized tube

Adjoin the three real parameters to the rationals. The resulting real
subfield is countable and carries the tube coefficient specialization, so
generic-direction independence need only be imposed over this smaller field.
-/

@[expose] public section

namespace LeanCanny.Geometry.TubePolynomial

noncomputable def parameterField (epsilon delta alpha : ℝ) : IntermediateField ℚ ℝ :=
  IntermediateField.adjoin ℚ (Set.range (parameters epsilon delta alpha))

instance countable_parameterField (epsilon delta alpha : ℝ) : Countable (parameterField epsilon delta alpha) := by
  apply Cardinal.mk_le_aleph0_iff.mp
  exact (IntermediateField.cardinalMk_adjoin_le ℚ (Set.range (parameters epsilon delta alpha))).trans
    (sup_le (sup_le Cardinal.mk_le_aleph0 Cardinal.mk_le_aleph0) le_rfl)

noncomputable def fieldParameters (epsilon delta alpha : ℝ) : Parameter → parameterField epsilon delta alpha :=
  fun i => ⟨parameters epsilon delta alpha i, IntermediateField.subset_adjoin ℚ _ (Set.mem_range_self i)⟩

noncomputable def fieldCoefficientMap (epsilon delta alpha : ℝ) : Coefficient →+* parameterField epsilon delta alpha :=
  MvPolynomial.eval₂Hom (Int.castRingHom _) (fieldParameters epsilon delta alpha)

theorem fieldCoefficientMap_comp (epsilon delta alpha : ℝ) :
    (algebraMap (parameterField epsilon delta alpha) ℝ).comp (fieldCoefficientMap epsilon delta alpha) =
      coefficientMap epsilon delta alpha := by
  ext i <;> simp [fieldCoefficientMap, coefficientMap, fieldParameters]

variable {ι : Type*} [Fintype ι]

theorem finite_projectionRootSet_over_parameterField (p : MvPolynomial ι ℤ)
    (s : Finset (PolynomialPerturbation.Constraint ι)) (epsilon delta alpha : ℝ)
    (v : Coordinate ι → ℝ) (hv : v (base ι) = 1)
    (hind : AlgebraicIndependent (parameterField epsilon delta alpha)
      (fun i : {i : Coordinate ι // i ≠ base ι} => v i))
    (hregular : ∀ x : Coordinate ι → ℝ,
      (polynomial p s).eval₂ (coefficientMap epsilon delta alpha) x = 0 →
        Function.Surjective (fderiv ℝ (fun y => (polynomial p s).eval₂ (coefficientMap epsilon delta alpha) y) x)) :
    (projectionRootSet p s epsilon delta alpha v).Finite :=
  finite_projectionRootSet_of_lift p s epsilon delta alpha (fieldCoefficientMap epsilon delta alpha)
    (fieldCoefficientMap_comp epsilon delta alpha) v hv hind hregular

end LeanCanny.Geometry.TubePolynomial
