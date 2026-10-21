/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeCharacteristicFinitePersistence
public import LeanCanny.ETR.TubeCharacteristicLowestBounds

/-! # Bounded projection values for finite affine tube fibers

On the certified small positive perturbation interval, the nonzero lowest
quotient polynomial covers all real affine roots when the affine fiber is
finite over an algebraically closed extension. Its padded-dimension degree
bound therefore counts all distinct real projection values, including
values arising only at singular roots.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeCharacteristicQuotient
open LeanCanny.Encoding LeanCanny.Algebra
open scoped Classical

attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree
attribute [local irreducible] Macaulay.matrix Matrix.det

variable (source active : List Bool → List Bool)
  (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool)

section Bounds
variable {L : Type*} [Field L] [IsAlgClosed L] [Algebra ℝ L]

theorem finite_projection_values_of_finite_extension_fiber (read : List Bool → List Bool)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q)))
    (hr : ∀ c i, i < TubeParameter.spatialCount (source c) → read (pair c (BinaryNatCode.encode i)) = (Codec.integer (ell c i)).toBits)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hsmall : epsilon ≤ InfinitesimalSign.dyadic
      (Nat.fromBitsLE (TubeDeformation.specializationExponent source read B.degree B.bits c)))
    (hfinite : (MvPolynomial.zeroLocus L (ProjectiveNullstellensatz.generated
      (finiteSystem source active n d ell c (algebraMap ℝ L epsilon)))).Finite) :
    {u : ℝ | ∃ y, regularSystem source active n d ell c epsilon (u, y) = 0}.Finite := by
  apply (Polynomial.finite_setOfPred_isRoot
    (lowestProjectionPolynomial_ne_zero_of_small source active n d ell c read B hr epsilon hepsilon hsmall)).subset
  rintro u ⟨y, hy⟩
  exact lowestProjectionPolynomial_eval_eq_zero_of_finite_extension_fiber source active n d ell c epsilon hfinite (u, y) hy

theorem projection_values_ncard_le_of_finite_extension_fiber (read : List Bool → List Bool)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q)))
    (hr : ∀ c i, i < TubeParameter.spatialCount (source c) → read (pair c (BinaryNatCode.encode i)) = (Codec.integer (ell c i)).toBits)
    (epsilon : ℝ) (hepsilon : 0 < epsilon)
    (hsmall : epsilon ≤ InfinitesimalSign.dyadic
      (Nat.fromBitsLE (TubeDeformation.specializationExponent source read B.degree B.bits c)))
    (hfinite : (MvPolynomial.zeroLocus L (ProjectiveNullstellensatz.generated
      (finiteSystem source active n d ell c (algebraMap ℝ L epsilon)))).Finite) :
    {u : ℝ | ∃ y, regularSystem source active n d ell c epsilon (u, y) = 0}.ncard ≤
      FixedWidthPolynomial.count (TubeParameter.spatialCount (source c)) (TubeCleared.matrixWidth (source c)) := by
  let p := lowestProjectionPolynomial source active n d ell c epsilon
  have hp : p ≠ 0 := lowestProjectionPolynomial_ne_zero_of_small source active n d ell c read B hr epsilon hepsilon hsmall
  have hsub : {u : ℝ | ∃ y, regularSystem source active n d ell c epsilon (u, y) = 0} ⊆ (p.roots.toFinset : Set ℝ) := by
    rintro u ⟨y, hy⟩
    exact Multiset.mem_toFinset.mpr ((Polynomial.mem_roots hp).mpr
      (lowestProjectionPolynomial_eval_eq_zero_of_finite_extension_fiber source active n d ell c epsilon hfinite (u, y) hy))
  exact (Set.ncard_le_ncard hsub).trans (by
    rw [Set.ncard_coe_finset]
    exact (Multiset.toFinset_card_le p.roots).trans (lowestProjectionPolynomial_roots_card_le source active n d ell c epsilon))
end Bounds

end LeanCanny.ETR.TubeCharacteristicQuotient
