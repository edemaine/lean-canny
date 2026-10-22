/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeCompiledReprojection
public import LeanCanny.ETR.TubeCharacteristicLowestBounds
public import Mathlib.Data.Fintype.BigOperators

/-! # Full solution-count bounds from coordinate eliminants

Every spatial coordinate lies among the roots of its own nonzero projection
polynomial. The original linear row determines the extra projection coordinate,
so the full root set injects into a product of univariate root sets. Singular
roots and reciprocal coordinates are included.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeCompiledAffineRoots
open LeanCanny.Encoding LeanCanny.Algebra
open Geometry TubeEncoding TubeProjectionEncoding TubeCharacteristicQuotient
open scoped Classical BigOperators
attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree
attribute [local irreducible] Macaulay.matrix Matrix.det

noncomputable def projectionBound (bits : List Bool) : ℕ :=
  FixedWidthPolynomial.count (TubeParameter.spatialCount bits) (TubeCleared.matrixWidth bits)

noncomputable def solutionBound (bits : List Bool) : ℕ :=
  projectionBound bits ^ (pointCount (TubeIndexed.arity bits) + 1)

variable {K : Type*} [Field K] [IsAlgClosed K]
variable (source active : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ)
  (ell : List Bool → ℕ → ℤ) (c : List Bool) (epsilon : K)

noncomputable def coordinatePolynomial
    (j : Fin (pointCount (TubeIndexed.arity (source c)) + 1)) : Polynomial K :=
  lowestProjectionPolynomial source active n d (fun _ => coordinateDirection j.val) c epsilon

omit [IsAlgClosed K] in
theorem coordinatePolynomial_degree
    (j : Fin (pointCount (TubeIndexed.arity (source c)) + 1)) :
    (coordinatePolynomial source active n d c epsilon j).natDegree ≤ projectionBound (source c) :=
  Polynomial.natDegree_map_le.trans
    (polynomial_trailingCoeff_projection_degree_le source active n d (fun _ => coordinateDirection j.val) c)

theorem finite_and_ncard_le
    (hd : ∀ i, i < TubeParameter.parameterCount (source c) →
      (d c i).eval₂ (Int.castRingHom K) epsilon ≠ 0)
    (hf : ∀ j : Fin (pointCount (TubeIndexed.arity (source c)) + 1),
      (MvPolynomial.zeroLocus K (ProjectiveNullstellensatz.generated
        (finiteSystem source active n d (fun _ => coordinateDirection j.val) c epsilon))).Finite)
    (hne : ∀ j, coordinatePolynomial source active n d c epsilon j ≠ 0) :
    (RootSet source active n d ell c epsilon).Finite ∧
      (RootSet source active n d ell c epsilon).ncard ≤ solutionBound (source c) := by
  let P := coordinatePolynomial source active n d c epsilon
  let t := Fintype.piFinset (fun j => (P j).roots.toFinset)
  let tail := fun z : Fin (TubeParameter.spatialCount (source c)) → K =>
    fun j : Fin (pointCount (TubeIndexed.arity (source c)) + 1) => z j.succ
  have hmap : Set.MapsTo tail (RootSet source active n d ell c epsilon) (t : Set _) := by
    intro z hz
    apply Fintype.mem_piFinset.mpr
    intro j
    apply Multiset.mem_toFinset.mpr
    apply (Polynomial.mem_roots (hne j)).mpr
    have hsp := spatial_roots_of_compiled source active n d ell c epsilon hd z hz
    have hr := compiled_root_of_spatial source active n d (fun _ => coordinateDirection j.val)
      c epsilon hd (decodedPoint (source c) z) hsp
    have hm : compiledPoint (source c) (coordinateDirection j.val) (decodedPoint (source c) z) ∈
        MvPolynomial.zeroLocus K (ProjectiveNullstellensatz.generated
          (finiteSystem source active n d (fun _ => coordinateDirection j.val) c epsilon)) := by
      rw [ProjectiveNullstellensatz.zeroLocus_generated]
      exact hr
    have he := lowestProjectionPolynomial_eval_eq_zero_of_finite_fiber source active n d
      (fun _ => coordinateDirection j.val) c epsilon (hf j) _ hm
    rw [coordinate_projection] at he
    exact he
  have hi := tail_injective_on_roots source active n d ell c epsilon
  have ht := Finset.finite_toSet t
  refine ⟨ht.of_injOn hmap hi, (Set.ncard_le_ncard_of_injOn tail hmap hi ht).trans ?_⟩
  rw [Set.ncard_coe_finset, Fintype.card_piFinset]
  calc
    _ ≤ ∏ _j : Fin (pointCount (TubeIndexed.arity (source c)) + 1), projectionBound (source c) := by
      apply Finset.prod_le_prod
      intro j _
      exact (Multiset.toFinset_card_le _).trans
        ((Polynomial.card_roots' _).trans (coordinatePolynomial_degree source active n d c epsilon j))
    _ = solutionBound (source c) := by simp [solutionBound]

end LeanCanny.ETR.TubeCompiledAffineRoots
