/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeDeformationSystem
public import LeanCanny.Algebra.DeformationLowestCoefficient

/-! # The lowest coefficient of the full tube deformation

The candidate is nonzero, with the proved inner-degree allowance. A converging
family of nonzero homogeneous roots of the actual deformed tube system forces
the candidate to vanish at the limiting coefficient parameters. The existence
of such families for isolated original solutions, and the relation to the
resultant quotient, remain separate obligations.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeDeformation
open Complexity LeanCanny.Encoding LeanCanny.Algebra
open Polynomial Filter
open scoped Topology

attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree
attribute [local irreducible] Macaulay.matrix Matrix.det

noncomputable def lowestCoefficient (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) : Polynomial (Polynomial ℤ) :=
  (determinant source active n d ell c).trailingCoeff

theorem lowestCoefficient_ne_zero (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) :
    lowestCoefficient source active n d ell c ≠ 0 :=
  Polynomial.trailingCoeff_nonzero_iff_nonzero.mpr (determinant_ne_zero source active n d ell c)

theorem determinant_map_ne_zero {K : Type*} [CommRing K] [Nontrivial K]
    (source active : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ)
    (c : List Bool) (φ : Polynomial (Polynomial ℤ) →+* K) :
    (determinant source active n d ell c).map φ ≠ 0 := by
  have h : ((determinant source active n d ell c).map φ).eval 1 = 1 := by
    rw [Polynomial.eval_map, Polynomial.eval₂_at_one, determinant_at_one, map_one]
  intro hz
  rw [hz, Polynomial.eval_zero] at h
  exact zero_ne_one h

theorem lowestCoefficient_eval_zero_iff_order_increases {K : Type*} [CommRing K] [Nontrivial K]
    (source active : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ)
    (c : List Bool) (φ : Polynomial (Polynomial ℤ) →+* K) :
    φ (lowestCoefficient source active n d ell c) = 0 ↔
      (determinant source active n d ell c).natTrailingDegree <
        ((determinant source active n d ell c).map φ).natTrailingDegree := by
  rw [lowestCoefficient, DeformationLowestCoefficient.map_trailingCoeff_eq_zero_iff,
    or_iff_right (determinant_map_ne_zero source active n d ell c φ)]

theorem lowestCoefficient_inner_degree (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q))) (c : List Bool) (j : ℕ) :
    ((lowestCoefficient source active n d ell c).coeff j).natDegree ≤
      FixedWidthPolynomial.count (TubeParameter.spatialCount (source c)) (TubeCleared.matrixWidth (source c)) *
        Nat.fromBitsLE (TubeCleared.uniformDegree source B.degree c) :=
  determinant_inner_degree source active n d ell B c _ j

noncomputable def parameterEvaluation {K : Type*} [CommRing K] (a : K × K) : Polynomial (Polynomial ℤ) →+* K :=
  Polynomial.eval₂RingHom (Polynomial.eval₂RingHom (Int.castRingHom K) a.1) a.2

theorem continuous_parameterEvaluation {K : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    (p : Polynomial (Polynomial ℤ)) : Continuous (fun a : K × K => parameterEvaluation a p) := by
  exact DeformationLowestCoefficient.continuous_eval₂ p (fun a => Polynomial.eval₂RingHom (Int.castRingHom K) a)
    (fun r => r.continuous_eval₂ (Int.castRingHom K))

theorem lowestCoefficient_vanishes_of_roots_tendsto
    {K I : Type*} [Field K] [TopologicalSpace K] [IsTopologicalRing K] [T2Space K]
    (source active : List Bool → List Bool) (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ)
    (c : List Bool) (l : Filter I) [NeBot l] (a : I → K × K) (s : I → K) (a₀ : K × K)
    (x : I → Fin (TubeParameter.spatialCount (source c)) → K)
    (ha : Tendsto a l (𝓝 a₀)) (hs : Tendsto s l (𝓝 0)) (hne : ∀ᶠ j in l, s j ≠ 0)
    (hroot : ∀ᶠ j in l, ∀ i, MvPolynomial.eval₂
      (Polynomial.eval₂RingHom (parameterEvaluation (a j)) (s j)) (x j) (system source active n d ell c i) = 0)
    (hnz : ∀ᶠ j in l, ∃ i, x j i ≠ 0) :
    parameterEvaluation a₀ (lowestCoefficient source active n d ell c) = 0 := by
  apply DeformationLowestCoefficient.trailingCoeff_eq_zero_of_tendsto
    (determinant source active n d ell c) parameterEvaluation continuous_parameterEvaluation l a s a₀ ha hs hne
  filter_upwards [hroot, hnz] with j hj hnj
  have hW := TubeCleared.level_lt source c
  rw [MacaulayBits.level_eq] at hW
  exact Macaulay.map_det_eq_zero_of_common_root
    (Polynomial.eval₂RingHom (parameterEvaluation (a j)) (s j)) (system source active n d ell c)
    (MacaulayBits.Degrees (TubeCleared.layout source) c) (TubeCleared.matrixWidth (source c))
    (system_homogeneous source active n d ell c) hW (x j) hj hnj

noncomputable def projectionPolynomial {K : Type*} [CommRing K] (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) (a : K) : Polynomial K :=
  (lowestCoefficient source active n d ell c).map (Polynomial.eval₂RingHom (Int.castRingHom K) a)

theorem projectionPolynomial_eval {K : Type*} [CommRing K] (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) (a t : K) :
    (projectionPolynomial source active n d ell c a).eval t =
      parameterEvaluation (a, t) (lowestCoefficient source active n d ell c) := by
  rw [projectionPolynomial, Polynomial.eval_map]
  rfl

theorem lowestCoefficient_specialize {K : Type*} [CommRing K] (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) (a : K)
    (ha : projectionPolynomial source active n d ell c a ≠ 0) :
    ((determinant source active n d ell c).map
      (Polynomial.mapRingHom (Polynomial.eval₂RingHom (Int.castRingHom K) a))).trailingCoeff =
        projectionPolynomial source active n d ell c a :=
  (DeformationLowestCoefficient.trailingCoeff_map_of_nonzero _ _ ha).2

theorem exists_specialization_witness (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ)
    (B : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q))) (c : List Bool) :
    ∃ q : Polynomial ℤ, q ≠ 0 ∧ q.natDegree ≤
      FixedWidthPolynomial.count (TubeParameter.spatialCount (source c)) (TubeCleared.matrixWidth (source c)) *
        Nat.fromBitsLE (TubeCleared.uniformDegree source B.degree c) ∧
      ∀ (K : Type) [CommRing K] (a : K), q.eval₂ (Int.castRingHom K) a ≠ 0 →
        projectionPolynomial source active n d ell c a ≠ 0 := by
  let p := lowestCoefficient source active n d ell c
  have hp : p ≠ 0 := lowestCoefficient_ne_zero source active n d ell c
  refine ⟨p.leadingCoeff, Polynomial.leadingCoeff_ne_zero.mpr hp, lowestCoefficient_inner_degree source active n d ell B c p.natDegree, ?_⟩
  intro K _ a ha hz
  apply ha
  have h := congrArg (fun f : Polynomial K => f.coeff p.natDegree) hz
  change ((p.map (Polynomial.eval₂RingHom (Int.castRingHom K) a)).coeff p.natDegree) = 0 at h
  rw [Polynomial.coeff_map, Polynomial.coeff_natDegree] at h
  exact h

end LeanCanny.ETR.TubeDeformation
