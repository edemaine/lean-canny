/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeCompiledCardinality
public import LeanCanny.ETR.TubeLevelCoordinates
public import LeanCanny.ETR.TubeLevelEliminantSampling
public import LeanCanny.Algebra.FiniteSystemCardinality

/-! # Source degree bounds for the actual rational-level coordinate data

Below a common positive coordinate-projection threshold, the full complex and
algebraic-closure zero sets have a source-only cardinality bound. Every integer
coordinate representation inherits the resulting degree bounds. Coefficient
heights and effective construction are separate obligations.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeCharacteristicQuotient
open LeanCanny.Algebra
variable {K E : Type*} [CommRing K] [CommRing E]

theorem map_lowestProjectionPolynomial (φ : K →+* E) (source active : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) (c : List Bool) (alpha : K) :
    (lowestProjectionPolynomial source active n d ell c alpha).map φ =
      lowestProjectionPolynomial source active n d ell c (φ alpha) := by
  unfold lowestProjectionPolynomial
  rw [Polynomial.map_map]
  have he : φ.comp (Polynomial.eval₂RingHom (Int.castRingHom K) alpha) =
      Polynomial.eval₂RingHom (Int.castRingHom E) (φ alpha) := by
    ext <;> simp
  rw [he]

end LeanCanny.ETR.TubeCharacteristicQuotient

namespace LeanCanny.ETR.TubeLevelPacket
open LeanCanny.Encoding LeanCanny.Algebra
open Geometry TubeEncoding TubeProjectionEncoding TubeCompiledAffineRoots
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm CompactSource.term
attribute [local irreducible] Macaulay.matrix Matrix.det TubeCleared.uniformDegree

noncomputable def coordinateThreshold (c : List Bool) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty
    (fun j : Fin (pointCount (TubeIndexed.arity (pairFst c)) + 1) =>
      eliminantThreshold c (coordinateDirection j.val))

theorem coordinateThreshold_pos (c : List Bool) : 0 < coordinateThreshold c := by
  apply (Finset.lt_inf'_iff _).mpr
  intro j _
  exact eliminantThreshold_pos c _

theorem coordinateThreshold_le (c : List Bool) (j : Fin (pointCount (TubeIndexed.arity (pairFst c)) + 1)) :
    coordinateThreshold c ≤ eliminantThreshold c (coordinateDirection j.val) :=
  Finset.inf'_le _ (Finset.mem_univ j)

theorem complex_solution_ncard_le (c mask : List Bool) (ell : ℕ → ℤ) (alpha : ℝ)
    (hf : FiniteCompiledFibers.{0} c alpha) (hp : 0 < alpha) (hs : alpha ≤ coordinateThreshold c) :
    (RootSet pairFst (fun _ => mask) numerator denominator (fun _ => ell) c (algebraMap ℝ ℂ alpha)).ncard ≤
      solutionBound (pairFst c) := by
  apply (finite_and_ncard_le pairFst (fun _ => mask) numerator denominator (fun _ => ell)
    c (algebraMap ℝ ℂ alpha) (fun i _ => denominator_eval_ne_zero c i _) ?_ ?_).2
  · intro j
    exact hf ℂ (fun _ => mask) (fun _ => coordinateDirection j.val)
  · intro j
    have he := TubeCharacteristicQuotient.map_lowestProjectionPolynomial (algebraMap ℝ ℂ)
      pairFst (fun _ => mask) numerator denominator (fun _ => coordinateDirection j.val) c alpha
    change TubeCharacteristicQuotient.lowestProjectionPolynomial _ _ _ _ _ _ _ ≠ 0
    rw [← he]
    exact Polynomial.map_ne_zero (eliminant_ne_zero_of_small c mask _ alpha hp
      (hs.trans (coordinateThreshold_le c j)))

theorem rational_solution_ncard_le (c mask : List Bool) (ell : ℕ → ℤ) (alpha : ℚ)
    (hf : FiniteCompiledFibers.{0} c (alpha : ℝ)) (hp : 0 < (alpha : ℝ))
    (hs : (alpha : ℝ) ≤ coordinateThreshold c) :
    (FiniteSystemCoordinates.zeroSet (L := AlgebraicClosure ℚ) (rationalSystem c mask ell alpha)).ncard ≤
      solutionBound (pairFst c) := by
  have he : FiniteSystemCoordinates.zeroSet (L := ℂ) (rationalSystem c mask ell alpha) =
      RootSet pairFst (fun _ => mask) numerator denominator (fun _ => ell) c (algebraMap ℝ ℂ (alpha : ℝ)) := by
    ext z
    change (∀ j, MvPolynomial.eval₂ (algebraMap ℚ ℂ) z (rationalSystem c mask ell alpha j) = 0) ↔ _
    simp_rw [eval_rationalSystem]
    have hc : algebraMap ℚ ℂ alpha = algebraMap ℝ ℂ (alpha : ℝ) := by simp
    rw [hc]
    rfl
  have hfin : (FiniteSystemCoordinates.zeroSet (L := ℂ) (rationalSystem c mask ell alpha)).Finite := by
    rw [he]
    have hf' := hf ℂ (fun _ => mask) (fun _ => ell)
    rw [ProjectiveNullstellensatz.zeroLocus_generated] at hf'
    exact hf'
  let f : AlgebraicClosure ℚ →ₐ[ℚ] ℂ := IsAlgClosed.lift
  have hcard := FiniteSystemCoordinates.ncard_le_of_embedding (rationalSystem c mask ell alpha) f hfin
  rw [he] at hcard
  exact hcard.trans (complex_solution_ncard_le c mask ell (alpha : ℝ) hf hp hs)

theorem integer_coordinate_degrees (c mask : List Bool) (ell : ℕ → ℤ) (alpha : ℚ)
    (hf : FiniteCompiledFibers.{0} c (alpha : ℝ)) (hp : 0 < (alpha : ℝ))
    (hs : (alpha : ℝ) ≤ coordinateThreshold c)
    {r : FiniteSystemCoordinates.Representation (L := AlgebraicClosure ℚ) (rationalSystem c mask ell alpha)}
    (d : IntegerCoordinatePolynomials.IntegerData r) :
    d.polynomial.natDegree ≤ solutionBound (pairFst c) ∧
      (∀ j, (d.numerator j).natDegree ≤ solutionBound (pairFst c) * solutionBound (pairFst c) + 2) ∧
      ∀ j, (d.denominator j).natDegree ≤ solutionBound (pairFst c) * solutionBound (pairFst c) + 2 := by
  have hB := rational_solution_ncard_le c mask ell alpha hf hp hs
  refine ⟨?_, ?_, ?_⟩
  · rw [d.polynomial_natDegree]
    exact r.polynomial_degree_le _ hB
  · intro j
    rw [d.numerator_natDegree]
    exact r.numerator_degree_le _ hB j
  · intro j
    rw [d.denominator_natDegree]
    exact r.denominator_degree_le _ hB j

end LeanCanny.ETR.TubeLevelPacket
