/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PrincipalSubresultant.Query
public import LeanCanny.Algebra.PrincipalSubresultant.Minor

/-! # Tarski queries from explicit principal determinant signs

The derivative product is first reduced modulo the head. The remaining data are
the signs of signed principal subresultants at actual degrees, in descending
index order, with zero gaps retained. An encoded bounded-space evaluator must
still supply the reduced seed and its coefficient access.
-/

@[expose] public section

namespace LeanCanny.Algebra.PrincipalSubresultant
open Polynomial

variable {K L : Type*} [Field K] [LinearOrder K] [Field L] [LinearOrder L]

/-- The coefficient-determinant formula for a whole-line query. -/
noncomputable def principalQuery (p f : K[X]) : ℤ :=
  let q := (f * p.derivative) % p
  permanencesMinusVariations ((List.range (p.natDegree + 1)).reverse.map
    (signedPsc p q p.natDegree q.natDegree))

/-- Sign-preserving field embeddings preserve the complete determinant formula. -/
theorem principalQuery_map (φ : K →+* L)
    (hs : ∀ x, SignType.sign (φ x) = SignType.sign x) (p f : K[X]) :
    principalQuery (p.map φ) (f.map φ) = principalQuery p f := by
  simp only [principalQuery, Polynomial.derivative_map, ← Polynomial.map_mul,
    ← Polynomial.map_mod, natDegree_map]
  apply permanencesMinusVariations_congr
  simp only [List.map_map]
  apply List.map_congr_left
  intro j _
  change SignType.sign (signedPsc (p.map φ) (((f * p.derivative) % p).map φ)
      p.natDegree (((f * p.derivative) % p).natDegree) j) =
    SignType.sign (signedPsc p ((f * p.derivative) % p)
      p.natDegree (((f * p.derivative) % p).natDegree) j)
  rw [signedPsc_map_map]
  exact hs _

end LeanCanny.Algebra.PrincipalSubresultant

namespace LeanCanny.Algebra.RootSignQueries
open Polynomial PrincipalSubresultant
open scoped Classical

/-- Tarski queries use signs of explicit determinant coefficients, including
multiple roots, vanishing queries, and constant or zero heads. -/
theorem tarskiQuery_eq_principalQuery (p f : ℝ[X]) :
    tarskiQuery p f = principalQuery p f := by
  by_cases hp : p.natDegree = 0
  · have hz : p.roots = 0 := by rw [eq_C_of_natDegree_eq_zero hp]; simp
    simp [tarskiQuery, signSum, hz, principalQuery, hp]
  · exact (Sturm.remainderIndex_tarskiSeed (Sturm.IsTarskiSeed.mod p f)).symm.trans
      (remainderIndex_eq_permanences_signedPsc (natDegree_mod_lt _ hp))

/-- The determinant formula for rational inputs can be evaluated over ℚ. -/
theorem tarskiQuery_principal_rat (p f : ℚ[X]) :
    tarskiQuery (p.map (algebraMap ℚ ℝ)) (f.map (algebraMap ℚ ℝ)) =
      principalQuery p f := by
  rw [tarskiQuery_eq_principalQuery]
  apply principalQuery_map
  intro x
  change SignType.sign (x : ℝ) = SignType.sign x
  simp only [sign_apply, Rat.cast_pos, Rat.cast_lt_zero]

/-- Integer inputs use the same formula after promotion to the rational field. -/
theorem tarskiQuery_principal_int (p f : ℤ[X]) :
    tarskiQuery (p.map (algebraMap ℤ ℝ)) (f.map (algebraMap ℤ ℝ)) =
      principalQuery (p.map (algebraMap ℤ ℚ)) (f.map (algebraMap ℤ ℚ)) := by
  simpa only [Polynomial.map_map, ← IsScalarTower.algebraMap_eq ℤ ℚ ℝ] using
    tarskiQuery_principal_rat (p.map (algebraMap ℤ ℚ)) (f.map (algebraMap ℤ ℚ))

/-- Sign-pattern counting reduces to these explicit principal determinant formulas. -/
theorem scaledRootCount_eq_principalQuery {J : Type*} [Fintype J] (p : ℝ[X])
    (Q : J → ℝ[X]) (σ : J → SignType) :
    scaledRootCount p Q σ =
      ∑ e : J → Fin 3, patternWeight σ e * principalQuery p (queryPolynomial Q e) := by
  simp only [scaledRootCount, tarskiQuery_eq_principalQuery]

end LeanCanny.Algebra.RootSignQueries
