/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeBivariateSource

/-! # Full regular tube Macaulay coefficients in polynomial space

This instance supplies the bivariate determinant backend with its actual tube
source evaluator. The remaining input contracts concern parameter coordinates,
their bounds, integer direction access, and FP input/selection fields. There
is no callback for tube rows or matrix entries. Suspended parameter-reader
workspace is included in the resulting determinant coefficient evaluator.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeBivariate
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra

attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree sourceValue

structure Data (source active modulus inner outer : List Bool → List Bool)
    (n d : List Bool → ℕ → Polynomial ℤ) (ell : List Bool → ℕ → ℤ) where
  coordinates : TubeParameter.CoordinateReaders source (fun q => n (pairFst q)) (fun q => d (pairFst q))
  bounds : TubeParameter.CoordinateBounds source (fun q => n (pairFst q)) (fun q => d (pairFst q))
  direction : List Bool → List Bool
  sourceFP : source ∈ FP
  activeFP : active ∈ FP
  modulusFP : modulus ∈ FP
  innerFP : inner ∈ FP
  outerFP : outer ∈ FP
  directionFP : direction ∈ FP
  direction_eq : ∀ c i, i < TubeParameter.spatialCount (source c) →
    direction (pair c (BinaryNatCode.encode i)) = (Codec.integer (ell c i)).toBits

theorem Data.evaluator {source active modulus inner outer : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : Data source active modulus inner outer n d ell) :
    SpaceFunction (family source active modulus inner outer n d ell D.bounds).value := by
  have ES := sourceEvaluator source active modulus D.direction n d ell D.coordinates
    D.sourceFP D.activeFP D.modulusFP D.directionFP D.direction_eq
  have hM := mem_FP_comp D.modulusFP BinaryNat.succ_mem_FP
  have hB := mem_FP_comp (TubeCleared.uniformDegree_mem_FP D.sourceFP D.bounds.degreeFP) BinaryNat.normalize_mem_FP
  have hI := mem_FP_comp D.innerFP BinaryNat.normalize_mem_FP
  have hO := mem_FP_comp D.outerFP BinaryNat.normalize_mem_FP
  exact (access source active modulus inner outer n d ell D.bounds).evaluator
    (TubeCleared.layout_polyTime D.sourceFP) hM hB hI hO ES

theorem Data.zeroLanguage_mem_PSPACE {source active modulus inner outer : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : Data source active modulus inner outer n d ell) :
    (family source active modulus inner outer n d ell D.bounds).zeroLanguage ∈ PSPACE := by
  have ES := sourceEvaluator source active modulus D.direction n d ell D.coordinates
    D.sourceFP D.activeFP D.modulusFP D.directionFP D.direction_eq
  have hM := mem_FP_comp D.modulusFP BinaryNat.succ_mem_FP
  have hB := mem_FP_comp (TubeCleared.uniformDegree_mem_FP D.sourceFP D.bounds.degreeFP) BinaryNat.normalize_mem_FP
  have hI := mem_FP_comp D.innerFP BinaryNat.normalize_mem_FP
  have hO := mem_FP_comp D.outerFP BinaryNat.normalize_mem_FP
  exact (access source active modulus inner outer n d ell D.bounds).zeroLanguage_mem_PSPACE
    (TubeCleared.layout_polyTime D.sourceFP) hM hB hI hO ES

end LeanCanny.ETR.TubeBivariate
