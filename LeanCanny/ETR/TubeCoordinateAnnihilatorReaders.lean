/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeCoordinateAnnihilator
public import LeanCanny.ETR.TubeDeformationLowestSpace
public import LeanCanny.ETR.TubeLevelReaders

/-! # Native streamed access to the lowest determinant annihilator

Reindexing the certified tube determinant computation supplies every scalar
coefficient of the bivariate lowest coefficient. Rational specialization then
uses the certified denominator-cleared composition computation.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeCoordinateAnnihilator
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open Polynomial MatrixPower RationalSubstitution.IntegerBits
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree
attribute [local irreducible] Macaulay.matrix Matrix.det

def bivariateContext (q : List Bool) : List Bool := pairFst (context q)
def bivariateOuter (q : List Bool) : List Bool := pairSnd (context q)

theorem bivariateContext_FP : bivariateContext ∈ FP := mem_FP_comp context_mem_FP pairFst_mem_FP

theorem bivariateOuter_FP : bivariateOuter ∈ FP := mem_FP_comp context_mem_FP pairSnd_mem_FP

noncomputable def scalarData {source active modulus inner middle : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : TubeBivariate.Data source active modulus inner middle n d ell) :
    TubeBivariate.Data (source ∘ bivariateContext) (active ∘ bivariateContext)
      pairSnd selectedDegree bivariateOuter (fun q => n (bivariateContext q))
      (fun q => d (bivariateContext q)) (fun q => ell (bivariateContext q)) := by
  let E := D.reindex bivariateContext bivariateContext_FP
  exact ⟨E.coordinates, E.bounds, E.direction, E.sourceFP, E.activeFP,
    pairSnd_mem_FP, selectedDegree_mem_FP, bivariateOuter_FP, E.directionFP, E.direction_eq⟩

theorem lowestBivariate_evaluator {source active modulus inner middle : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (D : TubeBivariate.Data source active modulus inner middle n d ell) :
    SpaceFunction (PrimitivePairBits.coefficient (coefficientPolynomial
      (TubeDeformation.lowestCoefficient source active n d ell))) := by
  have E := TubeDeformation.lowestModularEvaluator (scalarData D)
  refine E.congr (funext fun q => ?_)
  rfl

theorem lowestSpecialization_evaluator {source active modulus inner middle : List Bool → List Bool}
    {n d : List Bool → ℕ → Polynomial ℤ} {ell : List Bool → ℕ → ℤ}
    (T : TubeBivariate.Data source active modulus inner middle n d ell)
    (D : List Bool → ℕ) (a b : List Bool → ℤ) (hD : BinaryFn D)
    (A : SpaceFunction (PrimitivePairBits.coefficient (fun c => C (a (pairFst c)))))
    (B : SpaceFunction (PrimitivePairBits.coefficient (fun c => C (b (pairFst c))))) :
    SpaceFunction (PrimitivePairBits.coefficient (fun c => specialize (D c) (a c) (b c)
      (TubeDeformation.lowestCoefficient source active n d ell c))) :=
  specialize_evaluator _ D a b hD (lowestBivariate_evaluator T) A B

end LeanCanny.ETR.TubeCoordinateAnnihilator

namespace LeanCanny.ETR.TubeLevelPacket
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open Polynomial
attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree
attribute [local irreducible] Macaulay.matrix Matrix.det

theorem annihilatorInnerDegree_binary : BinaryFn annihilatorInnerDegree := by
  have hcount := BinaryFn.fromBits (MacaulayBits.dimensionCode_mem_FP (TubeCleared.layout_polyTime pairFst_mem_FP))
  have hdegree := BinaryFn.fromBits (TubeCleared.uniformDegree_mem_FP pairFst_mem_FP bounds.degreeFP)
  have h := hcount.mul hdegree
  simp only [MacaulayBits.dimensionCode, FixedWidthPolynomial.countCode_code,
    MacaulayBits.fromBits_encode] at h
  exact h

/-- All parameter coefficient readers are supplied by the actual packet compiler. -/
noncomputable def annihilatorData (active modulus inner middle read : List Bool → List Bool)
    (ell : List Bool → ℕ → ℤ) (ha : active ∈ FP) (hm : modulus ∈ FP)
    (hi : inner ∈ FP) (hj : middle ∈ FP) (hr : read ∈ FP)
    (he : ∀ c i, i < TubeParameter.spatialCount (pairFst c) →
      read (pair c (BinaryNatCode.encode i)) = (Codec.integer (ell c i)).toBits) :
    TubeBivariate.Data pairFst active modulus inner middle numerator denominator ell where
  coordinates := readers
  bounds := bounds
  direction := read
  sourceFP := pairFst_mem_FP
  activeFP := ha
  modulusFP := hm
  innerFP := hi
  outerFP := hj
  directionFP := hr
  direction_eq := he

/-- Native constant residue access permits denominators with exponentially many bits. -/
theorem integerAnnihilator_evaluator {active modulus inner middle : List Bool → List Bool}
    {ell : List Bool → ℕ → ℤ}
    (T : TubeBivariate.Data pairFst active modulus inner middle numerator denominator ell)
    (a b : List Bool → ℤ)
    (A : SpaceFunction (PrimitivePairBits.coefficient (fun c => C (a (pairFst c)))))
    (B : SpaceFunction (PrimitivePairBits.coefficient (fun c => C (b (pairFst c))))) :
    SpaceFunction (PrimitivePairBits.coefficient (fun c =>
      integerAnnihilator c (active c) (ell c) (a c) (b c))) := by
  have E := TubeCoordinateAnnihilator.lowestSpecialization_evaluator T annihilatorInnerDegree a b
    annihilatorInnerDegree_binary A B
  refine E.congr (funext fun q => ?_)
  rfl

end LeanCanny.ETR.TubeLevelPacket
