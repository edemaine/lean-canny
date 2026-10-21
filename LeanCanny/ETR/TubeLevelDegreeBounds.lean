/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeCoordinateThreshold
public import LeanCanny.ETR.TubeLevelSignNative

/-! # Source-derived degree controls for native tube sample counting

The source alone gives binary solution-count and coordinate-degree allowances.
At sufficiently small positive levels, only coefficient-mass bounds and native
root/coordinate readers remain as resource hypotheses of the sign-stage theorem.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeCompiledAffineRoots
open LeanCanny.Encoding LeanCanny.Algebra
open Geometry TubeProjectionEncoding
attribute [local irreducible] RationalSubstitutionBits.compiledTerm BinaryNat.add BinaryNat.mul

noncomputable def solutionBoundCode : List Bool → List Bool :=
  FixedWidthPolynomial.countCode
    (fun bits => TubeParameter.spatialCount bits * (pointCount (TubeIndexed.arity bits) + 1)) TubeCleared.matrixWidth

theorem solutionBoundCode_mem_FP : solutionBoundCode ∈ FP :=
  FixedWidthPolynomial.countCode_mem_FP
    (TubeParameter.spatialCount_unary.mul
      ((TubeProjectionQuery.pointCount_unary TubeIndexed.arity_unary).add (UnaryFn.const 1))) TubeCleared.matrixWidth_unary

theorem solutionBoundCode_eq (bits : List Bool) : solutionBoundCode bits = BinaryNatCode.encode (solutionBound bits) := by
  rw [solutionBoundCode, FixedWidthPolynomial.countCode_code]
  congr 1
  exact pow_mul _ _ _

theorem solutionBound_pos (bits : List Bool) : 0 < solutionBound bits :=
  Nat.pow_pos (Nat.pow_pos (Nat.two_pow_pos _))

noncomputable def coordinateDegreeCode (bits : List Bool) : List Bool :=
  BinaryNat.add (pair (BinaryNat.mul (pair (solutionBoundCode bits) (solutionBoundCode bits))) (BinaryNatCode.encode 2))

theorem coordinateDegreeCode_mem_FP : coordinateDegreeCode ∈ FP := by
  have hm := mem_FP_comp (mem_FP_pair solutionBoundCode_mem_FP solutionBoundCode_mem_FP) BinaryNat.mul_mem_FP
  have he := mem_FP_comp (mem_FP_pair hm (constFn_mem_FP (BinaryNatCode.encode 2))) BinaryNat.add_mem_FP
  exact mem_FP_of_eq he (fun _ => rfl)

theorem coordinateDegreeCode_eq (bits : List Bool) : coordinateDegreeCode bits =
    BinaryNatCode.encode (solutionBound bits * solutionBound bits + 2) := by
  simp only [coordinateDegreeCode, solutionBoundCode_eq, BinaryNat.add_pair, BinaryNat.mul_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]

end LeanCanny.ETR.TubeCompiledAffineRoots

namespace LeanCanny.ETR.TubeLevelSign
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open TubeLevelPacket TubeCompiledAffineRoots
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm

def SmallLevels (S : Source) : Prop := ∀ c,
  0 < (S.level c : ℝ) ∧ (S.level c : ℝ) ≤ coordinateThreshold (S.packet c)

/-- Degree bounds are derived from the actual system, while height bounds remain supplied. -/
structure MassBudget (S : Source) where
  rootMass : List Bool → List Bool
  mass : List Bool → List Bool
  rootMassFP : rootMass ∈ FP
  massFP : mass ∈ FP
  root_mass : ∀ c, coefficientMass (S.coordinates c).polynomial ≤ 2 ^ Nat.fromBitsLE (rootMass c)
  numerator_mass : ∀ c j, coefficientMass ((S.coordinates c).numerator j) ≤ 2 ^ Nat.fromBitsLE (mass c)
  denominator_mass : ∀ c j, coefficientMass ((S.coordinates c).denominator j) ≤ 2 ^ Nat.fromBitsLE (mass c)

namespace MassBudget
attribute [local irreducible] solutionBoundCode coordinateDegreeCode
variable {S : Source}

noncomputable def coordinateBudget (M : MassBudget S) (hp : S.packet ∈ FP) (hl : SmallLevels S) : CoordinateBudget S where
  rootDegree c := solutionBoundCode (pairFst (S.packet c))
  degree c := coordinateDegreeCode (pairFst (S.packet c))
  rootMass := M.rootMass
  mass := M.mass
  rootDegreeFP := by
    have he := mem_FP_comp (mem_FP_comp hp pairFst_mem_FP) solutionBoundCode_mem_FP
    exact mem_FP_of_eq he (fun _ => rfl)
  degreeFP := by
    have he := mem_FP_comp (mem_FP_comp hp pairFst_mem_FP) coordinateDegreeCode_mem_FP
    exact mem_FP_of_eq he (fun _ => rfl)
  rootMassFP := M.rootMassFP
  massFP := M.massFP
  rootDegree_pos c := by
    rw [solutionBoundCode_eq, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact solutionBound_pos _
  root_degree c := by
    rw [solutionBoundCode_eq, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact (integer_coordinate_degrees (S.packet c) (S.mask c) (S.projection c) (S.level c)
      (S.finite c) (hl c).1 (hl c).2 (S.coordinates c)).1
  root_mass := M.root_mass
  numerator_degree c j := by
    rw [coordinateDegreeCode_eq, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact (integer_coordinate_degrees (S.packet c) (S.mask c) (S.projection c) (S.level c)
      (S.finite c) (hl c).1 (hl c).2 (S.coordinates c)).2.1 j
  denominator_degree c j := by
    rw [coordinateDegreeCode_eq, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    exact (integer_coordinate_degrees (S.packet c) (S.mask c) (S.projection c) (S.level c)
      (S.finite c) (hl c).1 (hl c).2 (S.coordinates c)).2.2 j
  numerator_mass := M.numerator_mass
  denominator_mass := M.denominator_mass

theorem sampleLanguage_mem_PSPACE (M : MassBudget S) (C : CoefficientReaders S)
    (hp : S.packet ∈ FP) (hm : S.mask ∈ FP) (hl : SmallLevels S) : sampleLanguage S ∈ PSPACE :=
  C.sampleLanguage_mem_PSPACE (M.coordinateBudget hp hl) hp hm

theorem countEvaluator (M : MassBudget S) (C : CoefficientReaders S)
    (hp : S.packet ∈ FP) (hm : S.mask ∈ FP) (hl : SmallLevels S) :
    SpaceFunction (fun c => BinaryNatCode.encode (sampleCount S c)) :=
  C.countEvaluator (M.coordinateBudget hp hl) hp hm

end MassBudget
end LeanCanny.ETR.TubeLevelSign
