/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeCoordinateAnnihilatorFamily

/-! # Binary coefficient-mass budgets for native tube annihilators

A native binary exponent controls the rational numerator and denominator.
Combining it with the complete determinant budget gives a binary coefficient
mass bound for each indexed coordinate annihilator, without writing the large
rational constants explicitly.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeCoordinateAnnihilator
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra Polynomial TubeLevelPacket
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree
attribute [local irreducible] Macaulay.matrix Matrix.det
set_option maxHeartbeats 100000

variable (packet mask read : List Bool → List Bool) (ell : List Bool → ℕ → ℤ)
variable (hp : packet ∈ FP) (hm : mask ∈ FP) (hr : read ∈ FP)
variable (he : ∀ c i, read (pair c (BinaryNatCode.encode i)) = (Codec.integer (ell c i)).toBits)

noncomputable def rawMassExponent (c : List Bool) : ℕ :=
  let T := indexedData packet mask read ell hp hm hr he
  Nat.fromBitsLE (TubeDeformation.specializationMassCode (pairFst ∘ indexedPacket packet)
    T.direction T.bounds.degree T.bounds.bits c)

theorem rawMassExponent_binary : BinaryFn (rawMassExponent packet mask read ell hp hm hr he) := by
  let T := indexedData packet mask read ell hp hm hr he
  exact BinaryFn.fromBits (TubeDeformation.specializationMassCode_mem_FP T.sourceFP T.directionFP
    T.bounds.degreeFP T.bounds.bitsFP)

noncomputable def massExponent (mag : List Bool → ℕ) (c : List Bool) : ℕ :=
  (TubeCompiledAffineRoots.projectionBound (pairFst (indexedPacket packet c)) + 1).size +
    rawMassExponent packet mask read ell hp hm hr he c +
      mag (pairFst c) * annihilatorInnerDegree (indexedPacket packet c)

theorem massExponent_binary (mag : List Bool → ℕ) (hmag : BinaryFn mag) :
    BinaryFn (massExponent packet mask read ell hp hm hr he mag) := by
  have hP := mem_FP_comp pairFst_mem_FP hp
  have hcount := BinaryFn.fromBits
    (MacaulayBits.dimensionCode_mem_FP (TubeCleared.layout_polyTime (mem_FP_comp hP pairFst_mem_FP)))
  simp only [MacaulayBits.dimensionCode, FixedWidthPolynomial.countCode_code,
    MacaulayBits.fromBits_encode] at hcount
  have hmag' : BinaryFn (fun c => mag (pairFst c)) := hmag.comp pairFst_mem_FP
  have hinner : BinaryFn (fun c => annihilatorInnerDegree (indexedPacket packet c)) :=
    annihilatorInnerDegree_binary.comp hP
  exact ((hcount.add (BinaryFn.const 1)).size.add
    (rawMassExponent_binary packet mask read ell hp hm hr he)).add
      (hmag'.mul hinner)

theorem family_mass (a b : List Bool → ℤ) (mag : List Bool → ℕ)
    (ha : ∀ c, (a c).natAbs ≤ 2 ^ mag c) (hb : ∀ c, (b c).natAbs ≤ 2 ^ mag c) (c : List Bool) :
    coefficientMass (family packet mask ell a b c) ≤
      2 ^ massExponent packet mask read ell hp hm hr he mag c := by
  let T := indexedData packet mask read ell hp hm hr he
  have hm' (j : ℕ) : coefficientMass
      ((TubeDeformation.lowestCoefficient (pairFst ∘ indexedPacket packet) (mask ∘ pairFst)
        (fun c => numerator (indexedPacket packet c)) (fun c => denominator (indexedPacket packet c))
        (selectedDirection ell) c).coeff j) ≤
      2 ^ rawMassExponent packet mask read ell hp hm hr he c :=
    TubeDeformation.lowestCoefficient_coefficient_mass (pairFst ∘ indexedPacket packet) (mask ∘ pairFst)
      T.direction (fun c => numerator (indexedPacket packet c)) (fun c => denominator (indexedPacket packet c))
      (selectedDirection ell) T.bounds T.direction_eq c j
  have hcleared := specialize_mass (annihilatorInnerDegree (indexedPacket packet c))
    (TubeCompiledAffineRoots.projectionBound (pairFst (indexedPacket packet c)))
    (2 ^ rawMassExponent packet mask read ell hp hm hr he c) (a (pairFst c)) (b (pairFst c))
    (annihilatorBivariate (indexedPacket packet c) (mask (pairFst c)) (selectedDirection ell c))
    (annihilatorBivariate_inner_degree _ _ _) (annihilatorBivariate_degree _ _ _) hm'
  have hM : max (a (pairFst c)).natAbs (b (pairFst c)).natAbs ≤ 2 ^ mag (pairFst c) :=
    max_le (ha _) (hb _)
  apply hcleared.trans
  calc
    _ ≤ 2 ^ (TubeCompiledAffineRoots.projectionBound (pairFst (indexedPacket packet c)) + 1).size *
        (2 ^ rawMassExponent packet mask read ell hp hm hr he c *
          (2 ^ mag (pairFst c)) ^ annihilatorInnerDegree (indexedPacket packet c)) :=
      Nat.mul_le_mul (Nat.lt_size_self _).le (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hM _))
    _ = _ := by rw [massExponent, ← pow_mul, ← pow_add, ← pow_add, Nat.add_assoc]

end LeanCanny.ETR.TubeCoordinateAnnihilator
