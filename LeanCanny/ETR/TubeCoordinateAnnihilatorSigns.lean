/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeCoordinateAnnihilatorBudget
public import LeanCanny.ETR.TubeCoordinateAnnihilatorDyadic
public import LeanCanny.ETR.TubeSampleCoefficient
public import LeanCanny.ETR.TubeFiniteLeafSigns
public import LeanCanny.Algebra.FiniteLeafSignResidue
public import LeanCanny.Computation.FiniteBinaryEnvelope

/-! # Native sign feasibility on the actual coordinate annihilants

The determinant family supplies the original residues. Its indexed mass
budgets have a common binary FP envelope over the finite coordinate range.
Exact original degrees, coordinate readers, and expanded sign polynomials
are constructed by the finite-leaf procedure.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeCoordinateAnnihilator
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open Polynomial TubeLevelPacket
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree
attribute [local irreducible] Macaulay.matrix Matrix.det
set_option backward.isDefEq.respectTransparency false

/-- The original height is proof data; the sign algorithm computes bounded
metadata separately from the native determinant budget. -/
noncomputable def originalFamily (packet mask : List Bool → List Bool) (ell : List Bool → ℕ → ℤ)
    (a b : List Bool → ℤ) : SeparableBits.Family where
  polynomial := family packet mask ell a b
  height c := (coefficientMass (family packet mask ell a b c)).size
  coefficient_bound _c k := (coeff_natAbs_le_coefficientMass _ k).trans (Nat.lt_size_self _).le

theorem degreeBound_binary (packet : List Bool → List Bool) (hp : packet ∈ FP) :
    BinaryFn (fun c => TubeCompiledAffineRoots.projectionBound (pairFst (packet c))) := by
  have H := BinaryFn.fromBits (MacaulayBits.dimensionCode_mem_FP
    (TubeCleared.layout_polyTime (mem_FP_comp hp pairFst_mem_FP)))
  simpa only [MacaulayBits.dimensionCode, FixedWidthPolynomial.countCode_code,
    MacaulayBits.fromBits_encode, TubeCleared.layout, Function.comp_apply,
    TubeCompiledAffineRoots.projectionBound] using H

theorem signs_mem_PSPACE (packet mask read : List Bool → List Bool)
    (ell : List Bool → ℕ → ℤ) (a b : List Bool → ℤ)
    (hp : packet ∈ FP) (hm : mask ∈ FP) (hr : read ∈ FP)
    (he : ∀ c i, read (pair c (BinaryNatCode.encode i)) = (Codec.integer (ell c i)).toBits)
    (mag : List Bool → ℕ) (hmag : BinaryFn mag)
    (ha : ∀ c, (a c).natAbs ≤ 2 ^ mag c) (hb : ∀ c, (b c).natAbs ≤ 2 ^ mag c)
    (A : SpaceFunction (PrimitivePairBits.coefficient (fun c => C (a (pairFst (pairFst c))))))
    (B : SpaceFunction (PrimitivePairBits.coefficient (fun c => C (b (pairFst (pairFst c))))))
    (hne : ∀ c i, i < TubeSampleCoefficient.A packet c →
      family packet mask ell a b (pair c (BinaryNatCode.encode i)) ≠ 0)
    (S : FiniteLeafSignBits.Source (TubeSampleCoefficient.A packet)) (R : S.Access) :
    FiniteLeafSignBits.finiteSignLanguage (originalFamily packet mask ell a b)
      (TubeSampleCoefficient.A packet) S ∈ PSPACE := by
  obtain ⟨bound, hbound, hle⟩ := (massExponent_binary packet mask read ell hp hm hr he mag hmag).finiteEnvelope
    (TubeSampleCoefficient.A_unary packet hp)
  have hd : ∀ c i, i < TubeSampleCoefficient.A packet c →
      ((originalFamily packet mask ell a b).polynomial (pair c (BinaryNatCode.encode i))).natDegree ≤
        TubeCompiledAffineRoots.projectionBound (pairFst (packet c)) := by
    intro c i hi
    change (family packet mask ell a b (pair c (BinaryNatCode.encode i))).natDegree ≤ _
    rw [family_coordinate packet mask ell a b c ⟨i, hi⟩]
    exact integerCoordinateAnnihilator_degree _ _ _ _ _ _
  have hmass : ∀ c i, i < TubeSampleCoefficient.A packet c →
      coefficientMass ((originalFamily packet mask ell a b).polynomial (pair c (BinaryNatCode.encode i))) ≤
        2 ^ bound c := by
    intro c i hi
    exact (family_mass packet mask read ell hp hm hr he a b mag ha hb _).trans
      (Nat.pow_le_pow_right (by decide) (hle c i hi))
  exact FiniteLeafSignBits.finiteSignLanguage_mem_PSPACE_from_residues
    (originalFamily packet mask ell a b) (TubeSampleCoefficient.A packet)
    (fun c => TubeCompiledAffineRoots.projectionBound (pairFst (packet c))) bound hne hd hmass S R
    (TubeSampleCoefficient.A_unary packet hp) (degreeBound_binary packet hp) hbound
    (family_evaluator packet mask read ell a b hp hm hr he A B)

/-- At the computed implicit level, all original annihilator coefficients,
degrees, mass budgets, and nonvanishing proofs are supplied internally. -/
theorem dyadic_signs_mem_PSPACE (packet mask read : List Bool → List Bool)
    (ell : List Bool → ℕ → ℤ) (hp : packet ∈ FP) (hm : mask ∈ FP) (hr : read ∈ FP)
    (he : ∀ c i, read (pair c (BinaryNatCode.encode i)) = (Codec.integer (ell c i)).toBits)
    (S : FiniteLeafSignBits.Source (TubeSampleCoefficient.A packet)) (R : S.Access) :
    FiniteLeafSignBits.finiteSignLanguage
      (originalFamily packet mask ell (fun _ => 1) (dyadicDenominator packet mask read ell hp hm hr he))
      (TubeSampleCoefficient.A packet) S ∈ PSPACE := by
  have hE := dyadicExponent_binary packet mask read ell hp hm hr he
  have hEc := hE.comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  apply signs_mem_PSPACE packet mask read ell (fun _ => 1)
    (dyadicDenominator packet mask read ell hp hm hr he) hp hm hr he
    (dyadicExponent packet mask read ell hp hm hr he) hE
    (fun _ => by simpa using Nat.one_le_two_pow)
    (fun _ => by simp only [dyadicDenominator, Int.natAbs_natCast]; exact le_rfl)
    (by simpa only [Polynomial.C_1] using DyadicConstantBits.oneCoefficientEvaluator)
    (DyadicConstantBits.coefficientEvaluator hEc)
  · intro c i hi
    exact dyadicFamily_ne_zero packet mask read ell hp hm hr he c ⟨i, hi⟩
  · exact R

theorem dyadic_tube_signs_mem_PSPACE (packet mask read : List Bool → List Bool)
    (ell : List Bool → ℕ → ℤ) (hp : packet ∈ FP) (hm : mask ∈ FP) (hr : read ∈ FP)
    (he : ∀ c i, read (pair c (BinaryNatCode.encode i)) = (Codec.integer (ell c i)).toBits)
    (pattern : List Bool → ℕ → SignType) (readPattern : List Bool → List Bool)
    (hs : readPattern ∈ FP)
    (hpattern : ∀ c j, readPattern (pair c (BinaryNatCode.encode j)) = InfinitesimalSign.encode (pattern c j)) :
    TubeFiniteLeafSigns.language packet pattern
      (originalFamily packet mask ell (fun _ => 1) (dyadicDenominator packet mask read ell hp hm hr he)) ∈ PSPACE := by
  rw [TubeFiniteLeafSigns.language_eq]
  exact dyadic_signs_mem_PSPACE packet mask read ell hp hm hr he
    (TubeFiniteLeafSigns.source packet pattern)
    (TubeFiniteLeafSigns.access packet pattern hp readPattern hs hpattern)

end LeanCanny.ETR.TubeCoordinateAnnihilator
