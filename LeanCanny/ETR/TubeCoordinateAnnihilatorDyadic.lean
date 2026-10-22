/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeCoordinateAnnihilatorBudget
public import LeanCanny.Computation.FiniteBinaryEnvelope
public import LeanCanny.Algebra.DyadicConstantCoefficient

/-! # One implicit dyadic level with nonzero coordinate annihilators

A finite binary envelope bounds every coordinate's lowest-determinant mass
exponent. One additional binary exponent bit-step yields the same rational
level for every coordinate. Its denominator need never be materialized.
This gives algebraic nonvanishing; it makes no geometric sampling claim.
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

noncomputable def dyadicEnvelope :=
  Classical.choose ((rawMassExponent_binary packet mask read ell hp hm hr he).finiteEnvelope
    (TubeParameter.spatialCount_unary.comp (mem_FP_comp hp pairFst_mem_FP)))

theorem dyadicEnvelope_binary : BinaryFn (dyadicEnvelope packet mask read ell hp hm hr he) :=
  (Classical.choose_spec ((rawMassExponent_binary packet mask read ell hp hm hr he).finiteEnvelope
    (TubeParameter.spatialCount_unary.comp (mem_FP_comp hp pairFst_mem_FP)))).1

noncomputable def dyadicExponent (c : List Bool) : ℕ :=
  dyadicEnvelope packet mask read ell hp hm hr he c + 1

theorem dyadicExponent_binary : BinaryFn (dyadicExponent packet mask read ell hp hm hr he) :=
  (dyadicEnvelope_binary packet mask read ell hp hm hr he).add (BinaryFn.const 1)

theorem rawMassExponent_lt_dyadicExponent (c : List Bool)
    (i : Fin (TubeParameter.spatialCount (pairFst (packet c)))) :
    rawMassExponent packet mask read ell hp hm hr he (pair c (BinaryNatCode.encode i.val)) <
      dyadicExponent packet mask read ell hp hm hr he c := by
  have h := (Classical.choose_spec ((rawMassExponent_binary packet mask read ell hp hm hr he).finiteEnvelope
    (TubeParameter.spatialCount_unary.comp (mem_FP_comp hp pairFst_mem_FP)))).2 c i.val i.isLt
  exact Nat.lt_succ_of_le h

noncomputable def dyadicDenominator (c : List Bool) : ℤ :=
  (2 ^ dyadicExponent packet mask read ell hp hm hr he c : ℕ)

noncomputable def dyadicLevel (c : List Bool) : ℝ :=
  InfinitesimalSign.dyadic (dyadicExponent packet mask read ell hp hm hr he c)

noncomputable def dyadicFamily : List Bool → Polynomial ℤ :=
  family packet mask ell (fun _ => 1) (dyadicDenominator packet mask read ell hp hm hr he)

theorem dyadicFamily_ne_zero (c : List Bool)
    (i : Fin (TubeParameter.spatialCount (pairFst (packet c)))) :
    dyadicFamily packet mask read ell hp hm hr he (pair c (BinaryNatCode.encode i.val)) ≠ 0 := by
  let q := pair c (BinaryNatCode.encode i.val)
  let T := indexedData packet mask read ell hp hm hr he
  let E := dyadicExponent packet mask read ell hp hm hr he c
  have hE : rawMassExponent packet mask read ell hp hm hr he q < E :=
    rawMassExponent_lt_dyadicExponent packet mask read ell hp hm hr he c i
  have hthreshold : Nat.fromBitsLE (TubeDeformation.specializationExponent (pairFst ∘ indexedPacket packet)
      T.direction T.bounds.degree T.bounds.bits q) ≤ E := by
    rw [TubeDeformation.specializationExponent_value]
    exact Nat.succ_le_of_lt hE
  have hsmall : InfinitesimalSign.dyadic E ≤ InfinitesimalSign.dyadic
      (Nat.fromBitsLE (TubeDeformation.specializationExponent (pairFst ∘ indexedPacket packet)
        T.direction T.bounds.degree T.bounds.bits q)) := by
    unfold InfinitesimalSign.dyadic
    exact inv_le_inv₀ (by positivity) (by positivity) |>.mpr
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hthreshold)
  have hn := TubeDeformation.projectionPolynomial_ne_zero_of_small
    (pairFst ∘ indexedPacket packet) (mask ∘ pairFst) T.direction
    (fun c => numerator (indexedPacket packet c)) (fun c => denominator (indexedPacket packet c))
    (selectedDirection ell) T.bounds T.direction_eq q (InfinitesimalSign.dyadic E)
    (InfinitesimalSign.dyadic_pos E) hsmall
  have hb : ((2 ^ E : ℕ) : ℝ) ≠ 0 := by positivity
  have hα : (1 : ℝ) / ((2 ^ E : ℕ) : ℝ) = InfinitesimalSign.dyadic E := by
    simp [InfinitesimalSign.dyadic]
  have hraw : ((annihilatorBivariate (indexedPacket packet q) (mask (pairFst q))
      (selectedDirection ell q)).map (Polynomial.eval₂RingHom (Int.castRingHom ℝ)
        ((1 : ℝ) / (((2 ^ E : ℕ) : ℤ) : ℝ)))) ≠ 0 := by
    rw [Int.cast_natCast, hα]
    unfold annihilatorBivariate TubeDeformation.projectionPolynomial at *
    exact hn
  have hs := specialize_ne_zero (K := ℝ) (annihilatorInnerDegree (indexedPacket packet q))
    1 ((2 ^ E : ℕ) : ℤ) (annihilatorBivariate (indexedPacket packet q) (mask (pairFst q))
      (selectedDirection ell q)) (annihilatorBivariate_inner_degree _ _ _)
    (by simpa only [Int.cast_natCast] using hb) (by simpa only [Int.cast_one] using hraw)
  simpa only [dyadicFamily, family, integerAnnihilator, dyadicDenominator, E, q, indexedPacket, pairFst_pair] using hs

end LeanCanny.ETR.TubeCoordinateAnnihilator

namespace LeanCanny.ETR.TubeCoordinateAnnihilator
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra Polynomial TubeLevelPacket
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree
attribute [local irreducible] Macaulay.matrix Matrix.det
set_option maxHeartbeats 100000

variable (packet mask read : List Bool → List Bool) (ell : List Bool → ℕ → ℤ)
variable (hp : packet ∈ FP) (hm : mask ∈ FP) (hr : read ∈ FP)
variable (he : ∀ c i, read (pair c (BinaryNatCode.encode i)) = (Codec.integer (ell c i)).toBits)

theorem dyadicFamily_evaluator :
    SpaceFunction (PrimitivePairBits.coefficient (dyadicFamily packet mask read ell hp hm hr he)) := by
  have hE : BinaryFn (fun c => dyadicExponent packet mask read ell hp hm hr he (pairFst (pairFst c))) :=
    (dyadicExponent_binary packet mask read ell hp hm hr he).comp
      (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  exact family_evaluator packet mask read ell (fun _ => 1)
    (dyadicDenominator packet mask read ell hp hm hr he) hp hm hr he
    (by simpa only [Polynomial.C_1] using DyadicConstantBits.oneCoefficientEvaluator)
    (DyadicConstantBits.coefficientEvaluator hE)

theorem dyadicFamily_mass (c : List Bool) :
    coefficientMass (dyadicFamily packet mask read ell hp hm hr he c) ≤
      2 ^ massExponent packet mask read ell hp hm hr he
        (dyadicExponent packet mask read ell hp hm hr he) c :=
  family_mass packet mask read ell hp hm hr he (fun _ => 1)
    (dyadicDenominator packet mask read ell hp hm hr he)
    (dyadicExponent packet mask read ell hp hm hr he)
    (fun _ => by simpa using Nat.one_le_two_pow)
    (fun _ => by simp only [dyadicDenominator, Int.natAbs_natCast]; rfl) c

theorem dyadicFamily_massExponent_binary :
    BinaryFn (massExponent packet mask read ell hp hm hr he
      (dyadicExponent packet mask read ell hp hm hr he)) :=
  massExponent_binary packet mask read ell hp hm hr he _ (dyadicExponent_binary packet mask read ell hp hm hr he)

theorem dyadicFamily_degree (c : List Bool)
    (i : Fin (TubeParameter.spatialCount (pairFst (packet c)))) :
    (dyadicFamily packet mask read ell hp hm hr he (pair c (BinaryNatCode.encode i.val))).natDegree ≤
      TubeCompiledAffineRoots.projectionBound (pairFst (packet c)) := by
  rw [dyadicFamily, family_coordinate]
  exact integerCoordinateAnnihilator_degree _ _ _ _ _ i

theorem dyadicFamily_eval_compiled_root (c : List Bool)
    (hf : FiniteCompiledFibers.{0} (packet c) (dyadicLevel packet mask read ell hp hm hr he c))
    (z : Fin (TubeParameter.spatialCount (pairFst (packet c))) → ℝ)
    (hz : ∀ j, MvPolynomial.eval z
      (TubeCharacteristicQuotient.finiteSystem pairFst (fun _ => mask c) numerator denominator
        (fun _ => ell c) (packet c) (dyadicLevel packet mask read ell hp hm hr he c) j) = 0)
    (i : Fin (TubeParameter.spatialCount (pairFst (packet c)))) :
    (dyadicFamily packet mask read ell hp hm hr he (pair c (BinaryNatCode.encode i.val))).eval₂
      (Int.castRingHom ℝ) (z i) = 0 := by
  have hα : ((1 : ℤ) : ℝ) / (dyadicDenominator packet mask read ell hp hm hr he c : ℝ) =
      dyadicLevel packet mask read ell hp hm hr he c := by
    simp [dyadicDenominator, dyadicLevel, InfinitesimalSign.dyadic]
  have hb : (dyadicDenominator packet mask read ell hp hm hr he c : ℝ) ≠ 0 := by
    simp only [dyadicDenominator, Nat.cast_pow, Nat.cast_ofNat]
    positivity
  have hf' := hf
  rw [← hα] at hf'
  have hz' := hz
  rw [← hα] at hz'
  rw [dyadicFamily, family_coordinate]
  exact integerCoordinateAnnihilator_eval_compiled_root (packet c) (mask c) (ell c) 1
    (dyadicDenominator packet mask read ell hp hm hr he c) hb hf' z hz' i

end LeanCanny.ETR.TubeCoordinateAnnihilator
