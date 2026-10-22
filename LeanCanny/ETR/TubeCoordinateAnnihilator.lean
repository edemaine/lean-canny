/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeCoordinateAnnihilatorSpecialization
public import LeanCanny.ETR.TubeCoordinateThreshold

/-! # Integer annihilators from the actual lowest tube determinant

The lowest full determinant contains the lowest characteristic quotient as a
factor, up to a sign. Consequently it covers every compiled projection value,
including singular roots. Fixed rational clearing preserves these roots and
the source-derived projection degree bound.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeLevelPacket
open LeanCanny.Encoding LeanCanny.Algebra
open Geometry TubeEncoding TubeProjectionEncoding TubeCompiledAffineRoots
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm CompactSource.term
attribute [local irreducible] Macaulay.matrix Matrix.det TubeCleared.uniformDegree

noncomputable def annihilatorBivariate (c mask : List Bool) (ell : ℕ → ℤ) : Polynomial (Polynomial ℤ) :=
  TubeDeformation.lowestCoefficient pairFst (fun _ => mask) numerator denominator (fun _ => ell) c

noncomputable def annihilatorInnerDegree (c : List Bool) : ℕ :=
  projectionBound (pairFst c) * Nat.fromBitsLE (TubeCleared.uniformDegree pairFst bounds.degree c)

theorem annihilatorBivariate_inner_degree (c mask : List Bool) (ell : ℕ → ℤ) (i : ℕ) :
    ((annihilatorBivariate c mask ell).coeff i).natDegree ≤ annihilatorInnerDegree c :=
  TubeDeformation.lowestCoefficient_inner_degree pairFst (fun _ => mask)
    numerator denominator (fun _ => ell) bounds c i

theorem annihilatorBivariate_degree (c mask : List Bool) (ell : ℕ → ℤ) :
    (annihilatorBivariate c mask ell).natDegree ≤ projectionBound (pairFst c) := by
  have h := TubeCharacteristicQuotient.characteristicLowest_projection_degree_le
    pairFst (fun _ => mask) numerator denominator (fun _ => ell) c
  rw [(TubeDeformation.characteristicPolynomial_lowest pairFst (fun _ => mask)
    numerator denominator (fun _ => ell) c).2] at h
  rw [show (-1 : Polynomial (Polynomial ℤ)) ^ Nat.fromBitsLE (TubeDeformation.lowestIndex pairFst (fun _ => mask) numerator denominator (fun _ => ell) c) =
      Polynomial.C ((-1 : Polynomial ℤ) ^ Nat.fromBitsLE (TubeDeformation.lowestIndex pairFst (fun _ => mask) numerator denominator (fun _ => ell) c)) by simp,
    Polynomial.natDegree_C_mul (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))] at h
  exact h

theorem annihilatorBivariate_eval_compiled_root (c mask : List Bool) (ell : ℕ → ℤ) (alpha : ℝ)
    (hf : FiniteCompiledFibers.{0} c alpha)
    (z : Fin (TubeParameter.spatialCount (pairFst c)) → ℝ)
    (hz : ∀ i, MvPolynomial.eval z
      (TubeCharacteristicQuotient.finiteSystem pairFst (fun _ => mask) numerator denominator
        (fun _ => ell) c alpha i) = 0) :
    (TubeDeformation.projectionPolynomial pairFst (fun _ => mask) numerator denominator
      (fun _ => ell) c alpha).eval (projectionValue c z) = 0 := by
  let φ := TubeDeformation.parameterEvaluation (alpha, projectionValue c z)
  have hq : φ (TubeCharacteristicQuotient.polynomial pairFst (fun _ => mask)
      numerator denominator (fun _ => ell) c).trailingCoeff = 0 := by
    simpa only [eliminant, TubeCharacteristicQuotient.lowestProjectionPolynomial,
      Polynomial.eval_map, φ, TubeDeformation.parameterEvaluation, Polynomial.coe_eval₂RingHom] using
      eliminant_eval_compiled_root c mask ell alpha hf z hz
  have hn : φ (TubeDeformation.characteristicPolynomial pairFst (fun _ => mask)
      numerator denominator (fun _ => ell) c).trailingCoeff = 0 := by
    rw [← (TubeCharacteristicQuotient.numerator_lowest pairFst (fun _ => mask)
      numerator denominator (fun _ => ell) c).2,
      TubeCharacteristicQuotient.polynomial_factorization, Polynomial.trailingCoeff_mul, map_mul, hq, zero_mul]
  rw [TubeDeformation.projectionPolynomial_eval]
  exact (TubeDeformation.characteristicLowest_eval_zero_iff φ pairFst (fun _ => mask)
    numerator denominator (fun _ => ell) c).mp hn

noncomputable def integerAnnihilator (c mask : List Bool) (ell : ℕ → ℤ) (a b : ℤ) : Polynomial ℤ :=
  TubeCoordinateAnnihilator.specialize (annihilatorInnerDegree c) a b (annihilatorBivariate c mask ell)

theorem integerAnnihilator_degree (c mask : List Bool) (ell : ℕ → ℤ) (a b : ℤ) :
    (integerAnnihilator c mask ell a b).natDegree ≤ projectionBound (pairFst c) :=
  (TubeCoordinateAnnihilator.specialize_degree_le _ _ _ _).trans (annihilatorBivariate_degree c mask ell)

theorem integerAnnihilator_ne_zero (c mask : List Bool) (ell : ℕ → ℤ) (a b : ℤ)
    (hb : (b : ℝ) ≠ 0) (hp : 0 < (a : ℝ) / (b : ℝ))
    (hs : (a : ℝ) / (b : ℝ) ≤ eliminantThreshold c ell) :
    integerAnnihilator c mask ell a b ≠ 0 := by
  apply TubeCoordinateAnnihilator.specialize_ne_zero (K := ℝ) _ _ _ _
    (annihilatorBivariate_inner_degree c mask ell) hb
  exact TubeDeformation.projectionPolynomial_ne_zero_of_small pairFst (fun _ => mask)
    (projectionRead ell) numerator denominator (fun _ => ell) bounds
    (fun c i _ => projectionRead_correct ell c i) c _ hp hs

theorem integerAnnihilator_eval_compiled_root (c mask : List Bool) (ell : ℕ → ℤ) (a b : ℤ)
    (hb : (b : ℝ) ≠ 0) (hf : FiniteCompiledFibers.{0} c ((a : ℝ) / (b : ℝ)))
    (z : Fin (TubeParameter.spatialCount (pairFst c)) → ℝ)
    (hz : ∀ i, MvPolynomial.eval z
      (TubeCharacteristicQuotient.finiteSystem pairFst (fun _ => mask) numerator denominator
        (fun _ => ell) c ((a : ℝ) / (b : ℝ)) i) = 0) :
    (integerAnnihilator c mask ell a b).eval₂ (Int.castRingHom ℝ) (projectionValue c z) = 0 :=
  TubeCoordinateAnnihilator.specialize_eval_eq_zero _ _ _ _
    (annihilatorBivariate_inner_degree c mask ell) hb _
    (annihilatorBivariate_eval_compiled_root c mask ell _ hf z hz)

end LeanCanny.ETR.TubeLevelPacket

namespace LeanCanny.ETR.TubeLevelPacket
open LeanCanny.Encoding LeanCanny.Algebra
open Geometry TubeEncoding TubeProjectionEncoding TubeCompiledAffineRoots
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm CompactSource.term
attribute [local irreducible] Macaulay.matrix Matrix.det TubeCleared.uniformDegree

/-- Coordinate zero is the original projection; the tail includes the reciprocal. -/
noncomputable def integerCoordinateAnnihilator (c mask : List Bool) (ell : ℕ → ℤ) (a b : ℤ) :
    Fin (TubeParameter.spatialCount (pairFst c)) → Polynomial ℤ :=
  Fin.cons (integerAnnihilator c mask ell a b)
    (fun j => integerAnnihilator c mask (coordinateDirection j.val) a b)

theorem integerCoordinateAnnihilator_degree (c mask : List Bool) (ell : ℕ → ℤ) (a b : ℤ)
    (i : Fin (TubeParameter.spatialCount (pairFst c))) :
    (integerCoordinateAnnihilator c mask ell a b i).natDegree ≤ projectionBound (pairFst c) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact integerAnnihilator_degree c mask ell a b
  · exact integerAnnihilator_degree c mask (coordinateDirection j.val) a b

theorem integerCoordinateAnnihilator_ne_zero (c mask : List Bool) (ell : ℕ → ℤ) (a b : ℤ)
    (hb : (b : ℝ) ≠ 0) (hp : 0 < (a : ℝ) / (b : ℝ))
    (he : (a : ℝ) / (b : ℝ) ≤ eliminantThreshold c ell)
    (hc : (a : ℝ) / (b : ℝ) ≤ coordinateThreshold c)
    (i : Fin (TubeParameter.spatialCount (pairFst c))) :
    integerCoordinateAnnihilator c mask ell a b i ≠ 0 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact integerAnnihilator_ne_zero c mask ell a b hb hp he
  · exact integerAnnihilator_ne_zero c mask (coordinateDirection j.val) a b hb hp
      (hc.trans (coordinateThreshold_le c j))

theorem integerCoordinateAnnihilator_eval_compiled_root (c mask : List Bool) (ell : ℕ → ℤ) (a b : ℤ)
    (hb : (b : ℝ) ≠ 0) (hf : FiniteCompiledFibers.{0} c ((a : ℝ) / (b : ℝ)))
    (z : Fin (TubeParameter.spatialCount (pairFst c)) → ℝ)
    (hz : ∀ i, MvPolynomial.eval z
      (TubeCharacteristicQuotient.finiteSystem pairFst (fun _ => mask) numerator denominator
        (fun _ => ell) c ((a : ℝ) / (b : ℝ)) i) = 0)
    (i : Fin (TubeParameter.spatialCount (pairFst c))) :
    (integerCoordinateAnnihilator c mask ell a b i).eval₂ (Int.castRingHom ℝ) (z i) = 0 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact integerAnnihilator_eval_compiled_root c mask ell a b hb hf z hz
  · let z' := compiledPoint (pairFst c) (coordinateDirection j.val) (decodedPoint (pairFst c) z)
    have hd := fun i (_ : i < TubeParameter.parameterCount (pairFst c)) =>
      denominator_eval_ne_zero c i ((a : ℝ) / (b : ℝ))
    have hsp := spatial_roots_of_compiled pairFst (fun _ => mask) numerator denominator
      (fun _ => ell) c ((a : ℝ) / (b : ℝ)) hd z hz
    have hr := compiled_root_of_spatial pairFst (fun _ => mask) numerator denominator
      (fun _ => coordinateDirection j.val) c ((a : ℝ) / (b : ℝ)) hd _ hsp
    have he := integerAnnihilator_eval_compiled_root c mask (coordinateDirection j.val) a b hb hf z' hr
    change (integerAnnihilator c mask (coordinateDirection j.val) a b).eval₂
      (Int.castRingHom ℝ) (z j.succ) = 0
    simpa only [projectionValue, z', coordinate_projection] using he

end LeanCanny.ETR.TubeLevelPacket

namespace LeanCanny.ETR.TubeLevelPacket
open LeanCanny.Encoding LeanCanny.Algebra TubeCompiledAffineRoots

/-- The denominator may be implicit; only its numerical size enters this estimate. -/
theorem integerAnnihilator_mass (c mask : List Bool) (ell : ℕ → ℤ) (a b : ℤ) :
    coefficientMass (integerAnnihilator c mask ell a b) ≤
      (projectionBound (pairFst c) + 1) *
        (2 ^ Nat.fromBitsLE (TubeDeformation.specializationMassCode pairFst (projectionRead ell)
          bounds.degree bounds.bits c) * (max a.natAbs b.natAbs) ^ annihilatorInnerDegree c) := by
  apply TubeCoordinateAnnihilator.specialize_mass
    (hp := annihilatorBivariate_inner_degree c mask ell)
    (he := annihilatorBivariate_degree c mask ell)
  intro i
  exact TubeDeformation.lowestCoefficient_coefficient_mass pairFst (fun _ => mask)
    (projectionRead ell) numerator denominator (fun _ => ell) bounds
    (fun c i _ => projectionRead_correct ell c i) c i

end LeanCanny.ETR.TubeLevelPacket
