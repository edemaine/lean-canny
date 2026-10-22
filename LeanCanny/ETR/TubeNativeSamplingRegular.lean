/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeNativeSampling
public import LeanCanny.ETR.TubeCoordinateAnnihilatorRegular
public import LeanCanny.ETR.TubeRegularJacobianChart

/-! # Simple compiled samples are accepted without a global fiber promise

Persistence of one simple root covers every reprojected spatial coordinate.
The existing polynomial-space sampler therefore accepts whenever such a
sample exists, even if other components of the fiber are infinite.
-/

@[expose] public section
set_option maxHeartbeats 200000
namespace LeanCanny.ETR.TubeNativeAnnihilator.Source
open LeanCanny.Encoding LeanCanny.Algebra Geometry
open TubeEncoding TubeProjectionEncoding TubeCharacteristicQuotient TubeLevelPacket
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree
attribute [local irreducible] Macaulay.matrix Matrix.det TubeCharacteristicQuotient.regularSystem

variable (S : Source)

noncomputable def Simple (c : List Bool) (z : Fin (TubeParameter.spatialCount (S.input c)) → ℝ) : Prop :=
  (fderiv ℝ (regularSystem pairFst (fun _ => S.mask c) TubeLevelPacket.numerator TubeLevelPacket.denominator
    (fun _ => S.projection c) (S.packet c) (S.level c))
      (projectionValue (S.packet c) z, fun j => z j.succ)).IsInvertible

theorem polynomial_eval_decoded_spatial_of_regular (c : List Bool)
    (z : Fin (TubeParameter.spatialCount (S.input c)) → ℝ)
    (hz : ∀ k, MvPolynomial.eval z
      (finiteSystem pairFst (fun _ => S.mask c) TubeLevelPacket.numerator TubeLevelPacket.denominator (fun _ => S.projection c)
        (S.packet c) (S.level c) k) = 0)
    (hJac : S.Simple c z) (j : Option (TubeSource.Coordinate (S.input c))) :
    (S.polynomial (pair c (BinaryNatCode.encode (TubeHomogenization.outputEquiv (S.input c)
      (spatialVariable (S.input c) j)).val))).eval₂ (Int.castRingHom ℝ)
      (S.decoded c z (spatialVariable (S.input c) j)) = 0 := by
  let k := TubeMacaulay.coordinateEquiv (TubeIndexed.arity (S.input c)) j
  have hk : k.val < S.spatialPrefix c := k.isLt
  rw [spatialVariable_index, S.decoded_spatial]
  unfold polynomial
  have hs : S.spatial (pair c (BinaryNatCode.encode k.val)) := by
    simpa only [spatial, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits] using hk
  rw [ite_eq_left hs]
  unfold Simple level at hJac
  have h := TubeCoordinateAnnihilator.dyadicFamily_eval_compiled_root_of_regular
    S.packet S.mask S.read S.projection S.packet_FP S.mask_FP S.read_FP S.read_eq c z hz hJac k.succ
  simpa only [spatialQuery, pairFst_pair, pairSnd_pair, BinaryNat.succ_eq_bits,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, TubeCompiledAffineRoots.decodedPoint,
    Fin.val_succ, k] using h

/-- One simple compiled root gives every original root in the native layout. -/
theorem polynomial_eval_decoded_of_regular (c : List Bool)
    (z : Fin (TubeParameter.spatialCount (S.input c)) → ℝ)
    (hz : ∀ k, MvPolynomial.eval z
      (finiteSystem pairFst (fun _ => S.mask c) TubeLevelPacket.numerator TubeLevelPacket.denominator (fun _ => S.projection c)
        (S.packet c) (S.level c) k) = 0)
    (hJac : S.Simple c z) (i : TubeRegularSource.Variable (S.input c)) :
    (S.polynomial (pair c (BinaryNatCode.encode (TubeHomogenization.outputEquiv (S.input c) i).val))).eval₂
      (Int.castRingHom ℝ) (S.decoded c z i) = 0 := by
  rcases i with _ | ((i | i) | p)
  · exact S.polynomial_eval_decoded_spatial_of_regular c z hz hJac none
  · exact S.polynomial_eval_decoded_spatial_of_regular c z hz hJac (some i)
  · exact S.polynomial_eval_decoded_parameter c z (.inl i)
  · exact S.polynomial_eval_decoded_parameter c z (.inr p)

end LeanCanny.ETR.TubeNativeAnnihilator.Source

namespace LeanCanny.ETR.TubeNativeSampling
open LeanCanny.Algebra Geometry TubeNativeAnnihilator
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree
attribute [local irreducible] Macaulay.matrix Matrix.det TubeCharacteristicQuotient.regularSystem

/-- The sampler accepts every simple sample without requiring all fibers finite. -/
theorem mem_of_regular_sample (S : Source) (c : List Bool)
    (z : Fin (TubeParameter.spatialCount (S.input c)) → ℝ)
    (hz : TubeLevelPacket.CompiledSample (S.packet c) (S.mask c) (S.projection c) (S.level c) z)
    (hJac : S.Simple c z) : c ∈ language S := by
  apply (language_iff_native S c).mpr
  refine ⟨S.decoded c z, S.polynomial_eval_decoded_of_regular c z hz.1 hJac, ?_, hz.2⟩
  have he : S.decoded c z = TubeNativeSampleGeometry.extend (S.packet c) (S.level c)
      (TubeCompiledAffineRoots.decodedPoint (S.input c) z) := by
    funext i
    rcases i with _ | ((i | i) | p) <;> rfl
  rw [he]
  exact TubeNativeSampleGeometry.regular_of_compiled (S.packet c) (S.mask c) (S.projection c)
    (S.level c) z hz.1

theorem accepts_simple_samples (S : Source) (c : List Bool) :
    (∃ z, TubeLevelPacket.CompiledSample (S.packet c) (S.mask c) (S.projection c) (S.level c) z ∧ S.Simple c z) →
      c ∈ language S := fun ⟨z, hz, hJac⟩ => mem_of_regular_sample S c z hz hJac

/-- The concrete integer singularity polynomial supplies the simple-root
condition required by the sampler. -/
theorem mem_of_jacobian_ne_zero (S : Source) (c : List Bool)
    (z : Fin (TubeParameter.spatialCount (S.input c)) → ℝ)
    (hz : TubeLevelPacket.CompiledSample (S.packet c) (S.mask c) (S.projection c) (S.level c) z)
    (hdet : (TubeRegularJacobianBudget.polynomial (S.input c)
      (TubeEncoding.activeSet (TubeIndexed.arity (S.input c)) (S.mask c))).eval₂
        (Int.castRingHom ℝ) (S.decoded c z) ≠ 0) : c ∈ language S := by
  apply mem_of_regular_sample S c z hz
  apply TubeRegularJacobianChart.packet_isInvertible (S.packet c) (S.mask c) (S.projection c) (S.level c) z
  have he : S.decoded c z = TubeNativeSampleGeometry.extend (S.packet c) (S.level c)
      (TubeCompiledAffineRoots.decodedPoint (S.input c) z) := by
    funext i
    rcases i with _ | ((i | i) | p) <;> rfl
  simpa only [← he] using hdet

end LeanCanny.ETR.TubeNativeSampling
