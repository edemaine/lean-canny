/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeNativeAnnihilatorBudget

/-! # Compiled-root coverage and exact recovery of pinned tube parameters -/

@[expose] public section

namespace LeanCanny.ETR.TubeNativeAnnihilator.Source
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra Polynomial
open Geometry TubeEncoding TubeProjectionEncoding
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree
attribute [local irreducible] Macaulay.matrix Matrix.det

variable (S : Source)

noncomputable def decoded (c : List Bool)
    (z : Fin (TubeParameter.spatialCount (S.input c)) → ℝ) : TubeRegularSource.Variable (S.input c) → ℝ
  | none => TubeCompiledAffineRoots.decodedPoint (S.input c) z none
  | some (.inl (.inl i)) => TubeCompiledAffineRoots.decodedPoint (S.input c) z (some i)
  | some (.inl (.inr i)) => TubeLevelPacket.parameters (S.packet c) (S.level c) (MvPolynomial.X (.inl i))
  | some (.inr p) => TubeLevelPacket.parameters (S.packet c) (S.level c) (MvPolynomial.X (.inr p))

theorem decoded_spatial (c : List Bool)
    (z : Fin (TubeParameter.spatialCount (S.input c)) → ℝ) (j : Option (TubeSource.Coordinate (S.input c))) :
    S.decoded c z (spatialVariable (S.input c) j) = TubeCompiledAffineRoots.decodedPoint (S.input c) z j := by
  cases j <;> rfl

theorem decoded_parameter (c : List Bool)
    (z : Fin (TubeParameter.spatialCount (S.input c)) → ℝ) (j : TubeParameter.Parameter (S.input c)) :
    S.decoded c z (parameterVariable (S.input c) j) =
      TubeLevelPacket.parameters (S.packet c) (S.level c) (MvPolynomial.X j) := by
  cases j <;> rfl

theorem polynomial_parameter (c : List Bool) (j : TubeParameter.Parameter (S.input c)) :
    S.polynomial (pair c (BinaryNatCode.encode (TubeHomogenization.outputEquiv (S.input c)
      (parameterVariable (S.input c) j)).val)) =
      TubeNativeAnnihilatorPins.polynomial
        (S.numerator (pair c (BinaryNatCode.encode
          (S.spatialPrefix c + (TubeParameter.parameterEquiv (S.input c) j).val))))
        (S.denominator (pair c (BinaryNatCode.encode
          (S.spatialPrefix c + (TubeParameter.parameterEquiv (S.input c) j).val)))) := by
  rw [parameterVariable_index]
  unfold polynomial
  rw [ite_eq_right]
  · rfl
  · simp only [spatial, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    unfold spatialPrefix
    omega

/-- Every parameter in a native root tuple is exactly the prescribed packet/dyadic value. -/
theorem parameters_pinned (c : List Bool) (w : TubeRegularSource.Variable (S.input c) → ℝ)
    (hw : ∀ i, (S.polynomial (pair c (BinaryNatCode.encode
      (TubeHomogenization.outputEquiv (S.input c) i).val))).eval₂ (Int.castRingHom ℝ) (w i) = 0)
    (j : TubeParameter.Parameter (S.input c)) :
    w (parameterVariable (S.input c) j) =
      TubeLevelPacket.parameters (S.packet c) (S.level c) (MvPolynomial.X j) := by
  have h := hw (parameterVariable (S.input c) j)
  rw [S.polynomial_parameter] at h
  have hd : (S.denominator (pair c (BinaryNatCode.encode
      (S.spatialPrefix c + (TubeParameter.parameterEquiv (S.input c) j).val))) : ℝ) ≠ 0 :=
    Int.cast_ne_zero.mpr (S.denominator_ne_zero _)
  exact ((TubeNativeAnnihilatorPins.root_iff _ _ _ hd).mp h).trans (S.parameterValue c j)

theorem polynomial_eval_decoded_spatial (c : List Bool)
    (hf : TubeLevelPacket.FiniteCompiledFibers.{0} (S.packet c) (S.level c))
    (z : Fin (TubeParameter.spatialCount (S.input c)) → ℝ)
    (hz : ∀ k, MvPolynomial.eval z
      (TubeCharacteristicQuotient.finiteSystem pairFst (fun _ => S.mask c)
        TubeLevelPacket.numerator TubeLevelPacket.denominator (fun _ => S.projection c)
        (S.packet c) (S.level c) k) = 0)
    (j : Option (TubeSource.Coordinate (S.input c))) :
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
  have h := TubeCoordinateAnnihilator.dyadicFamily_eval_compiled_root S.packet S.mask S.read S.projection
    S.packet_FP S.mask_FP S.read_FP S.read_eq c hf z hz k.succ
  simpa only [spatialQuery, pairFst_pair, pairSnd_pair, BinaryNat.succ_eq_bits,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, TubeCompiledAffineRoots.decodedPoint,
    Fin.val_succ, k] using h

theorem polynomial_eval_decoded_parameter (c : List Bool)
    (z : Fin (TubeParameter.spatialCount (S.input c)) → ℝ) (j : TubeParameter.Parameter (S.input c)) :
    (S.polynomial (pair c (BinaryNatCode.encode (TubeHomogenization.outputEquiv (S.input c)
      (parameterVariable (S.input c) j)).val))).eval₂ (Int.castRingHom ℝ)
      (S.decoded c z (parameterVariable (S.input c) j)) = 0 := by
  rw [S.polynomial_parameter, S.decoded_parameter]
  exact (TubeNativeAnnihilatorPins.root_iff _ _ _ (Int.cast_ne_zero.mpr (S.denominator_ne_zero _))).mpr
    (S.parameterValue c j).symm

/-- Every compiled root gives an annihilated tuple in the native regular-variable layout. -/
theorem polynomial_eval_decoded (c : List Bool)
    (hf : TubeLevelPacket.FiniteCompiledFibers.{0} (S.packet c) (S.level c))
    (z : Fin (TubeParameter.spatialCount (S.input c)) → ℝ)
    (hz : ∀ k, MvPolynomial.eval z
      (TubeCharacteristicQuotient.finiteSystem pairFst (fun _ => S.mask c)
        TubeLevelPacket.numerator TubeLevelPacket.denominator (fun _ => S.projection c)
        (S.packet c) (S.level c) k) = 0)
    (i : TubeRegularSource.Variable (S.input c)) :
    (S.polynomial (pair c (BinaryNatCode.encode (TubeHomogenization.outputEquiv (S.input c) i).val))).eval₂
      (Int.castRingHom ℝ) (S.decoded c z i) = 0 := by
  rcases i with _ | ((i | i) | p)
  · exact S.polynomial_eval_decoded_spatial c hf z hz none
  · exact S.polynomial_eval_decoded_spatial c hf z hz (some i)
  · exact S.polynomial_eval_decoded_parameter c z (.inl i)
  · exact S.polynomial_eval_decoded_parameter c z (.inr p)

end LeanCanny.ETR.TubeNativeAnnihilator.Source
