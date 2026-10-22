/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeNativeAnnihilatorPins
public import LeanCanny.ETR.TubeRegularFiniteSigns

/-! # Original annihilators for every variable of the regular tube system

Reciprocal and point variables use the dyadic spatial annihilators. Direction,
epsilon, and delta variables are pinned to the packet's rational constants;
alpha is pinned to the same implicit dyadic level as the spatial family.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeNativeAnnihilator
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra Polynomial
open Geometry TubeEncoding TubeProjectionEncoding
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree
attribute [local irreducible] Macaulay.matrix Matrix.det

structure Source where
  packet : List Bool → List Bool
  mask : List Bool → List Bool
  read : List Bool → List Bool
  projection : List Bool → ℕ → ℤ
  packet_FP : packet ∈ FP
  mask_FP : mask ∈ FP
  read_FP : read ∈ FP
  read_eq : ∀ c i, read (pair c (BinaryNatCode.encode i)) = (Codec.integer (projection c i)).toBits

namespace Source
variable (S : Source)

noncomputable abbrev input (c : List Bool) : List Bool := pairFst (S.packet c)
noncomputable def spatialPrefix (c : List Bool) : ℕ := pointCount (TubeIndexed.arity (S.input c)) + 1
noncomputable def parameterCount (c : List Bool) : ℕ := TubeLevelPacket.arity (S.packet c)
noncomputable def count (c : List Bool) : ℕ := TubeRegularFiniteSigns.arity S.input c
noncomputable def exponent : List Bool → ℕ :=
  TubeCoordinateAnnihilator.dyadicExponent S.packet S.mask S.read S.projection S.packet_FP S.mask_FP S.read_FP S.read_eq
noncomputable def level : List Bool → ℝ :=
  TubeCoordinateAnnihilator.dyadicLevel S.packet S.mask S.read S.projection S.packet_FP S.mask_FP S.read_FP S.read_eq
noncomputable def levelDenominator : List Bool → ℤ :=
  TubeCoordinateAnnihilator.dyadicDenominator S.packet S.mask S.read S.projection S.packet_FP S.mask_FP S.read_FP S.read_eq

noncomputable def parameterIndex (q : List Bool) : ℕ :=
  min (Nat.fromBitsLE (pairSnd q) - S.spatialPrefix (pairFst q)) (S.parameterCount (pairFst q) - 1)

noncomputable def alpha (q : List Bool) : Prop :=
  S.parameterIndex q = TubeLevelPacket.alphaIndex (S.packet (pairFst q))
noncomputable instance (q : List Bool) : Decidable (S.alpha q) := inferInstanceAs (Decidable (_ = _))

noncomputable def numerator (q : List Bool) : ℤ :=
  if S.alpha q then 1 else TubeLevelPacket.integer (S.packet (pairFst q)) (S.parameterIndex q)
noncomputable def denominator (q : List Bool) : ℤ :=
  if S.alpha q then S.levelDenominator (pairFst q)
  else (TubeLevelPacket.denominatorNat (S.packet (pairFst q)) (S.parameterIndex q) : ℤ)

noncomputable def spatial (q : List Bool) : Prop := Nat.fromBitsLE (pairSnd q) < S.spatialPrefix (pairFst q)
noncomputable instance (q : List Bool) : Decidable (S.spatial q) := inferInstanceAs (Decidable (_ < _))

def spatialQuery (q : List Bool) : List Bool := pair (pairFst q) (BinaryNat.succ (pairSnd q))

noncomputable def polynomial (q : List Bool) : Polynomial ℤ :=
  if S.spatial q then TubeCoordinateAnnihilator.dyadicFamily S.packet S.mask S.read S.projection
    S.packet_FP S.mask_FP S.read_FP S.read_eq (spatialQuery q)
  else TubeNativeAnnihilatorPins.polynomial (S.numerator q) (S.denominator q)

noncomputable def family : SeparableBits.Family where
  polynomial := S.polynomial
  height q := (coefficientMass (S.polynomial q)).size
  coefficient_bound _q k := (coeff_natAbs_le_coefficientMass _ k).trans (Nat.lt_size_self _).le

theorem parameterIndex_lt (q : List Bool) : S.parameterIndex q < S.parameterCount (pairFst q) := by
  have hp : 0 < S.parameterCount (pairFst q) := by
    unfold parameterCount TubeLevelPacket.arity TubeParameter.parameterCount
    omega
  exact (min_le_right _ _).trans_lt (by omega)

theorem counts (c : List Bool) : S.count c = S.spatialPrefix c + S.parameterCount c := by
  dsimp only [count, spatialPrefix, parameterCount, input, TubeRegularFiniteSigns.arity, TubeLevelPacket.arity,
    TubeParameter.parameterCount, TubeIndexed.projectionDimension, TubeProjectionEncoding.dimension]
  omega

theorem levelDenominator_ne_zero (c : List Bool) : S.levelDenominator c ≠ 0 := by
  unfold levelDenominator TubeCoordinateAnnihilator.dyadicDenominator
  exact Int.natCast_ne_zero.mpr (pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0))

theorem denominator_ne_zero (q : List Bool) : S.denominator q ≠ 0 := by
  unfold denominator
  split_ifs
  · exact S.levelDenominator_ne_zero _
  · exact Int.natCast_ne_zero.mpr (Nat.succ_ne_zero _)

theorem polynomial_ne_zero (q : List Bool) : S.polynomial q ≠ 0 := by
  unfold polynomial
  split_ifs with hs
  · let i : Fin (TubeParameter.spatialCount (S.input (pairFst q))) :=
      ⟨Nat.fromBitsLE (pairSnd q) + 1, by
        have h := hs
        unfold spatial spatialPrefix TubeParameter.spatialCount at *
        omega⟩
    have h := TubeCoordinateAnnihilator.dyadicFamily_ne_zero S.packet S.mask S.read S.projection
      S.packet_FP S.mask_FP S.read_FP S.read_eq (pairFst q) i
    simpa only [spatialQuery, BinaryNat.succ_eq_bits, BinaryNatCode.encode, i] using h
  · exact TubeNativeAnnihilatorPins.ne_zero _ _ (S.denominator_ne_zero q)

/-- The alpha pin uses the implicit dyadic denominator. -/
theorem parameterValue (c : List Bool) (j : TubeParameter.Parameter (S.input c)) :
    (S.numerator (pair c (BinaryNatCode.encode (S.spatialPrefix c + (TubeParameter.parameterEquiv (S.input c) j).val))) : ℝ) /
      S.denominator (pair c (BinaryNatCode.encode (S.spatialPrefix c + (TubeParameter.parameterEquiv (S.input c) j).val))) =
      TubeLevelPacket.parameters (S.packet c) (S.level c) (MvPolynomial.X j) := by
  have hj := (TubeParameter.parameterEquiv (S.input c) j).isLt
  have hindex : S.parameterIndex (pair c (BinaryNatCode.encode
      (S.spatialPrefix c + (TubeParameter.parameterEquiv (S.input c) j).val))) =
        (TubeParameter.parameterEquiv (S.input c) j).val := by
    simp only [parameterIndex, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
      Nat.add_sub_cancel_left]
    exact min_eq_left (by simpa only [parameterCount, TubeLevelPacket.arity, input, Nat.pred_eq_sub_one] using Nat.le_pred_of_lt hj)
  let q := pair c (BinaryNatCode.encode (S.spatialPrefix c + (TubeParameter.parameterEquiv (S.input c) j).val))
  change (S.numerator q : ℝ) / S.denominator q = _
  by_cases ha : S.alpha q
  · have hi : (TubeParameter.parameterEquiv (S.input c) j).val = TubeLevelPacket.alphaIndex (S.packet c) := by
      simpa only [alpha, q, hindex, pairFst_pair] using ha
    rw [numerator, denominator, ite_eq_left ha, ite_eq_left ha]
    simp only [q, pairFst_pair]
    have hparam := TubeLevelPacket.parameters_X (S.packet c) (S.level c) j
    rw [ite_eq_left hi] at hparam
    rw [hparam]
    simp [levelDenominator, level, TubeCoordinateAnnihilator.dyadicDenominator,
      TubeCoordinateAnnihilator.dyadicLevel, InfinitesimalSign.dyadic]
  · have hi : (TubeParameter.parameterEquiv (S.input c) j).val ≠ TubeLevelPacket.alphaIndex (S.packet c) := by
      simpa only [alpha, q, hindex, pairFst_pair] using ha
    rw [numerator, denominator, ite_eq_right ha, ite_eq_right ha]
    simp only [q, pairFst_pair, hindex]
    have hparam := TubeLevelPacket.parameters_X (S.packet c) (S.level c) j
    rw [ite_eq_right hi] at hparam
    rw [hparam]
    simp [TubeLevelPacket.rationalValue]

end Source

noncomputable def spatialVariable (bits : List Bool) : Option (TubeSource.Coordinate bits) → TubeRegularSource.Variable bits
  | none => none
  | some i => some (.inl (.inl i))

noncomputable def parameterVariable (bits : List Bool) : TubeParameter.Parameter bits → TubeRegularSource.Variable bits
  | .inl i => some (.inl (.inr i))
  | .inr p => some (.inr p)

theorem spatialVariable_index (bits : List Bool) (j : Option (TubeSource.Coordinate bits)) :
    (TubeHomogenization.outputEquiv bits (spatialVariable bits j)).val =
      (TubeMacaulay.coordinateEquiv (TubeIndexed.arity bits) j).val := by
  cases j <;> rfl

theorem parameterVariable_index (bits : List Bool) (j : TubeParameter.Parameter bits) :
    (TubeHomogenization.outputEquiv bits (parameterVariable bits j)).val =
      pointCount (TubeIndexed.arity bits) + 1 + (TubeParameter.parameterEquiv bits j).val := by
  cases j with
  | inl i =>
    change pointCount (TubeIndexed.arity bits) + (pointEquiv (TubeIndexed.arity bits) i).val + 1 =
      pointCount (TubeIndexed.arity bits) + 1 + (pointEquiv (TubeIndexed.arity bits) i).val
    omega
  | inr p =>
    change pointCount (TubeIndexed.arity bits) + pointCount (TubeIndexed.arity bits) +
      (TubeEncoding.parameterEquiv p).val + 1 =
      pointCount (TubeIndexed.arity bits) + 1 +
        (pointCount (TubeIndexed.arity bits) + (TubeEncoding.parameterEquiv p).val)
    omega

end LeanCanny.ETR.TubeNativeAnnihilator
