/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeNativeAnnihilatorReaders

/-! # Binary degree and mass bounds for the full native coordinate family -/

@[expose] public section

namespace LeanCanny.ETR.TubeNativeAnnihilator.Source
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra Polynomial
open TubeCompiledAffineRoots
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree
attribute [local irreducible] Macaulay.matrix Matrix.det

variable (S : Source)

noncomputable def degreeBound (c : List Bool) : ℕ := projectionBound (S.input c) + 1

theorem degreeBound_binary : BinaryFn S.degreeBound := by
  have h := BinaryFn.fromBits (MacaulayBits.dimensionCode_mem_FP (TubeCleared.layout_polyTime S.input_FP))
  simp only [MacaulayBits.dimensionCode, FixedWidthPolynomial.countCode_code, MacaulayBits.fromBits_encode] at h
  exact h.add (BinaryFn.const 1)

theorem polynomial_degree (q : List Bool) : (S.polynomial q).natDegree ≤ S.degreeBound (pairFst q) := by
  unfold polynomial
  split_ifs with hs
  · let i : Fin (TubeParameter.spatialCount (S.input (pairFst q))) :=
      ⟨Nat.fromBitsLE (pairSnd q) + 1, by
        have h := hs
        unfold spatial spatialPrefix TubeParameter.spatialCount at *
        omega⟩
    have h := TubeCoordinateAnnihilator.dyadicFamily_degree S.packet S.mask S.read S.projection
      S.packet_FP S.mask_FP S.read_FP S.read_eq (pairFst q) i
    have h' : (TubeCoordinateAnnihilator.dyadicFamily S.packet S.mask S.read S.projection
        S.packet_FP S.mask_FP S.read_FP S.read_eq (spatialQuery q)).natDegree ≤ projectionBound (S.input (pairFst q)) := by
      simpa only [spatialQuery, BinaryNat.succ_eq_bits, BinaryNatCode.encode, i] using h
    exact h'.trans (Nat.le_succ _)
  · exact (TubeNativeAnnihilatorPins.degree _ _).trans (Nat.le_add_left _ _)

noncomputable def spatialMassExponent : List Bool → ℕ :=
  TubeCoordinateAnnihilator.massExponent S.packet S.mask S.read S.projection S.packet_FP S.mask_FP S.read_FP S.read_eq S.exponent

theorem spatialMassExponent_binary : BinaryFn S.spatialMassExponent :=
  TubeCoordinateAnnihilator.massExponent_binary S.packet S.mask S.read S.projection
    S.packet_FP S.mask_FP S.read_FP S.read_eq S.exponent S.exponent_binary

noncomputable def massExponent (q : List Bool) : ℕ :=
  S.spatialMassExponent (spatialQuery q) + S.exponent (pairFst q) + TubeLevelPacket.width (S.packet (pairFst q)) + 2

theorem massExponent_binary : BinaryFn S.massExponent := by
  have hs : BinaryFn (fun q => S.spatialMassExponent (spatialQuery q)) :=
    S.spatialMassExponent_binary.comp spatialQuery_FP
  have he : BinaryFn (fun q => S.exponent (pairFst q)) := S.exponent_binary.comp pairFst_mem_FP
  have hw : BinaryFn (fun q => TubeLevelPacket.width (S.packet (pairFst q))) :=
    BinaryFn.of_bits (bits_mem_FP (TubeLevelPacket.width_unary.comp (mem_FP_comp pairFst_mem_FP S.packet_FP)))
  exact ((hs.add he).add hw).add (BinaryFn.const 2)

theorem numerator_bound (q : List Bool) :
    (S.numerator q).natAbs ≤ 2 ^ (S.exponent (pairFst q) + TubeLevelPacket.width (S.packet (pairFst q)) + 1) := by
  unfold numerator
  split_ifs
  · simpa only [Int.natAbs_one] using Nat.one_le_two_pow
  · exact (TubeLevelPacket.integer_bound _ _).trans
      (Nat.pow_le_pow_right (by decide) (by omega))

theorem denominator_bound (q : List Bool) :
    (S.denominator q).natAbs ≤ 2 ^ (S.exponent (pairFst q) + TubeLevelPacket.width (S.packet (pairFst q)) + 1) := by
  unfold denominator
  split_ifs
  · change (2 ^ S.exponent (pairFst q) : ℕ) ≤ _
    exact Nat.pow_le_pow_right (by decide) (by omega)
  · rw [Int.natAbs_natCast]
    exact (TubeLevelPacket.denominatorNat_bound _ _).trans
      (Nat.pow_le_pow_right (by decide) (by omega))

theorem polynomial_mass (q : List Bool) : coefficientMass (S.polynomial q) ≤ 2 ^ S.massExponent q := by
  unfold polynomial
  split_ifs
  · have h := TubeCoordinateAnnihilator.dyadicFamily_mass S.packet S.mask S.read S.projection
      S.packet_FP S.mask_FP S.read_FP S.read_eq (spatialQuery q)
    change coefficientMass _ ≤ 2 ^ S.spatialMassExponent (spatialQuery q) at h
    apply h.trans
    exact Nat.pow_le_pow_right (by decide) (by unfold massExponent; omega)
  · apply (TubeNativeAnnihilatorPins.mass _ _).trans
    calc
      _ ≤ 2 ^ (S.exponent (pairFst q) + TubeLevelPacket.width (S.packet (pairFst q)) + 1) +
          2 ^ (S.exponent (pairFst q) + TubeLevelPacket.width (S.packet (pairFst q)) + 1) :=
        Nat.add_le_add (S.denominator_bound q) (S.numerator_bound q)
      _ = 2 ^ (S.exponent (pairFst q) + TubeLevelPacket.width (S.packet (pairFst q)) + 2) := by
        have h := pow_succ (2 : ℕ) (S.exponent (pairFst q) + TubeLevelPacket.width (S.packet (pairFst q)) + 1)
        rw [Nat.mul_two] at h
        exact h.symm
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by unfold massExponent; omega)

end LeanCanny.ETR.TubeNativeAnnihilator.Source
