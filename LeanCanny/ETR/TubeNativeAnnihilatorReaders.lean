/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeNativeAnnihilator

/-! # Native coefficient readers for all regular tube coordinate annihilators -/

@[expose] public section

namespace LeanCanny.ETR.TubeNativeAnnihilator.Source
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra Polynomial MatrixPower
open RationalSubstitution.IntegerBits (context selectedDegree mValue coefficientResidue)
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm TubeCleared.uniformDegree
attribute [local irreducible] BinaryNat.succ BinaryNat.sub
attribute [local irreducible] Macaulay.matrix Matrix.det TubeLevelPacket.integerResidue TubeLevelPacket.denominatorResidue

variable (S : Source)

theorem input_FP : S.input ∈ FP := mem_FP_comp S.packet_FP pairFst_mem_FP

theorem spatialPrefix_unary : UnaryFn S.spatialPrefix :=
  ((TubeProjectionQuery.pointCount_unary (TubeIndexed.arity_unary.comp S.input_FP)).add (UnaryFn.const 1))

theorem parameterCount_unary : UnaryFn S.parameterCount :=
  TubeLevelPacket.arity_unary.comp S.packet_FP

theorem count_unary : UnaryFn S.count := TubeRegularFiniteSigns.arity_unary S.input S.input_FP

theorem exponent_binary : BinaryFn S.exponent :=
  TubeCoordinateAnnihilator.dyadicExponent_binary S.packet S.mask S.read S.projection
    S.packet_FP S.mask_FP S.read_FP S.read_eq

noncomputable def parameterDifferenceCode (q : List Bool) : List Bool :=
  BinaryNat.sub (pair (pairSnd q) (BinaryNatCode.encode (S.spatialPrefix (pairFst q))))

theorem parameterDifferenceCode_FP : S.parameterDifferenceCode ∈ FP :=
  mem_FP_comp (mem_FP_pair pairSnd_mem_FP (bits_mem_FP (S.spatialPrefix_unary.comp pairFst_mem_FP))) BinaryNat.sub_mem_FP

theorem parameterIndex_unary : UnaryFn S.parameterIndex := by
  have h := UnaryFn.fromBitsLE_min S.parameterDifferenceCode_FP
    ((S.parameterCount_unary.comp pairFst_mem_FP).sub (UnaryFn.const 1))
  exact h.of_eq (fun q => by
    simp only [parameterIndex, parameterDifferenceCode, BinaryNat.sub_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits])

theorem alpha_fppred : FPPred S.alpha := by
  have hj := bits_mem_FP S.parameterIndex_unary
  have ha := bits_mem_FP (TubeLevelPacket.alphaIndex_unary.comp (mem_FP_comp pairFst_mem_FP S.packet_FP))
  simpa only [Nat.fromBitsLE_bits, alpha] using BinaryNat.eq_fppred hj ha

theorem spatial_fppred : FPPred S.spatial := by
  exact (BinaryNat.lt_fppred pairSnd_mem_FP (bits_mem_FP (S.spatialPrefix_unary.comp pairFst_mem_FP))).of_iff
    (fun q => by simp only [Nat.fromBitsLE_bits, spatial])

theorem spatialQuery_FP : spatialQuery ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_comp pairSnd_mem_FP BinaryNat.succ_mem_FP)

noncomputable def packetConstantQuery (q : List Bool) : List Bool :=
  pair (pair (S.packet (pairFst (context q))) (BinaryNatCode.encode (S.parameterIndex (context q))))
    (BinaryNat.normalize (pairSnd q))

theorem packetConstantQuery_FP : S.packetConstantQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp (mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP pairFst_mem_FP) S.packet_FP)
    (bits_mem_FP (S.parameterIndex_unary.comp RationalSubstitution.IntegerBits.context_mem_FP)))
    (mem_FP_comp pairSnd_mem_FP BinaryNat.normalize_mem_FP)

noncomputable def packetIntegerValue (q : List Bool) : List Bool :=
  if Nat.fromBitsLE (selectedDegree q) = 0 then TubeLevelPacket.integerResidue (S.packetConstantQuery q) else []
noncomputable def packetDenominatorValue (q : List Bool) : List Bool :=
  if Nat.fromBitsLE (selectedDegree q) = 0 then TubeLevelPacket.denominatorResidue (S.packetConstantQuery q) else []

theorem packetIntegerValue_FP : S.packetIntegerValue ∈ FP :=
  DyadicConstantBits.degreeZero_pred.ite_mem_FP
    (mem_FP_comp S.packetConstantQuery_FP TubeLevelPacket.integerResidue_mem_FP) (constFn_mem_FP [])
theorem packetDenominatorValue_FP : S.packetDenominatorValue ∈ FP :=
  DyadicConstantBits.degreeZero_pred.ite_mem_FP
    (mem_FP_comp S.packetConstantQuery_FP TubeLevelPacket.denominatorResidue_mem_FP) (constFn_mem_FP [])

theorem packetConstantQuery_eq (q : List Bool) :
    S.packetConstantQuery q = pair (pair (S.packet (pairFst (context q)))
      (BinaryNatCode.encode (S.parameterIndex (context q)))) (BinaryNatCode.encode (mValue q - 1)) := by
  simp only [packetConstantQuery, BinaryNat.normalize_eq_bits, mValue, Nat.add_sub_cancel, BinaryNatCode.encode]

theorem packetIntegerValue_eq (q : List Bool) :
    S.packetIntegerValue q = PrimitivePairBits.coefficient
      (fun c => C (TubeLevelPacket.integer (S.packet (pairFst c)) (S.parameterIndex c))) q := by
  have hm : 0 < mValue q := by unfold mValue; omega
  have hj := S.parameterIndex_lt (context q)
  have hr := TubeLevelPacket.integerResidue_packet (S.packet (pairFst (context q)))
    (S.parameterIndex (context q)) (mValue q) hj hm
  rw [packetIntegerValue]
  simp only [PrimitivePairBits.coefficient, Polynomial.coeff_C]
  split_ifs with hk
  · rw [packetConstantQuery_eq]
    exact hr
  · rfl

theorem packetDenominatorValue_eq (q : List Bool) :
    S.packetDenominatorValue q = PrimitivePairBits.coefficient
      (fun c => C (TubeLevelPacket.denominatorNat (S.packet (pairFst c)) (S.parameterIndex c) : ℤ)) q := by
  have hm : 0 < mValue q := by unfold mValue; omega
  have hj := S.parameterIndex_lt (context q)
  have hr := TubeLevelPacket.denominatorResidue_packet (S.packet (pairFst (context q)))
    (S.parameterIndex (context q)) (mValue q) hj hm
  rw [packetDenominatorValue]
  simp only [PrimitivePairBits.coefficient, Polynomial.coeff_C]
  split_ifs with hk
  · rw [packetConstantQuery_eq]
    simpa only [coefficientResidue, Int.cast_natCast] using hr
  · rfl

theorem packetIntegerCoefficientEvaluator : SpaceFunction (PrimitivePairBits.coefficient
    (fun c => C (TubeLevelPacket.integer (S.packet (pairFst c)) (S.parameterIndex c)))) :=
  (SpaceFunction.ofFP _ S.packetIntegerValue_FP).congr (funext S.packetIntegerValue_eq)

theorem packetDenominatorCoefficientEvaluator : SpaceFunction (PrimitivePairBits.coefficient
    (fun c => C (TubeLevelPacket.denominatorNat (S.packet (pairFst c)) (S.parameterIndex c) : ℤ))) :=
  (SpaceFunction.ofFP _ S.packetDenominatorValue_FP).congr (funext S.packetDenominatorValue_eq)

theorem numeratorCoefficientEvaluator : SpaceFunction (PrimitivePairBits.coefficient (fun c => C (S.numerator c))) := by
  have E := SpaceFunction.branch (fun q => decide (S.alpha (context q)))
    (S.alpha_fppred.comp RationalSubstitution.IntegerBits.context_mem_FP).flag_mem_FP
    DyadicConstantBits.oneCoefficientEvaluator S.packetIntegerCoefficientEvaluator
  refine E.congr (funext fun q => ?_)
  simp only [decide_eq_true_eq]
  by_cases h : S.alpha (context q)
  · rw [ite_eq_left h]
    unfold PrimitivePairBits.coefficient
    dsimp only
    rw [Source.numerator, ite_eq_left h, Polynomial.C_1]
  · rw [ite_eq_right h]
    unfold PrimitivePairBits.coefficient
    dsimp only
    rw [Source.numerator, ite_eq_right h]

theorem denominatorCoefficientEvaluator : SpaceFunction (PrimitivePairBits.coefficient (fun c => C (S.denominator c))) := by
  have hE : BinaryFn (fun c => S.exponent (pairFst c)) := S.exponent_binary.comp pairFst_mem_FP
  have E := SpaceFunction.branch (fun q => decide (S.alpha (context q)))
    (S.alpha_fppred.comp RationalSubstitution.IntegerBits.context_mem_FP).flag_mem_FP
    (DyadicConstantBits.coefficientEvaluator hE) S.packetDenominatorCoefficientEvaluator
  refine E.congr (funext fun q => ?_)
  simp only [decide_eq_true_eq]
  by_cases h : S.alpha (context q)
  · rw [ite_eq_left h]
    unfold PrimitivePairBits.coefficient
    dsimp only
    rw [Source.denominator, ite_eq_left h]
    rfl
  · rw [ite_eq_right h]
    unfold PrimitivePairBits.coefficient
    dsimp only
    rw [Source.denominator, ite_eq_right h]

noncomputable def spatialCoefficientQuery (q : List Bool) : List Bool :=
  pair (pair (spatialQuery (context q)) (selectedDegree q)) (pairSnd q)

theorem spatialCoefficientQuery_FP : spatialCoefficientQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp RationalSubstitution.IntegerBits.context_mem_FP spatialQuery_FP)
    RationalSubstitution.IntegerBits.selectedDegree_mem_FP) pairSnd_mem_FP

theorem coefficientEvaluator : SpaceFunction (PrimitivePairBits.coefficient S.polynomial) := by
  have ED := (TubeCoordinateAnnihilator.dyadicFamily_evaluator S.packet S.mask S.read S.projection
    S.packet_FP S.mask_FP S.read_FP S.read_eq).precompose spatialCoefficientQuery spatialCoefficientQuery_FP
  have EP := TubeNativeAnnihilatorPins.coefficientEvaluator S.numerator S.denominator
    S.numeratorCoefficientEvaluator S.denominatorCoefficientEvaluator
  have E := SpaceFunction.branch (fun q => decide (S.spatial (context q)))
    (S.spatial_fppred.comp RationalSubstitution.IntegerBits.context_mem_FP).flag_mem_FP ED EP
  refine E.congr (funext fun q => ?_)
  simp only [decide_eq_true_eq, Function.comp_apply]
  by_cases h : S.spatial (context q)
  · rw [ite_eq_left h]
    unfold PrimitivePairBits.coefficient
    rw [polynomial, ite_eq_left h]
    simp only [spatialCoefficientQuery, context, selectedDegree, mValue, pairFst_pair, pairSnd_pair]
  · rw [ite_eq_right h]
    unfold PrimitivePairBits.coefficient
    rw [polynomial, ite_eq_right h]

end LeanCanny.ETR.TubeNativeAnnihilator.Source
