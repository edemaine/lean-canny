/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeSparseConstraintCoefficient
public import LeanCanny.ETR.TubeLevelReaders

/-! # Native coefficient residues of the actual integer tube constraints

The dense compact source, sparse affine terms, and raw stored margin parts
are combined modulo the requested positive modulus. All children and retained
inputs are included in the native space certificate.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeConstraintCoefficient
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open TubeLevelPacket MatrixPower
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm BinaryNat.normalize integerResidue denominatorResidue

variable (packet : List Bool → List Bool) (modulus : List Bool → List Bool)

noncomputable def marginQuery (c : List Bool) : List Bool :=
  pair (pair (packet c) (BinaryNatCode.encode (alphaIndex (packet c) + 1))) (BinaryNat.normalize (modulus c))

theorem marginQuery_FP (hp : packet ∈ FP) (hm : modulus ∈ FP) : marginQuery packet modulus ∈ FP := by
  have hi := bits_mem_FP ((alphaIndex_unary.comp hp).add (UnaryFn.const 1))
  have h := mem_FP_pair (mem_FP_pair hp hi) (mem_FP_comp hm BinaryNat.normalize_mem_FP)
  exact mem_FP_of_eq h (fun _ => rfl)

theorem margin_index_lt (c : List Bool) : alphaIndex (packet c) + 1 < arity (packet c) := by
  unfold alphaIndex arity TubeParameter.parameterCount
  omega

theorem numerator_correct (c : List Bool) : integerResidue (marginQuery packet modulus c) =
    residueBits (marginNumerator (packet c) : ZMod (ModularResidueSpace.m modulus c)) := by
  have h := integerResidue_packet (packet c) (alphaIndex (packet c) + 1)
    (ModularResidueSpace.m modulus c) (margin_index_lt packet c) (by unfold ModularResidueSpace.m; omega)
  simpa only [marginQuery, BinaryNat.normalize_eq_bits, ModularResidueSpace.m,
    Nat.add_sub_cancel_right, BinaryNatCode.encode, marginNumerator] using h

theorem denominator_correct (c : List Bool) : denominatorResidue (marginQuery packet modulus c) =
    residueBits (marginDenominator (packet c) : ZMod (ModularResidueSpace.m modulus c)) := by
  have h := denominatorResidue_packet (packet c) (alphaIndex (packet c) + 1)
    (ModularResidueSpace.m modulus c) (margin_index_lt packet c) (by unfold ModularResidueSpace.m; omega)
  simpa only [marginQuery, BinaryNat.normalize_eq_bits, ModularResidueSpace.m,
    Nat.add_sub_cancel_right, BinaryNatCode.encode, marginDenominator] using h

theorem numeratorEvaluator (hp : packet ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (fun c => residueBits (marginNumerator (packet c) : ZMod (ModularResidueSpace.m modulus c))) := by
  let E := SpaceFunction.ofFP _ (mem_FP_comp (marginQuery_FP packet modulus hp hm) integerResidue_mem_FP)
  exact E.congr (funext (numerator_correct packet modulus))

theorem denominatorEvaluator (hp : packet ∈ FP) (hm : modulus ∈ FP) :
    SpaceFunction (fun c => residueBits (marginDenominator (packet c) : ZMod (ModularResidueSpace.m modulus c))) := by
  let E := SpaceFunction.ofFP _ (mem_FP_comp (marginQuery_FP packet modulus hp hm) denominatorResidue_mem_FP)
  exact E.congr (funext (denominator_correct packet modulus))

variable (W : List Bool → ℕ) (target : List Bool → List Bool)
variable (row : (c : List Bool) → PerturbedSource.Index (pairFst (packet c)))

noncomputable def expression (c : List Bool) : ZMod (ModularResidueSpace.m modulus c) :=
  (marginDenominator (packet c) : ZMod _) *
    (((zeroMarginConstraint (packet c) (row c)).coeff (TubeSampleCoefficient.exponent packet W target c) : ℤ) : ZMod _) -
    (if TubeSparseConstraintCoefficient.code packet row c < 2 then 0 else
      (marginNumerator (packet c) : ZMod _) * TubeSparseConstraintCoefficient.constantCoefficient packet W target modulus c)

theorem expression_eq (c : List Bool) : expression packet modulus W target row c =
    (((integerConstraint (packet c) (row c)).coeff (TubeSampleCoefficient.exponent packet W target c) : ℤ) :
      ZMod (ModularResidueSpace.m modulus c)) := by
  let e := TubeSampleCoefficient.exponent packet W target c
  let off : ℤ := match row c with
    | .inl _ => 0
    | .inr _ => marginNumerator (packet c) *
      (1 : MvPolynomial (Fin (TubeParameter.spatialCount (pairFst (packet c)))) ℤ).coeff e
  have hmain := congrArg (fun z : ℤ => (z : ZMod (ModularResidueSpace.m modulus c)))
    (integerConstraint_coeff (packet c) (row c) e)
  simp only [Int.cast_sub, Int.cast_mul, Int.cast_natCast] at hmain
  have ho : (if TubeSparseConstraintCoefficient.code packet row c < 2 then 0 else
      (marginNumerator (packet c) : ZMod (ModularResidueSpace.m modulus c)) *
        TubeSparseConstraintCoefficient.constantCoefficient packet W target modulus c) = (off : ZMod _) := by
    rcases hi : row c with b | ⟨j, b⟩
    · have hc : TubeSparseConstraintCoefficient.code packet row c < 2 := by
        unfold TubeSparseConstraintCoefficient.code
        rw [hi]
        cases b
        · change (0 : ℕ) < 2; omega
        · change (1 : ℕ) < 2; omega
      rw [ite_eq_left hc]
      simp only [off, hi, Int.cast_zero]
    · have hcEq : TubeSparseConstraintCoefficient.code packet row c = 2 + 2 * j.val + (if b then 1 else 0) := by
        unfold TubeSparseConstraintCoefficient.code
        rw [hi]
        exact TubeEncoding.constraintIndex_box _ j b
      have hc : ¬ TubeSparseConstraintCoefficient.code packet row c < 2 := by
        intro h
        rw [hcEq] at h
        omega
      rw [ite_eq_right hc]
      simp only [off, hi, Int.cast_mul]
      rfl
  have hh := congrArg (fun x : ZMod (ModularResidueSpace.m modulus c) =>
    (marginDenominator (packet c) : ZMod _) * ((zeroMarginConstraint (packet c) (row c)).coeff e : ZMod _) - x) ho
  dsimp +instances only [expression, off, e, TubeSampleCoefficient.A, TubeParameter.spatialCount] at hh hmain ⊢
  rcases hi : row c with b | j <;> simp only [hi] at hh hmain
  all_goals exact hh.trans hmain.symm

theorem evaluator (hp : packet ∈ FP) (hm : modulus ∈ FP) (hW : UnaryFn W) (ht : target ∈ FP)
    (hr : UnaryFn (TubeSparseConstraintCoefficient.code packet row)) :
    SpaceFunction (fun c => residueBits
      (((integerConstraint (packet c) (row c)).coeff (TubeSampleCoefficient.exponent packet W target c) : ℤ) :
        ZMod (ModularResidueSpace.m modulus c))) := by
  let D := denominatorEvaluator packet modulus hp hm
  let N := numeratorEvaluator packet modulus hp hm
  let Z := TubeSparseConstraintCoefficient.evaluator packet W target row modulus hp hW ht hr hm
  let K := TubeSparseConstraintCoefficient.constantEvaluator packet W target modulus hp hW ht hm
  let S := ModularResidueSpace.mulEvaluator modulus _ _ hm D Z
  let NK := ModularResidueSpace.mulEvaluator modulus _ _ hm N K
  have ZERO : SpaceFunction (fun c => residueBits (0 : ZMod (ModularResidueSpace.m modulus c))) := by
    have E := SpaceFunction.ofFP (fun _ : List Bool => []) (constFn_mem_FP [])
    exact E.congr (funext fun c => by simp [residueBits, BinaryNatCode.encode])
  let T := ModularResidueSpace.branchEvaluator modulus _ _
    (fun c => TubeSparseConstraintCoefficient.code packet row c < 2)
    (FPPred.lt hr (UnaryFn.const 2)) ZERO NK
  let NT := ModularResidueSpace.negEvaluator modulus _ hm T
  let E := ModularResidueSpace.addEvaluator modulus _ _ hm S NT
  refine E.congr (funext fun c => ?_)
  have he := congrArg residueBits (expression_eq packet modulus W target row c)
  dsimp +instances only [expression, ModularResidueSpace.m] at he ⊢
  by_cases h : TubeSparseConstraintCoefficient.code packet row c < 2 <;>
    simpa only [h, ite_true, ite_false, sub_eq_add_neg] using he

end LeanCanny.ETR.TubeConstraintCoefficient
