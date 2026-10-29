/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.FlatAffinePowerSampleInput

/-! # Native complete-root sampling from original affine records

The cone certificate affects semantic proofs only. Row and annihilator
queries charge the original source, direction, and level readers.
-/

@[expose] public section
namespace LeanCanny.Encoding.FlatAffinePowerSampleInput
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open FlatAffineFullSourceTower (Inputs)
open FlatAffineFullSourcePositive (count)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
attribute [local irreducible] FlatAffinePowerPositive.system FlatAffinePowerPositive.degree

noncomputable def frame (F : Inputs) := FlatAffineFullSourceContext.comp F SquareSampleInput.source

noncomputable def row (F : Inputs) (hcone : FlatAffinePowerPositive.ConeCertificate F) (q : List Bool) :
    Fin (count (frame F) q) :=
  SquareSampleInput.selected (input F hcone) (SquareSampleInput.source q) (SquareSampleInput.indexWord q)

theorem row_unary {F : Inputs} (h : F.Access) (hcone : FlatAffinePowerPositive.ConeCertificate F) :
    UnaryFn (fun q => (row F hcone q).val) :=
  UnaryFn.fromBitsLE_min SquareSampleInput.indexWord_FP
    (((FlatAffineFullSourcePositive.count_unary h).comp SquareSampleInput.source_FP).sub (UnaryFn.const 1))

theorem row_evaluator {F : Inputs} (h : F.Access) (hcone : FlatAffinePowerPositive.ConeCertificate F) :
    SpaceFunction (SquareSampleInput.rowCoefficient (input F hcone)) := by
  have E := FlatAffinePowerPositive.evaluator (FlatAffineFullSourceContext.access h SquareSampleInput.source_FP)
    (row F hcone) (row_unary h hcone) (UnaryFn.length SquareSampleInput.widthWord_FP)
    SquareSampleInput.rankWord_FP SquareSampleInput.modulusWord_FP
  refine E.congr (funext fun q => ?_)
  change residueBits (((FlatAffinePowerPositive.system (frame F) q (row F hcone q)).coeff
    (FixedWidthPolynomial.nativeExponent (Equiv.refl _) (SquareSampleInput.widthWord q).length
      (Nat.fromBitsLE (SquareSampleInput.rankWord q))) : ℤ) : ZMod (Nat.fromBitsLE (SquareSampleInput.modulusWord q) + 1)) = _
  exact congrArg (fun p : MvPolynomial (Fin (count F (SquareSampleInput.source q))) ℤ =>
    residueBits ((p.coeff (FixedWidthPolynomial.nativeExponent (Equiv.refl _) (SquareSampleInput.widthWord q).length
      (Nat.fromBitsLE (SquareSampleInput.rankWord q))) : ℤ) : ZMod (Nat.fromBitsLE (SquareSampleInput.modulusWord q) + 1)))
    (FlatAffinePowerPositive.system_comp F SquareSampleInput.source q (row F hcone q))

private lemma coefficient_pair (p : List Bool → Polynomial ℤ) (c r m : List Bool) :
    PrimitivePairBits.coefficient p (pair (pair c r) m) = residueBits
      ((p c).coeff (Nat.fromBitsLE r) : ZMod (Nat.fromBitsLE m + 1)) := by
  simp only [PrimitivePairBits.coefficient, RationalSubstitution.IntegerBits.context,
    RationalSubstitution.IntegerBits.selectedDegree, RationalSubstitution.IntegerBits.mValue,
    pairFst_pair, pairSnd_pair]
  rfl

theorem ann_evaluator {F : Inputs} (h : F.Access) (hcone : FlatAffinePowerPositive.ConeCertificate F) :
    SpaceFunction (SquareSampleInput.annCoefficient (input F hcone)) := by
  have E := FlatAffinePowerGram.annihilator_evaluator (FlatAffineFullSourceContext.access h SquareSampleInput.source_FP)
    (row F hcone) (row_unary h hcone)
  let prepare (q : List Bool) := pair (pair q (SquareSampleInput.rankWord q)) (SquareSampleInput.modulusWord q)
  have hp : prepare ∈ FP := mem_FP_pair (mem_FP_pair id_mem_FP SquareSampleInput.rankWord_FP) SquareSampleInput.modulusWord_FP
  refine (E.precompose prepare hp).congr (funext fun q => ?_)
  simp only [Function.comp_apply, prepare, coefficient_pair, FlatAffinePowerGram.annihilator_eq]
  exact congrArg (fun p : Polynomial ℤ => residueBits
    (p.coeff (Nat.fromBitsLE (SquareSampleInput.rankWord q)) : ZMod (Nat.fromBitsLE (SquareSampleInput.modulusWord q) + 1)))
    (polynomial_comp F SquareSampleInput.source q (row F hcone q))

theorem access {F : Inputs} (h : F.Access) (hcone : FlatAffinePowerPositive.ConeCertificate F) :
    (input F hcone).Access :=
  ⟨FlatAffineFullSourcePositive.count_unary h, FlatAffineFullSourceTower.degree_binary h,
    FlatAffineFullSourceTower.mass_binary h, FlatAffinePowerGram.degreeBound_binary h,
    FlatAffinePowerGram.heightBound_binary h, row_evaluator h hcone, ann_evaluator h hcone⟩

theorem count_evaluator {F : Inputs} (h : F.Access) (hcone : FlatAffinePowerPositive.ConeCertificate F) :
    SpaceFunction (fun u => BinaryNatCode.encode (SquareSampleComplete.count (input F hcone) u)) :=
  SquareSampleComplete.count_evaluator (access h hcone) (complete F hcone)

theorem language_mem_PSPACE {F : Inputs} (h : F.Access) (hcone : FlatAffinePowerPositive.ConeCertificate F) :
    {u | ∃ z : Fin (count F u) → ℝ, ∀ i, (FlatAffinePowerPositive.system F u i).eval₂ (Int.castRingHom ℝ) z = 0} ∈ PSPACE :=
  SquareSampleComplete.language_mem_PSPACE (access h hcone) (complete F hcone)

end LeanCanny.Encoding.FlatAffinePowerSampleInput
