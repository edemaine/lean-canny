/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeConstraintCoefficient

/-! # Total binary row selection for the native constraint coefficient reader

Binary row indices are capped before conversion to a finite constraint. Valid
indices retain their exact row; arbitrary inputs select the final constraint
when the decoded index is too large. Every selector and child has a native
certificate on all input words.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeConstraintCoefficient
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open TubeLevelPacket TubeEncoding MatrixPower
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm

variable (packet rowBits : List Bool → List Bool)

noncomputable def cappedRow (c : List Bool) : ℕ :=
  min (Nat.fromBitsLE (rowBits c)) (constraintCount (TubeSampleCoefficient.n packet c) - 1)

theorem cappedRow_lt (c : List Bool) : cappedRow packet rowBits c < constraintCount (TubeSampleCoefficient.n packet c) := by
  have hm := Nat.min_le_right (Nat.fromBitsLE (rowBits c)) (constraintCount (TubeSampleCoefficient.n packet c) - 1)
  unfold cappedRow constraintCount at *
  omega

noncomputable def decodedRow (c : List Bool) : PerturbedSource.Index (pairFst (packet c)) :=
  (constraintEquiv (TubeSampleCoefficient.n packet c)).symm ⟨cappedRow packet rowBits c, cappedRow_lt packet rowBits c⟩

theorem decodedRow_code (c : List Bool) :
    TubeSparseConstraintCoefficient.code packet (decodedRow packet rowBits) c = cappedRow packet rowBits c :=
  congrArg Fin.val ((constraintEquiv (TubeSampleCoefficient.n packet c)).apply_symm_apply _)

theorem decodedRow_unary (hp : packet ∈ FP) (hr : rowBits ∈ FP) :
    UnaryFn (TubeSparseConstraintCoefficient.code packet (decodedRow packet rowBits)) := by
  have hc := (TubeZero.constraintCount_unary (TubeSampleCoefficient.n_unary packet hp)).sub (UnaryFn.const 1)
  have hmin := UnaryFn.fromBitsLE_min hr hc
  exact hmin.of_eq (fun c => (decodedRow_code packet rowBits c).symm)

theorem decodedRow_of_code (c : List Bool) (i : PerturbedSource.Index (pairFst (packet c)))
    (hi : Nat.fromBitsLE (rowBits c) = (constraintEquiv (TubeSampleCoefficient.n packet c) i).val) :
    decodedRow packet rowBits c = i := by
  apply (constraintEquiv (TubeSampleCoefficient.n packet c)).injective
  apply Fin.ext
  have he := decodedRow_code packet rowBits c
  change (constraintEquiv (TubeSampleCoefficient.n packet c) (decodedRow packet rowBits c)).val = _ at he
  exact he.trans (by
    unfold cappedRow
    rw [hi]
    exact min_eq_left (by have hlt := (constraintEquiv (TubeSampleCoefficient.n packet c) i).isLt; omega))

theorem encodedEvaluator (modulus : List Bool → List Bool) (W : List Bool → ℕ)
    (target : List Bool → List Bool) (hp : packet ∈ FP) (hr : rowBits ∈ FP)
    (hm : modulus ∈ FP) (hW : UnaryFn W) (ht : target ∈ FP) :
    SpaceFunction (fun c => residueBits
      (((integerConstraint (packet c) (decodedRow packet rowBits c)).coeff
        (TubeSampleCoefficient.exponent packet W target c) : ℤ) : ZMod (ModularResidueSpace.m modulus c))) :=
  evaluator packet modulus W target (decodedRow packet rowBits) hp hm hW ht (decodedRow_unary packet rowBits hp hr)

end LeanCanny.ETR.TubeConstraintCoefficient
