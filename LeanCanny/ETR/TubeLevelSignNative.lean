/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeLevelSignCoefficient

/-! # Native sample counting from root and coordinate coefficient readers

The sign-query coefficient access contract is derived internally. Coordinate
degree/mass bounds supply the query budgets. No expanded sign-query reader is
assumed, and the complete constraint and substitution children are included.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeLevelSign.CoefficientReaders
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open TubeLevelPacket TubeEncoding MatrixPower RationalSubstitution
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm

variable {S : Source} (C : CoefficientReaders S)

set_option backward.isDefEq.respectTransparency false in
noncomputable def access (B : Budget S) : SignPatternBits.Access (family S B) where
  rootCoefficient := C.rootCoefficient
  polynomialCoefficient := polynomialValue S
  pattern := fun _ => InfinitesimalSign.encode .pos
  root_eq := C.root_eq
  polynomial_eq c i hi k m hm := by
    have hlt : i < constraintCount (TubeIndexed.arity (pairFst (S.packet c))) := by
      simpa only [family, BinaryNatCode.encode, Nat.fromBitsLE_bits] using hi
    let j := (constraintEquiv (TubeIndexed.arity (pairFst (S.packet c)))).symm ⟨i, hlt⟩
    have hj : (constraintEquiv (TubeIndexed.arity (pairFst (S.packet c))) j).val = i :=
      congrArg Fin.val ((constraintEquiv _).apply_symm_apply ⟨i, hlt⟩)
    have he := polynomialValue_packet S c j k m hm
    rw [hj] at he
    have hq := indexedSignQuery_constraint (S.packet c) (S.mask c) (S.projection c)
      (S.level c) (S.coordinates c) j
    rw [hj] at hq
    change polynomialValue S _ = IntegerBits.coefficientResidue
      ((indexedSignQuery (S.packet c) (S.mask c) (S.projection c) (S.level c) (S.coordinates c) i).coeff k) m
    rw [hq]
    exact he
  pattern_eq _ _ := rfl

include C

theorem countEvaluator (B : CoordinateBudget S) (hp : S.packet ∈ FP) (hm : S.mask ∈ FP) :
    SpaceFunction (fun c => BinaryNatCode.encode (sampleCount S c)) :=
  B.countEvaluator hp (C.access B.budget) C.rootEvaluator (polynomialEvaluator S C hp hm)

theorem sampleDecider (B : CoordinateBudget S) (hp : S.packet ∈ FP) (hm : S.mask ∈ FP) :
    SpaceDecider (sampleLanguage S) :=
  TubeLevelSign.sampleDecider (C.access B.budget) (B.controls hp)
    C.rootEvaluator (polynomialEvaluator S C hp hm)

theorem sampleLanguage_mem_PSPACE (B : CoordinateBudget S) (hp : S.packet ∈ FP) (hm : S.mask ∈ FP) :
    sampleLanguage S ∈ PSPACE := (C.sampleDecider B hp hm).mem_PSPACE

end LeanCanny.ETR.TubeLevelSign.CoefficientReaders
