/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeConstraintIndexed
public import LeanCanny.Algebra.IndexedSource

/-! # Native rational substitution into the actual integer constraints

Only coordinate polynomial readers are supplied. The complete native constraint
reader, rank exponents, and clearing allowance instantiate the substitution
engine, with every child computation included in its space certificate.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeConstraintSubstitution
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open TubeLevelPacket MatrixPower RationalSubstitution
open scoped Classical
attribute [local irreducible] RationalSubstitutionBits.compiledTerm

variable (packet row : List Bool → List Bool)
variable (n d : List Bool → ℕ → Polynomial ℤ)

noncomputable def indexedSource : IntegerBits.IndexedSource :=
  IntegerBits.IndexedSource.dense (TubeSampleCoefficient.A packet) (TubeConstraintIndexed.blockWidth packet)
    (fun c => 2 * TubeIndexed.degreeBound (pairFst (packet c))) (TubeConstraintIndexed.coefficient packet row)
    (fun _ _ _ => (FixedWidthPolynomial.entry_lt _ _ _).le.trans (TubeIndexed.clearingWidth_le _))

noncomputable def family : IntegerBits.Family :=
  (indexedSource packet row).withCoordinates n d

theorem polynomial_eq (c : List Bool) : (family packet row n d).polynomial c =
    clearedWith (fun _ => TubeIndexed.degreeBound (pairFst (packet c)))
      (integerConstraint (packet c) (TubeConstraintCoefficient.decodedRow packet row c))
      (fun i => n c i.val) (fun i => d c i.val) := by
  unfold IntegerBits.Family.polynomial family indexedSource IntegerBits.IndexedSource.withCoordinates IntegerBits.IndexedSource.dense
  rw [Indexed.cleared_eq_clearedWith_source, TubeConstraintIndexed.source_eq]
  rfl

noncomputable def arityCode (c : List Bool) : List Bool := BinaryNatCode.encode (TubeSampleCoefficient.A packet c)

noncomputable def widthCode (c : List Bool) : List Bool :=
  BinaryNatCode.encode (2 * TubeIndexed.degreeBound (pairFst (packet c)))

noncomputable def termsCode : List Bool → List Bool :=
  FixedWidthPolynomial.countCode (TubeSampleCoefficient.A packet) (TubeConstraintIndexed.blockWidth packet)

noncomputable def exponentRead : List Bool → List Bool :=
  FixedWidthPolynomial.exponentRead (TubeSampleCoefficient.A packet) (TubeConstraintIndexed.blockWidth packet)

theorem arityCode_FP (hp : packet ∈ FP) : arityCode packet ∈ FP :=
  bits_mem_FP (TubeSampleCoefficient.A_unary packet hp)

theorem widthCode_FP (hp : packet ∈ FP) : widthCode packet ∈ FP :=
  bits_mem_FP ((UnaryFn.const 2).mul (TubeIndexed.degreeBound_unary.comp (mem_FP_comp hp pairFst_mem_FP)))

theorem termsCode_FP (hp : packet ∈ FP) : termsCode packet ∈ FP :=
  FixedWidthPolynomial.countCode_mem_FP (TubeSampleCoefficient.A_unary packet hp) (TubeConstraintIndexed.blockWidth_unary packet hp)

theorem exponentRead_FP (hp : packet ∈ FP) : exponentRead packet ∈ FP :=
  FixedWidthPolynomial.exponentRead_mem_FP (TubeSampleCoefficient.A_unary packet hp) (TubeConstraintIndexed.blockWidth_unary packet hp)

def CoordinateReaders :=
  IntegerBits.CoordinateReaders (TubeSampleCoefficient.A packet) n d

-- Preserve the original qualified constructor and field names.
namespace CoordinateReaders
variable {packet n d}

abbrev mk := @IntegerBits.CoordinateReaders.mk (TubeSampleCoefficient.A packet) n d
abbrev numerator (self : CoordinateReaders packet n d) := IntegerBits.CoordinateReaders.numerator self
abbrev denominator (self : CoordinateReaders packet n d) := IntegerBits.CoordinateReaders.denominator self
abbrev numeratorEvaluator (self : CoordinateReaders packet n d) := IntegerBits.CoordinateReaders.numeratorEvaluator self
abbrev denominatorEvaluator (self : CoordinateReaders packet n d) := IntegerBits.CoordinateReaders.denominatorEvaluator self
abbrev numerator_eq (self : CoordinateReaders packet n d) := IntegerBits.CoordinateReaders.numerator_eq self
abbrev denominator_eq (self : CoordinateReaders packet n d) := IntegerBits.CoordinateReaders.denominator_eq self

end CoordinateReaders

/-- Reindex only the context, retaining the binary coordinate, degree, and modulus. -/
abbrev coordinateQuery := IntegerBits.coordinateQuery

theorem coordinateQuery_FP (f : List Bool → List Bool) (hf : f ∈ FP) : coordinateQuery f ∈ FP :=
  IntegerBits.coordinateQuery_mem_FP hf

noncomputable def CoordinateReaders.precompose (C : CoordinateReaders packet n d) (f : List Bool → List Bool) (hf : f ∈ FP) :
    CoordinateReaders (packet ∘ f) (fun c => n (f c)) (fun c => d (f c)) :=
  IntegerBits.CoordinateReaders.precompose C f hf

noncomputable def sourceAccess : IntegerBits.IndexedSource.Access (indexedSource packet row) :=
  IntegerBits.IndexedSource.denseAccess (TubeSampleCoefficient.A packet) (TubeConstraintIndexed.blockWidth packet)
    (fun c => 2 * TubeIndexed.degreeBound (pairFst (packet c))) (TubeConstraintIndexed.coefficient packet row)
    (fun _ _ _ => (FixedWidthPolynomial.entry_lt _ _ _).le.trans (TubeIndexed.clearingWidth_le _)) (arityCode packet) (widthCode packet)
    (TubeConstraintIndexed.value packet row) (fun _ => Nat.fromBitsLE_bits _) (fun _ => Nat.fromBitsLE_bits _)
    (fun c r _ m hm => TubeConstraintIndexed.value_packet packet row c r m hm)

noncomputable def access (C : CoordinateReaders packet n d) : IntegerBits.Access (family packet row n d) :=
  IntegerBits.IndexedSource.access (sourceAccess packet row) C

theorem access_controls (C : CoordinateReaders packet n d) (hp : packet ∈ FP) :
    (access packet row n d C).ControlsPolyTime :=
  IntegerBits.IndexedSource.access_controls (n := n) (d := d) (sourceAccess packet row)
    ⟨arityCode_FP packet hp, widthCode_FP packet hp, termsCode_FP packet hp, exponentRead_FP packet hp⟩ C

theorem evaluator (C : CoordinateReaders packet n d) (hp : packet ∈ FP) (hr : row ∈ FP) :
    SpaceFunction (family packet row n d).value :=
  (access packet row n d C).evaluator (access_controls packet row n d C hp)
    (TubeConstraintIndexed.evaluator packet row hp hr) C.numeratorEvaluator C.denominatorEvaluator

end LeanCanny.ETR.TubeConstraintSubstitution
