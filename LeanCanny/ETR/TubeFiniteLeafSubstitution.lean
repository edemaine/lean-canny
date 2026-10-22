/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FiniteLeafCoordinateFiltering
public import LeanCanny.ETR.TubeConstraintSubstitution

/-! # Tube constraints on the computed finite-leaf coordinates

Reindexing the native finite-leaf coefficient readers supplies the actual
integer tube-constraint substitution. Only original annihilator readers and
bounds are assumed. No interpolated representation or expanded constraint
coefficient reader is supplied.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeFiniteLeafSubstitution
open LeanCanny.Encoding LeanCanny.Computation LeanCanny.Algebra
open RationalSubstitution
open SeparableBits (Family Readers)
open scoped Classical

variable (B : Family) (packet : List Bool → List Bool) (D b : List Bool → ℕ)
variable (hne : ∀ c i, i < TubeSampleCoefficient.A packet c →
  B.polynomial (pair c (BinaryNatCode.encode i)) ≠ 0)

noncomputable def numerator (c : List Bool) (i : ℕ) : Polynomial ℤ :=
  if hi : i < TubeSampleCoefficient.A packet c then
    FiniteLeafCoordinateBits.numerator B (TubeSampleCoefficient.A packet) D b hne c ⟨i, hi⟩ else 0

noncomputable def denominator (c : List Bool) (i : ℕ) : Polynomial ℤ :=
  if hi : i < TubeSampleCoefficient.A packet c then
    FiniteLeafCoordinateBits.denominator B (TubeSampleCoefficient.A packet) D b hne c ⟨i, hi⟩ else 0

/-- Move the coordinate index into the finite-leaf context, retaining degree and modulus. -/
def coordinateQuery (q : List Bool) : List Bool :=
  pair (pair (pair (IntegerBits.context q) (pairFst (IntegerBits.selectedDegree q)))
    (pairSnd (IntegerBits.selectedDegree q))) (pairSnd q)

theorem coordinateQuery_FP : coordinateQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_pair IntegerBits.context_mem_FP
    (mem_FP_comp IntegerBits.selectedDegree_mem_FP pairFst_mem_FP))
    (mem_FP_comp IntegerBits.selectedDegree_mem_FP pairSnd_mem_FP)) pairSnd_mem_FP

noncomputable def numeratorValue : List Bool → List Bool :=
  PrimitivePairBits.coefficient
    (fun u => (FiniteLeafCoordinateBits.coordinate B (TubeSampleCoefficient.A packet) D b hne u).numerator) ∘ coordinateQuery

noncomputable def denominatorValue : List Bool → List Bool :=
  PrimitivePairBits.coefficient
    (fun u => (FiniteLeafCoordinateBits.coordinate B (TubeSampleCoefficient.A packet) D b hne u).denominator) ∘ coordinateQuery

variable (hdegree : ∀ c i, i < TubeSampleCoefficient.A packet c →
  (B.polynomial (pair c (BinaryNatCode.encode i))).natDegree ≤ D c)
variable (hheight : ∀ c i, i < TubeSampleCoefficient.A packet c →
  B.height (pair c (BinaryNatCode.encode i)) ≤ b c)

include hdegree hheight in
noncomputable def coordinateReaders (A : Readers B) (hp : packet ∈ FP) (hD : BinaryFn D) (hb : BinaryFn b) :
    TubeConstraintSubstitution.CoordinateReaders packet
      (numerator B packet D b hne) (denominator B packet D b hne) where
  numerator := numeratorValue B packet D b hne
  denominator := denominatorValue B packet D b hne
  numeratorEvaluator := (FiniteLeafCoordinateBits.coefficientEvaluators B (TubeSampleCoefficient.A packet) D b hne
    hdegree hheight A (TubeSampleCoefficient.A_unary packet hp) hD hb).1.precompose _ coordinateQuery_FP
  denominatorEvaluator := (FiniteLeafCoordinateBits.coefficientEvaluators B (TubeSampleCoefficient.A packet) D b hne
    hdegree hheight A (TubeSampleCoefficient.A_unary packet hp) hD hb).2.precompose _ coordinateQuery_FP
  numerator_eq c i hi k m hm := by
    simp only [numeratorValue, Function.comp_apply, coordinateQuery, PrimitivePairBits.coefficient,
      IntegerBits.context, IntegerBits.selectedDegree, IntegerBits.mValue, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.sub_add_cancel hm,
      numerator, dite_eq_left hi, FiniteLeafCoordinateBits.numerator]
    rfl
  denominator_eq c i hi k m hm := by
    simp only [denominatorValue, Function.comp_apply, coordinateQuery, PrimitivePairBits.coefficient,
      IntegerBits.context, IntegerBits.selectedDegree, IntegerBits.mValue, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.sub_add_cancel hm,
      denominator, dite_eq_left hi, FiniteLeafCoordinateBits.denominator]
    rfl

variable (row : List Bool → List Bool)

noncomputable def family : IntegerBits.Family :=
  TubeConstraintSubstitution.family packet row (numerator B packet D b hne) (denominator B packet D b hne)

include hdegree hheight in
theorem evaluator (A : Readers B) (hp : packet ∈ FP) (hr : row ∈ FP) (hD : BinaryFn D) (hb : BinaryFn b) :
    SpaceFunction (family B packet D b hne row).value :=
  TubeConstraintSubstitution.evaluator packet row _ _
    (coordinateReaders B packet D b hne hdegree hheight A hp hD hb) hp hr

theorem polynomial_eq (c : List Bool) :
    (family B packet D b hne row).polynomial c =
      FiniteLeafCoordinateBits.constraint B (TubeSampleCoefficient.A packet) D b hne c
        (fun _ => TubeIndexed.degreeBound (pairFst (packet c)))
        (TubeLevelPacket.integerConstraint (packet c) (TubeConstraintCoefficient.decodedRow packet row c)) := by
  rw [family, TubeConstraintSubstitution.polynomial_eq]
  unfold FiniteLeafCoordinateBits.constraint
  congr 1 <;> funext i
  · exact dite_eq_left i.isLt
  · exact dite_eq_left i.isLt

include hdegree hheight in
theorem zero_iff {K : Type*} [Field K] [CharZero K] (c : List Bool) (theta : K)
    (ht : (FiniteAnnihilatorBits.finiteParameter B (TubeSampleCoefficient.A packet) hne c).eval₂ (Int.castRingHom K) theta = 0) :
    ((family B packet D b hne row).polynomial c).eval₂ (Int.castRingHom K) theta = 0 ↔
      (TubeLevelPacket.integerConstraint (packet c) (TubeConstraintCoefficient.decodedRow packet row c)).eval₂ (Int.castRingHom K)
        (FiniteAnnihilatorTree.decode (fun j => B.polynomial (pair c (BinaryNatCode.encode j)))
          (TubeSampleCoefficient.A packet c) (hne c) theta) = 0 := by
  rw [polynomial_eq]
  exact FiniteLeafCoordinateBits.constraint_zero_iff B (TubeSampleCoefficient.A packet) D b hne hdegree hheight c _ _
    (TubeLevelPacket.integerConstraint_degreeOf _ _) theta ht

include hdegree hheight in
theorem sign_eq (c : List Bool) (theta : ℝ)
    (ht : (FiniteAnnihilatorBits.finiteParameter B (TubeSampleCoefficient.A packet) hne c).eval₂ (Int.castRingHom ℝ) theta = 0) :
    SignType.sign (((family B packet D b hne row).polynomial c).eval₂ (Int.castRingHom ℝ) theta) =
      SignType.sign ((TubeLevelPacket.integerConstraint (packet c) (TubeConstraintCoefficient.decodedRow packet row c)).eval₂ (Int.castRingHom ℝ)
        (FiniteAnnihilatorTree.decode (fun j => B.polynomial (pair c (BinaryNatCode.encode j)))
          (TubeSampleCoefficient.A packet c) (hne c) theta)) := by
  rw [polynomial_eq]
  exact FiniteLeafCoordinateBits.constraint_sign B (TubeSampleCoefficient.A packet) D b hne hdegree hheight c _ _
    (TubeLevelPacket.integerConstraint_degreeOf _ _) theta ht

end LeanCanny.ETR.TubeFiniteLeafSubstitution
