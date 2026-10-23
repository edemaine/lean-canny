/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.RationalSubstitutionResidue
public import LeanCanny.Algebra.FixedWidthPolynomialLayout
public import LeanCanny.Algebra.IndexedRationalSubstitutionBudget

/-! # Indexed sources independent of the substituted coordinates

Dense ranks enumerate fixed-width exponent vectors. Projected sources retain
the full rank arity while selecting only the coordinates being substituted.
The access constructors preserve the existing bounded block reader, including
its behavior on malformed packets.
-/

@[expose] public section

namespace LeanCanny.Algebra.RationalSubstitution.IntegerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower

structure IndexedSource where
  arity : List Bool → ℕ
  width : List Bool → ℕ
  terms : List Bool → ℕ
  exponent : List Bool → ℕ → ℕ → ℕ
  coefficient : List Bool → ℕ → ℤ
  exponent_le : ∀ c r, r < terms c → ∀ i, i < arity c → exponent c r i ≤ width c

namespace IndexedSource

noncomputable def withCoordinates (S : IndexedSource)
    (n d : List Bool → ℕ → Polynomial ℤ) : Family where
  arity := S.arity
  width := S.width
  terms := S.terms
  exponent := S.exponent
  coefficient := S.coefficient
  numerator := n
  denominator := d
  exponent_le := S.exponent_le

structure Access (S : IndexedSource) where
  arity : List Bool → List Bool
  width : List Bool → List Bool
  terms : List Bool → List Bool
  exponent : List Bool → List Bool
  coefficient : List Bool → List Bool
  arity_eq : ∀ c, Nat.fromBitsLE (arity c) = S.arity c
  width_eq : ∀ c, Nat.fromBitsLE (width c) = S.width c
  terms_eq : ∀ c, Nat.fromBitsLE (terms c) = S.terms c
  exponent_eq : ∀ c r, r < S.terms c → ∀ i, i < S.arity c →
    Nat.fromBitsLE (exponent (pair c (pair (BinaryNatCode.encode r) (BinaryNatCode.encode i)))) = S.exponent c r i
  coefficient_eq : ∀ c r, r < S.terms c → ∀ m, 0 < m →
    coefficient (pair (pair c (BinaryNatCode.encode r)) (BinaryNatCode.encode (m - 1))) =
      residueBits ((S.coefficient c r : ℤ) : ZMod m)

structure Access.ControlsPolyTime {S : IndexedSource} (a : Access S) : Prop where
  arity : a.arity ∈ FP
  width : a.width ∈ FP
  terms : a.terms ∈ FP
  exponent : a.exponent ∈ FP

noncomputable def access {S : IndexedSource} (a : Access S)
    {n d : List Bool → ℕ → Polynomial ℤ} (C : CoordinateReaders S.arity n d) :
    IntegerBits.Access (S.withCoordinates n d) where
  arity := a.arity
  width := a.width
  terms := a.terms
  exponent := a.exponent
  coefficient := a.coefficient
  numerator := C.numerator
  denominator := C.denominator
  arity_eq := a.arity_eq
  width_eq := a.width_eq
  terms_eq := a.terms_eq
  exponent_eq := a.exponent_eq
  coefficient_eq := a.coefficient_eq
  numerator_eq := C.numerator_eq
  denominator_eq := C.denominator_eq

theorem access_controls {S : IndexedSource} (a : Access S) (h : a.ControlsPolyTime)
    {n d : List Bool → ℕ → Polynomial ℤ} (C : CoordinateReaders S.arity n d) :
    (access a C).ControlsPolyTime := ⟨h.arity, h.width, h.terms, h.exponent⟩

/-- Binary output allowances use only the source metadata and coordinate bounds. -/
def Access.outputDegreeCode {S : IndexedSource} (a : Access S)
    (degree : List Bool → List Bool) (c : List Bool) : List Bool :=
  Indexed.degreeCode (a.arity c) (a.width c) (degree c)

def Access.outputBudgetCode {S : IndexedSource} (a : Access S)
    (degree bits sourceBits : List Bool → List Bool) (c : List Bool) : List Bool :=
  Indexed.coefficientBudgetCode (a.arity c) (a.width c) (a.terms c) (degree c) (bits c) (sourceBits c)

theorem Access.outputDegreeCode_mem_FP {S : IndexedSource} (a : Access S)
    (hA : a.arity ∈ FP) (hW : a.width ∈ FP)
    {degree : List Bool → List Bool} (hE : degree ∈ FP) : a.outputDegreeCode degree ∈ FP :=
  Indexed.degreeCode_mem_FP hA hW hE

theorem Access.outputBudgetCode_mem_FP {S : IndexedSource} (a : Access S)
    (hA : a.arity ∈ FP) (hW : a.width ∈ FP) (hT : a.terms ∈ FP)
    {degree bits sourceBits : List Bool → List Bool} (hE : degree ∈ FP) (hb : bits ∈ FP) (hs : sourceBits ∈ FP) :
    a.outputBudgetCode degree bits sourceBits ∈ FP :=
  Indexed.coefficientBudgetCode_mem_FP hA hW hT hE hb hs

theorem Access.polynomial_degree {S : IndexedSource} (a : Access S)
    {n d : List Bool → ℕ → Polynomial ℤ} (B : CoordinateBounds S.arity n d) (c : List Bool) :
    ((S.withCoordinates n d).polynomial c).natDegree ≤ Nat.fromBitsLE (a.outputDegreeCode B.degree c) := by
  simp only [Access.outputDegreeCode, Indexed.degreeCode_code, BinaryNatCode.encode,
    Nat.fromBitsLE_bits, a.arity_eq, a.width_eq]
  exact Indexed.natDegree_cleared_le _ _ _ _ _ _ _ _ (S.exponent_le c)
    (B.numerator_degree c) (B.denominator_degree c)

theorem Access.polynomial_coefficient_bits {S : IndexedSource} (a : Access S)
    {n d : List Bool → ℕ → Polynomial ℤ} (B : CoordinateBounds S.arity n d)
    (sourceBits : List Bool → List Bool)
    (hsource : ∀ c r, r < S.terms c → (S.coefficient c r).natAbs ≤ 2 ^ Nat.fromBitsLE (sourceBits c))
    (c : List Bool) (k : ℕ) :
    (((S.withCoordinates n d).polynomial c).coeff k).natAbs.size ≤
      Nat.fromBitsLE (a.outputBudgetCode B.degree B.bits sourceBits c) := by
  simp only [Access.outputBudgetCode, Indexed.coefficientBudgetCode_code, BinaryNatCode.encode,
    Nat.fromBitsLE_bits, a.arity_eq, a.width_eq, a.terms_eq]
  exact Indexed.coeff_size_cleared_le _ _ _ _ _ _ _ _ _ (S.exponent_le c) (hsource c)
    (fun i hi => coefficientMass_le_pow_of_degree_coeff _ _ _ (B.numerator_degree c i hi) (B.numerator_coeff c i hi))
    (fun i hi => coefficientMass_le_pow_of_degree_coeff _ _ _ (B.denominator_degree c i hi) (B.denominator_coeff c i hi)) k

/-- Dense fixed-width ranks with an independently chosen clearing allowance. -/
noncomputable def dense (arity blockWidth width : List Bool → ℕ)
    (coefficient : List Bool → ℕ → ℤ)
    (he : ∀ c r i, FixedWidthPolynomial.entry (blockWidth c) r i ≤ width c) : IndexedSource where
  arity := arity
  width := width
  terms c := FixedWidthPolynomial.count (arity c) (blockWidth c)
  exponent c := FixedWidthPolynomial.entry (blockWidth c)
  coefficient := coefficient
  exponent_le c r _ i _ := he c r i

noncomputable def denseAccess (arity blockWidth width : List Bool → ℕ)
    (coefficient : List Bool → ℕ → ℤ)
    (he : ∀ c r i, FixedWidthPolynomial.entry (blockWidth c) r i ≤ width c)
    (arityCode widthCode coefficientRead : List Bool → List Bool)
    (hA : ∀ c, Nat.fromBitsLE (arityCode c) = arity c)
    (hW : ∀ c, Nat.fromBitsLE (widthCode c) = width c)
    (hC : ∀ c r, r < FixedWidthPolynomial.count (arity c) (blockWidth c) → ∀ m, 0 < m →
      coefficientRead (pair (pair c (BinaryNatCode.encode r)) (BinaryNatCode.encode (m - 1))) =
        residueBits ((coefficient c r : ℤ) : ZMod m)) :
    Access (dense arity blockWidth width coefficient he) where
  arity := arityCode
  width := widthCode
  terms := FixedWidthPolynomial.countCode arity blockWidth
  exponent := FixedWidthPolynomial.exponentRead arity blockWidth
  coefficient := coefficientRead
  arity_eq := hA
  width_eq := hW
  terms_eq c := by rw [FixedWidthPolynomial.countCode_code]; exact Nat.fromBitsLE_bits _
  exponent_eq c r _ i hi := by
    rw [FixedWidthPolynomial.exponentRead_packet arity blockWidth c r i hi]
    exact Nat.fromBitsLE_bits _
  coefficient_eq := hC

/-- Full native ranks, with only the selected coordinates substituted. -/
noncomputable def projected (rankArity substitutedArity blockWidth width : List Bool → ℕ)
    (coordinateIndex : List Bool → ℕ → ℕ) (coefficient : List Bool → ℕ → ℤ)
    (he : ∀ c r i, FixedWidthPolynomial.entry (blockWidth c) r (coordinateIndex c i) ≤ width c) : IndexedSource where
  arity := substitutedArity
  width := width
  terms c := FixedWidthPolynomial.count (rankArity c) (blockWidth c)
  exponent c r i := FixedWidthPolynomial.entry (blockWidth c) r (coordinateIndex c i)
  coefficient := coefficient
  exponent_le c r _ i _ := he c r i

/-- `coordinateIndexCode` reads `pair context coordinate`; ranks stay binary. -/
def projectedPacket (coordinateIndexCode : List Bool → List Bool) (q : List Bool) : List Bool :=
  pair (pairFst q) (pair (pairFst (pairSnd q))
    (coordinateIndexCode (pair (pairFst q) (pairSnd (pairSnd q)))))

theorem projectedPacket_mem_FP {index : List Bool → List Bool} (hi : index ∈ FP) : projectedPacket index ∈ FP := by
  have hindex := mem_FP_comp (mem_FP_pair pairFst_mem_FP (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP)) hi
  exact mem_FP_pair pairFst_mem_FP (mem_FP_pair (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP) hindex)

def projectedExponentRead (rankArity blockWidth : List Bool → ℕ)
    (index : List Bool → List Bool) : List Bool → List Bool :=
  FixedWidthPolynomial.exponentRead rankArity blockWidth ∘ projectedPacket index

theorem projectedExponentRead_mem_FP {rankArity blockWidth : List Bool → ℕ}
    {index : List Bool → List Bool} (hA : UnaryFn rankArity) (hW : UnaryFn blockWidth) (hi : index ∈ FP) :
    projectedExponentRead rankArity blockWidth index ∈ FP :=
  mem_FP_comp (projectedPacket_mem_FP hi) (FixedWidthPolynomial.exponentRead_mem_FP hA hW)

theorem projectedExponentRead_packet (rankArity substitutedArity blockWidth : List Bool → ℕ)
    (index : List Bool → List Bool) (coordinateIndex : List Bool → ℕ → ℕ)
    (hindex : ∀ c i, i < substitutedArity c →
      index (pair c (BinaryNatCode.encode i)) = BinaryNatCode.encode (coordinateIndex c i))
    (hbound : ∀ c i, i < substitutedArity c → coordinateIndex c i < rankArity c)
    (c : List Bool) (r i : ℕ) (hi : i < substitutedArity c) :
    Nat.fromBitsLE (projectedExponentRead rankArity blockWidth index
      (pair c (pair (BinaryNatCode.encode r) (BinaryNatCode.encode i)))) =
      FixedWidthPolynomial.entry (blockWidth c) r (coordinateIndex c i) := by
  simp only [projectedExponentRead, Function.comp_apply, projectedPacket, pairFst_pair, pairSnd_pair]
  rw [hindex c i hi, FixedWidthPolynomial.exponentRead_packet _ _ c r _ (hbound c i hi)]
  exact Nat.fromBitsLE_bits _

end IndexedSource
end LeanCanny.Algebra.RationalSubstitution.IntegerBits
