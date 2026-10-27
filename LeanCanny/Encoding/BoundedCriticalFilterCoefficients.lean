/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedCriticalFilters
public import LeanCanny.Algebra.FiniteLeafSignSource
public import LeanCanny.Algebra.FixedWidthPolynomialFP

/-! # Native modular coefficients of the exact critical-sample filters

Dense monomial ranks stream the original critical equations. The existing
rational-substitution machine combines their native coefficients with the
computed coordinate readers, without expanding a polynomial in memory.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedCriticalFilterCoefficients
open LeanCanny.ETR LeanCanny.Algebra LeanCanny.Computation BoundedFullWriter
open RationalSubstitution.Indexed MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] BoundedCriticalRationalCoordinates.coordinate
  BoundedFullCriticalSamples.equations RationalSubstitution.Indexed.exponentVector

noncomputable def arity (P : Readers) (w : List Bool) : ℕ := P.dim (pairFst w) + 4
noncomputable def width (P : Readers) (w : List Bool) : ℕ := BoundedCriticalProjection.systemWidth P (pairFst w)

noncomputable def sourceCoefficient (P : Readers) (w : List Bool) (r : ℕ) : ℤ :=
  (BoundedFullCriticalSamples.equations P (pairFst w) (BoundedCriticalFilters.row P w)).coeff
    (exponentVector (arity P w) (FixedWidthPolynomial.entry (width P w) r))

theorem source_eq (P : Readers) (w : List Bool) :
    RationalSubstitution.Indexed.source (arity P w) (FixedWidthPolynomial.count (arity P w) (width P w))
      (sourceCoefficient P w) (FixedWidthPolynomial.entry (width P w)) =
        BoundedFullCriticalSamples.equations P (pairFst w) (BoundedCriticalFilters.row P w) := by
  apply FixedWidthPolynomial.indexed_source_eq
  intro m hm i
  exact (MvPolynomial.monomial_le_degreeOf i hm).trans_lt
    (BoundedCriticalFilters.equation_degree P (pairFst w) (BoundedCriticalFilters.row P w) i)

noncomputable def family (P : Readers) : RationalSubstitution.IntegerBits.Family where
  arity := arity P
  width w := 2 * BoundedCriticalFilters.gridDegree P (pairFst w)
  terms w := FixedWidthPolynomial.count (arity P w) (width P w)
  coefficient := sourceCoefficient P
  exponent w := FixedWidthPolynomial.entry (width P w)
  numerator w := BoundedCriticalFilters.numerator P (pairFst w)
  denominator w := BoundedCriticalFilters.denominator P (pairFst w)
  exponent_le w _ _ _ _ := (FixedWidthPolynomial.entry_lt _ _ _).le.trans (by
    change BoundedCriticalFilters.gridDegree P (pairFst w) ≤ 2 * BoundedCriticalFilters.gridDegree P (pairFst w)
    omega)

theorem polynomial_eq (P : Readers) (w : List Bool) :
    (family P).polynomial w = BoundedCriticalFilters.polynomial P w := by
  unfold RationalSubstitution.IntegerBits.Family.polynomial
  rw [family, cleared_eq_clearedWith_source, source_eq]
  rfl

def base (q : List Bool) : List Bool := pairFst (pairFst (pairFst q))
def rowContext (q : List Bool) : List Bool := pairFst (pairFst q)
def rank (q : List Bool) : List Bool := pairSnd (pairFst q)
theorem base_FP : base ∈ FP := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairFst_mem_FP
theorem rowContext_FP : rowContext ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
theorem rank_FP : rank ∈ FP := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP

theorem equations_comp (P : Readers) (f : List Bool → List Bool) (c : List Bool) :
    BoundedCriticalSampleQuery.equations (P.comp f) (BoundedFullDirectionChoice.record (P.comp f)) c =
      BoundedFullCriticalSamples.equations P (f c) := by
  unfold BoundedCriticalSampleQuery.equations BoundedFullCriticalSamples.equations
    BoundedFullCriticalSamples.direction BoundedFullDirectionQueries.direction FixedWidthQuery.coordinate
  simp only [BoundedFullDirectionChoice.record_comp]
  rfl

noncomputable def coefficient (P : Readers) : List Bool → List Bool :=
  BoundedCriticalCoefficient.value (P.comp base) (BoundedFullDirectionChoice.record (P.comp base))
    (fun q => BoundedCriticalFilters.row P (rowContext q))
    (BoundedCriticalProjection.systemWidth P ∘ base) rank pairSnd

theorem coefficient_evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) : SpaceFunction (coefficient P) :=
  BoundedCriticalCoefficient.selected_evaluator (h.comp base_FP)
    ((BoundedCriticalFilters.row_unary h).comp rowContext_FP)
    ((BoundedCriticalProjection.systemWidth_unary h).comp base_FP) rank_FP pairSnd_mem_FP
    (fun q => ha (base q)) (fun q => BoundedProjectionMacaulay.width_fits P (base q))

theorem coefficient_eq (P : Readers) (q : List Bool) : coefficient P q =
    residueBits (((BoundedFullCriticalSamples.equations P (base q)
      (BoundedCriticalFilters.row P (rowContext q))).coeff
        (exponentVector (P.dim (base q) + 4)
          (FixedWidthQuery.coordinate (BoundedCriticalProjection.systemWidth P ∘ base) rank q)) : ℤ) :
            ZMod (Nat.fromBitsLE (pairSnd q) + 1)) := by
  unfold coefficient BoundedCriticalCoefficient.value
  rw [equations_comp]
  rfl

theorem coefficient_packet (P : Readers) (w : List Bool) (r m : ℕ) (hm : 0 < m) :
    coefficient P (pair (pair w (BinaryNatCode.encode r)) (BinaryNatCode.encode (m - 1))) =
      residueBits ((sourceCoefficient P w r : ℤ) : ZMod m) := by
  generalize hq : pair (pair w (BinaryNatCode.encode r)) (BinaryNatCode.encode (m - 1)) = q
  have hw : rowContext q = w := by rw [← hq]; simp only [rowContext, pairFst_pair]
  have hk : rank q = BinaryNatCode.encode r := by rw [← hq]; simp only [rank, pairFst_pair, pairSnd_pair]
  have hm' : Nat.fromBitsLE (pairSnd q) + 1 = m := by
    rw [← hq, pairSnd_pair]
    simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
    omega
  subst w
  have he : FixedWidthQuery.coordinate (BoundedCriticalProjection.systemWidth P ∘ base) rank q =
      FixedWidthPolynomial.entry (width P (rowContext q)) r := by
    funext i
    simp only [FixedWidthQuery.coordinate, Function.comp_apply, hk, FixedWidthPolynomial.entry,
      width, rowContext, base, BinaryNatCode.encode]
  rw [coefficient_eq]
  exact congrArg₂ (fun (z : ℤ) (m : ℕ) => residueBits (z : ZMod m))
    (by unfold sourceCoefficient; rw [he]; rfl) hm'

noncomputable def numerator (P : Readers) : List Bool → List Bool :=
  PrimitivePairBits.coefficient (fun u => (BoundedCriticalRationalCoordinates.coordinate P u).numerator) ∘
    FiniteLeafSignBits.coordinateQuery
noncomputable def denominator (P : Readers) : List Bool → List Bool :=
  PrimitivePairBits.coefficient (fun u => (BoundedCriticalRationalCoordinates.coordinate P u).denominator) ∘
    FiniteLeafSignBits.coordinateQuery

noncomputable def access (P : Readers) : RationalSubstitution.IntegerBits.Access (family P) where
  arity w := BinaryNatCode.encode (arity P w)
  width w := BinaryNatCode.encode (2 * BoundedCriticalFilters.gridDegree P (pairFst w))
  terms := FixedWidthPolynomial.countCode (arity P) (width P)
  exponent := FixedWidthPolynomial.exponentRead (arity P) (width P)
  coefficient := coefficient P
  numerator := numerator P
  denominator := denominator P
  arity_eq _ := Nat.fromBitsLE_bits _
  width_eq _ := Nat.fromBitsLE_bits _
  terms_eq w := by rw [FixedWidthPolynomial.countCode_code]; exact Nat.fromBitsLE_bits _
  exponent_eq w r _ i hi := by
    rw [FixedWidthPolynomial.exponentRead_packet (arity P) (width P) w r i hi]
    exact Nat.fromBitsLE_bits _
  coefficient_eq w r _ m hm := coefficient_packet P w r m hm
  numerator_eq w i _ k m hm := by
    simp only [numerator, Function.comp_apply, PrimitivePairBits.coefficient,
      RationalSubstitution.IntegerBits.coefficientResidue]
    exact congrArg₂ (fun (z : ℤ) (m : ℕ) => residueBits (z : ZMod m))
      (by simp only [FiniteLeafSignBits.coordinateQuery, RationalSubstitution.IntegerBits.context,
        RationalSubstitution.IntegerBits.selectedDegree, pairFst_pair, pairSnd_pair,
        BinaryNatCode.encode, Nat.fromBitsLE_bits]; rfl)
      (by simp only [RationalSubstitution.IntegerBits.mValue, FiniteLeafSignBits.coordinateQuery, pairSnd_pair,
        BinaryNatCode.encode, Nat.fromBitsLE_bits]; omega)
  denominator_eq w i _ k m hm := by
    simp only [denominator, Function.comp_apply, PrimitivePairBits.coefficient,
      RationalSubstitution.IntegerBits.coefficientResidue]
    exact congrArg₂ (fun (z : ℤ) (m : ℕ) => residueBits (z : ZMod m))
      (by simp only [FiniteLeafSignBits.coordinateQuery, RationalSubstitution.IntegerBits.context,
        RationalSubstitution.IntegerBits.selectedDegree, pairFst_pair, pairSnd_pair,
        BinaryNatCode.encode, Nat.fromBitsLE_bits]; rfl)
      (by simp only [RationalSubstitution.IntegerBits.mValue, FiniteLeafSignBits.coordinateQuery, pairSnd_pair,
        BinaryNatCode.encode, Nat.fromBitsLE_bits]; omega)

theorem evaluator {P : Readers} (h : P.PolyTime)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (PrimitivePairBits.coefficient (BoundedCriticalFilters.polynomial P)) := by
  have hn : UnaryFn (arity P) := (h.dim.comp pairFst_mem_FP).add (UnaryFn.const 4)
  have hw := (BoundedCriticalProjection.systemWidth_unary h).comp pairFst_mem_FP
  have E := BoundedCriticalRationalCoordinates.coefficient_evaluators h ha
  have R := (access P).evaluator
    ⟨(BinaryFn.ofUnary hn).bits_mem_FP,
      ((BinaryFn.const 2).mul ((BoundedCriticalFilters.gridDegree_binary h).comp pairFst_mem_FP)).bits_mem_FP,
      FixedWidthPolynomial.countCode_mem_FP hn hw, FixedWidthPolynomial.exponentRead_mem_FP hn hw⟩
    (coefficient_evaluator h ha) (E.1.precompose _ FiniteLeafSignBits.coordinateQuery_FP)
    (E.2.precompose _ FiniteLeafSignBits.coordinateQuery_FP)
  refine R.congr (funext fun q => ?_)
  simp only [RationalSubstitution.IntegerBits.Family.value, polynomial_eq, PrimitivePairBits.coefficient]

end LeanCanny.Encoding.BoundedCriticalFilterCoefficients
