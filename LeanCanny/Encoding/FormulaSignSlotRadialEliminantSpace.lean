/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FormulaSignSlotRadialEliminantParameterPacket
public import LeanCanny.Algebra.MacaulayNormalizedPolynomialSpace
/-! # Original-only native coefficients of the actual normalized formal eliminant

The context retains the original source and coordinate selector. A coefficient
query retains all center, radius, perturbation and target exponents in the
originally bounded parameter box. No row reader, model, homomorphism, or
extraneous determinant guard is supplied to the evaluator.
-/
@[expose] public section
namespace LeanCanny.Encoding.FormulaSignSlotRadialEliminantSpace
open LeanCanny.Algebra LeanCanny.Connectivity LeanCanny.Computation MatrixPower
open FormulaSignSlotRadialEliminantPackingLayout
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] MacaulayUniversal.polynomialValue

private theorem polynomialValue_congr {n : ℕ} {R : Type*} [CommRing R]
    (d e : Fin (n + 1) → ℕ) (W : ℕ)
    (hd : ∀ i, d i < 2 ^ W) (he : ∀ i, e i < 2 ^ W)
    (hWd : Macaulay.level d < 2 ^ W) (hWe : Macaulay.level e < 2 ^ W)
    (p : Fin (n + 1) → MvPolynomial (Fin (n + 1)) R) (h : d = e) :
    MacaulayUniversal.polynomialValue d W hd hWd p = MacaulayUniversal.polynomialValue e W he hWe p := by
  cases h
  rfl

noncomputable def value : List Bool → List Bool :=
  PrimitivePairBits.coefficient FormulaSignSlotRadialEliminantPacked.eliminant

theorem evaluator : SpaceFunction value := by
  have HDE (c : List Bool) : (fun i : Fin (spatial c + 1) => layout.degree c i.val) =
      CoerciveCriticalHomogenization.finDegree (sourceDegree c) := degrees_eq c
  have HH (c : List Bool) (i : Fin (spatial c + 1)) :
      (FormulaSignSlotRadialEliminantPacked.system c i).IsHomogeneous (layout.degree c i.val) := by
    simpa only [CoerciveHomogeneousLayout.finDegree_eq, layout, width] using
      FormulaSignSlotRadialEliminantPacked.homogeneous c i
  have HD (c : List Bool) (i : Fin (spatial c + 1)) : 0 < layout.degree c i.val := by
    simpa only [CoerciveHomogeneousLayout.finDegree_eq, layout, width] using
      CoerciveCriticalHomogenization.finDegree_pos (n := spatial c) (sourceDegree c) i
  have HW (c : List Bool) (i : Fin (spatial c + 1)) : layout.degree c i.val < 2 ^ width c := by
    simpa only [CoerciveHomogeneousLayout.finDegree_eq, layout, width] using
      CoerciveCoordinateEliminant.degree_lt (spatial c) (sourceDegree c) i
  have HL (c : List Bool) : Macaulay.level (fun i : Fin (spatial c + 1) => layout.degree c i.val) < 2 ^ width c := by
    rw [HDE]
    exact CoerciveCoordinateEliminant.level_lt _ _
  have E := MacaulayNormalizedPolynomialBits.evaluator spatial width layout.degree
    FormulaSignSlotRadialEliminantPacked.system layout_polyTime
    FormulaSignSlotRadialEliminantPacked.parameterBox FormulaSignSlotRadialEliminantPacked.parameterBox_binary
    FormulaSignSlotRadialEliminantPacked.coefficient_degree HH HD HW HL
    FormulaSignSlotRadialEliminantParameterCoefficient.value
    FormulaSignSlotRadialEliminantParameterCoefficient.evaluator
    FormulaSignSlotRadialEliminantParameterCoefficient.source_packet
  have HP (c : List Bool) :
      MacaulayUniversal.polynomialValue (fun i : Fin (spatial c + 1) => layout.degree c i.val) (width c)
        (HW c) (HL c) (FormulaSignSlotRadialEliminantPacked.system c) =
          FormulaSignSlotRadialEliminantPacked.eliminant c := by
    exact (polynomialValue_congr (n := spatial c) _ _ (width c) (HW c)
      (CoerciveCoordinateEliminant.degree_lt _ _) (HL c) (CoerciveCoordinateEliminant.level_lt _ _)
      (FormulaSignSlotRadialEliminantPacked.system c) (HDE c)).trans
        (FormulaSignSlotRadialEliminantPacked.polynomialValue c)
  rw [funext HP] at E
  exact E

theorem coefficient_packet (c modulus : List Bool) (k : Fin (FormulaSignSlotRadialEliminantPacked.parameterBox c)) :
    value (pair (pair c (BinaryNatCode.encode k.val)) modulus) =
      residueBits (((FormulaSignSlotRadialEliminantParameterRows.eliminant (pairFst c)
        (FormulaSignSlotRadialEliminantInput.coordinate c)).coeff
          (FixedWidthPolynomial.vector (FormulaSignSlotCenteredRadialGraph.d (pairFst c) + 3)
            (parameterWidth c) k) : ℤ) : ZMod (Nat.fromBitsLE modulus + 1)) := by
  simp only [value, PrimitivePairBits.coefficient, RationalSubstitution.IntegerBits.context,
    RationalSubstitution.IntegerBits.selectedDegree, RationalSubstitution.IntegerBits.mValue,
    pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [FormulaSignSlotRadialEliminantPacked.eliminant_coefficient]
  rfl

private theorem flatten_coefficient_any {a : ℕ}
    (p : Polynomial (Polynomial (Polynomial (MvPolynomial (Fin a) ℤ)))) (f : Fin (a + 3) →₀ ℕ) :
    (TriplePolynomialParameterFlatten.flatten p).coeff f =
      (((p.coeff (f 0)).coeff (f.tail 0)).coeff (f.tail.tail 0)).coeff f.tail.tail.tail := by
  have HE : TriplePolynomialParameterFlatten.exponent (f 0) (f.tail 0) (f.tail.tail 0) f.tail.tail.tail = f := by
    simp only [TriplePolynomialParameterFlatten.exponent, Finsupp.cons_tail]
  exact (congrArg (fun e => (TriplePolynomialParameterFlatten.flatten p).coeff e) HE).symm.trans
    (TriplePolynomialParameterFlatten.coefficient p _ _ _ _)

theorem nested_coefficient_packet (c modulus : List Bool)
    (k : Fin (FormulaSignSlotRadialEliminantPacked.parameterBox c)) :
    let f := FixedWidthPolynomial.vector (FormulaSignSlotCenteredRadialGraph.d (pairFst c) + 3) (parameterWidth c) k
    value (pair (pair c (BinaryNatCode.encode k.val)) modulus) =
      residueBits ((((((FormulaSignSlotRadialFormalEliminant.eliminant (pairFst c)
        (FormulaSignSlotRadialEliminantInput.coordinate c)).coeff (f 0)).coeff (f.tail 0)).coeff
          (f.tail.tail 0)).coeff f.tail.tail.tail : ℤ) : ZMod (Nat.fromBitsLE modulus + 1)) := by
  dsimp only
  rw [coefficient_packet, FormulaSignSlotRadialEliminantParameterRows.eliminant, flatten_coefficient_any]

/-- The native original-input factory stores just the coordinate selector. -/
def sourceContext (c coordinate : List Bool) : List Bool := pair c (WordList.encode [coordinate])

def query (q : List Bool) : List Bool := pair
  (pair (sourceContext (pairFst q) (FormulaSignSlotRadialEliminantInput.field 0 q))
    (FormulaSignSlotRadialEliminantInput.field 1 q)) (FormulaSignSlotRadialEliminantInput.field 2 q)

theorem query_FP : query ∈ FP := by
  have HC := mem_FP_pair pairFst_mem_FP
    (mem_FP_pair (FormulaSignSlotRadialEliminantInput.field_FP 0) (constFn_mem_FP []))
  exact mem_FP_pair (mem_FP_pair HC (FormulaSignSlotRadialEliminantInput.field_FP 1))
    (FormulaSignSlotRadialEliminantInput.field_FP 2)

/-- Input: original source paired with `[coordinate, parameter rank, modulus predecessor]`. -/
noncomputable def nativeValue : List Bool → List Bool := value ∘ query

theorem native_evaluator : SpaceFunction nativeValue := evaluator.precompose query query_FP

theorem sourceContext_original (c coordinate : List Bool) : pairFst (sourceContext c coordinate) = c :=
  pairFst_pair _ _

end LeanCanny.Encoding.FormulaSignSlotRadialEliminantSpace
