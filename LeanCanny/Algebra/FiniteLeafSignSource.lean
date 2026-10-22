/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FiniteLeafCoordinateFiltering
public import LeanCanny.Algebra.FiniteAnnihilatorHeight
public import LeanCanny.Algebra.RationalSubstitutionResidue
public import LeanCanny.Algebra.IndexedRationalSubstitutionBudget
public import LeanCanny.Algebra.SignPatternSpace

/-! # Streamed constraints on native finite-annihilator coordinates -/

@[expose] public section

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace LeanCanny.Algebra.FiniteLeafSignBits
open Polynomial LeanCanny.Encoding LeanCanny.Computation
open RationalSubstitution
open SeparableBits (Family Readers)
open scoped Classical

/-- Streamed monomial rows with binary term, degree, and height controls. -/
structure Source (arity : List Bool → ℕ) where
  count : List Bool → ℕ
  terms : List Bool → ℕ
  degree : List Bool → ℕ
  height : List Bool → ℕ
  coefficient : List Bool → ℕ → ℕ → ℤ
  exponent : List Bool → ℕ → ℕ → ℕ → ℕ
  pattern : List Bool → ℕ → SignType
  exponent_le : ∀ c j r, r < terms c → ∀ i, i < arity c → exponent c j r i ≤ 2 * degree c
  coefficient_le : ∀ c j r, r < terms c → (coefficient c j r).natAbs ≤ 2 ^ height c

noncomputable def Source.polynomial {arity : List Bool → ℕ} (S : Source arity) (c : List Bool) (j : ℕ) :
    MvPolynomial (Fin (arity c)) ℤ :=
  Indexed.source (arity c) (S.terms c) (S.coefficient c j) (S.exponent c j)

/-- A selected row is encoded as `pair c row`; arbitrary row words are decoded. -/
structure Source.Access {arity : List Bool → ℕ} (S : Source arity) where
  coefficient : List Bool → List Bool
  exponent : List Bool → List Bool
  pattern : List Bool → List Bool
  count_unary : UnaryFn S.count
  terms_binary : BinaryFn S.terms
  degree_binary : BinaryFn S.degree
  height_binary : BinaryFn S.height
  coefficientEvaluator : SpaceFunction coefficient
  exponent_FP : exponent ∈ FP
  pattern_FP : pattern ∈ FP
  coefficient_eq : ∀ q r, r < S.terms (pairFst q) → ∀ m, 0 < m →
    coefficient (pair (pair q (BinaryNatCode.encode r)) (BinaryNatCode.encode (m - 1))) =
      MatrixPower.residueBits ((S.coefficient (pairFst q) (Nat.fromBitsLE (pairSnd q)) r : ℤ) : ZMod m)
  exponent_eq : ∀ q r, r < S.terms (pairFst q) → ∀ i, i < arity (pairFst q) →
    Nat.fromBitsLE (exponent (pair q (pair (BinaryNatCode.encode r) (BinaryNatCode.encode i)))) =
      S.exponent (pairFst q) (Nat.fromBitsLE (pairSnd q)) r i
  pattern_eq : ∀ c j, pattern (pair c (BinaryNatCode.encode j)) = InfinitesimalSign.encode (S.pattern c j)

variable (B : Family) (count D b : List Bool → ℕ)
variable (hne : ∀ c i, i < count c → B.polynomial (pair c (BinaryNatCode.encode i)) ≠ 0)

noncomputable def numerator (q : List Bool) (i : ℕ) : ℤ[X] :=
  (FiniteLeafCoordinateBits.coordinate B count D b hne (pair (pairFst q) (BinaryNatCode.encode i))).numerator
noncomputable def denominator (q : List Bool) (i : ℕ) : ℤ[X] :=
  (FiniteLeafCoordinateBits.coordinate B count D b hne (pair (pairFst q) (BinaryNatCode.encode i))).denominator

noncomputable def substitution (S : Source count) : IntegerBits.Family where
  arity q := count (pairFst q)
  width q := 2 * S.degree (pairFst q)
  terms q := S.terms (pairFst q)
  coefficient q := S.coefficient (pairFst q) (Nat.fromBitsLE (pairSnd q))
  exponent q := S.exponent (pairFst q) (Nat.fromBitsLE (pairSnd q))
  numerator := numerator B count D b hne
  denominator := denominator B count D b hne
  exponent_le _q r hr i hi := S.exponent_le _ _ r hr i hi

def coordinateQuery (q : List Bool) : List Bool :=
  pair (pair (pair (pairFst (IntegerBits.context q)) (pairFst (IntegerBits.selectedDegree q)))
    (pairSnd (IntegerBits.selectedDegree q))) (pairSnd q)

theorem coordinateQuery_FP : coordinateQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_pair (mem_FP_comp IntegerBits.context_mem_FP pairFst_mem_FP)
    (mem_FP_comp IntegerBits.selectedDegree_mem_FP pairFst_mem_FP))
    (mem_FP_comp IntegerBits.selectedDegree_mem_FP pairSnd_mem_FP)) pairSnd_mem_FP

noncomputable def numeratorValue : List Bool → List Bool :=
  PrimitivePairBits.coefficient (fun u => (FiniteLeafCoordinateBits.coordinate B count D b hne u).numerator) ∘ coordinateQuery
noncomputable def denominatorValue : List Bool → List Bool :=
  PrimitivePairBits.coefficient (fun u => (FiniteLeafCoordinateBits.coordinate B count D b hne u).denominator) ∘ coordinateQuery

noncomputable def substitutionAccess (S : Source count) (A : S.Access) :
    IntegerBits.Access (substitution B count D b hne S) where
  arity q := BinaryNatCode.encode (count (pairFst q))
  width q := BinaryNatCode.encode (2 * S.degree (pairFst q))
  terms q := BinaryNatCode.encode (S.terms (pairFst q))
  exponent := A.exponent
  coefficient := A.coefficient
  numerator := numeratorValue B count D b hne
  denominator := denominatorValue B count D b hne
  arity_eq _ := Nat.fromBitsLE_bits _
  width_eq _ := Nat.fromBitsLE_bits _
  terms_eq _ := Nat.fromBitsLE_bits _
  exponent_eq q r hr i hi := A.exponent_eq q r hr i hi
  coefficient_eq q r hr m hm := A.coefficient_eq q r hr m hm
  numerator_eq c i _ k m hm := by
    simp only [numeratorValue, Function.comp_apply, coordinateQuery, PrimitivePairBits.coefficient,
      IntegerBits.context, IntegerBits.selectedDegree, IntegerBits.mValue, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.sub_add_cancel hm]
    rfl
  denominator_eq c i _ k m hm := by
    simp only [denominatorValue, Function.comp_apply, coordinateQuery, PrimitivePairBits.coefficient,
      IntegerBits.context, IntegerBits.selectedDegree, IntegerBits.mValue, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.sub_add_cancel hm]
    rfl

attribute [local irreducible] FiniteLeafCoordinateBits.coordinate

variable (hdegree : ∀ c i, i < count c → (B.polynomial (pair c (BinaryNatCode.encode i))).natDegree ≤ D c)
variable (hheight : ∀ c i, i < count c → B.height (pair c (BinaryNatCode.encode i)) ≤ b c)

include hdegree hheight in
theorem substitutionEvaluator (S : Source count) (A : S.Access) (R : Readers B)
    (hn : UnaryFn count) (hD : BinaryFn D) (hb : BinaryFn b) :
    SpaceFunction (substitution B count D b hne S).value := by
  have E := FiniteLeafCoordinateBits.coefficientEvaluators B count D b hne hdegree hheight R hn hD hb
  apply (substitutionAccess B count D b hne S A).evaluator
    ⟨(bits_mem_FP hn).comp pairFst_mem_FP,
      ((BinaryFn.const 2).mul A.degree_binary).bits_mem_FP.comp pairFst_mem_FP,
      A.terms_binary.bits_mem_FP.comp pairFst_mem_FP, A.exponent_FP⟩
    A.coefficientEvaluator (E.1.precompose _ coordinateQuery_FP) (E.2.precompose _ coordinateQuery_FP)

/-- Uniform coordinate controls depend only on the original context. -/
def coordinateDegree (c : List Bool) : ℕ :=
  FiniteLeafCoordinateBits.degreeControl count D b (pair c []) ^ (count c).size

def coordinateMass (c : List Bool) : ℕ :=
  (count c).size * coordinateDegree count D b c * FiniteLeafCoordinateBits.massControl count D b (pair c [])

theorem coordinateDegree_binary (hn : UnaryFn count) (hD : BinaryFn D) (hb : BinaryFn b) :
    BinaryFn (coordinateDegree count D b) :=
  by
    have hd : BinaryFn (fun c => FiniteLeafCoordinateBits.degreeControl count D b (pair c [])) :=
      (FiniteLeafCoordinateBits.degreeControl_binary hn hD hb).comp (mem_FP_pair id_mem_FP (constFn_mem_FP []))
    exact hd.powUnary hn.size

theorem coordinateMass_binary (hn : UnaryFn count) (hD : BinaryFn D) (hb : BinaryFn b) :
    BinaryFn (coordinateMass count D b) :=
  ((BinaryFn.of_bits (bits_mem_FP hn.size)).mul (coordinateDegree_binary count D b hn hD hb)).mul
    ((FiniteLeafCoordinateBits.massControl_binary hn hD hb).comp (mem_FP_pair id_mem_FP (constFn_mem_FP [])))

include hdegree hheight in
theorem coordinate_bounds (c : List Bool) (i : ℕ) :
    (numerator B count D b hne (pair c []) i).natDegree ≤ coordinateDegree count D b c ∧
    (denominator B count D b hne (pair c []) i).natDegree ≤ coordinateDegree count D b c ∧
    coefficientMass (numerator B count D b hne (pair c []) i) ≤ 2 ^ coordinateMass count D b c ∧
    coefficientMass (denominator B count D b hne (pair c []) i) ≤ 2 ^ coordinateMass count D b c := by
  have H := FiniteLeafCoordinateBits.coordinate_bounds B count D b hne hdegree hheight (pair c (BinaryNatCode.encode i))
  have hd : FiniteLeafCoordinateBits.degreeControl count D b (pair c (BinaryNatCode.encode i)) =
      FiniteLeafCoordinateBits.degreeControl count D b (pair c []) := by
    simp only [FiniteLeafCoordinateBits.degreeControl, CanonicalPairBits.degreeBudget,
      CanonicalNodeBits.heightBudget, FiniteLeafPathContext.leafContext,
      pairFst_pair, BalancedParameterContext.original_packet]
  have hm : FiniteLeafCoordinateBits.massControl count D b (pair c (BinaryNatCode.encode i)) =
      FiniteLeafCoordinateBits.massControl count D b (pair c []) := by
    simp only [FiniteLeafCoordinateBits.massControl, CanonicalPairBits.massBudget,
      CanonicalNodeBits.heightBudget, FiniteLeafPathContext.leafContext,
      pairFst_pair, BalancedParameterContext.original_packet]
  rw [hd, hm] at H
  simp only [FiniteLeafPathContext.depth, pairFst_pair] at H
  have hn : (FiniteLeafCoordinateBits.coordinate B count D b hne (pair c (BinaryNatCode.encode i))).numerator.natDegree ≤
      coordinateDegree count D b c := (le_max_left _ _).trans H.1
  have hd : (FiniteLeafCoordinateBits.coordinate B count D b hne (pair c (BinaryNatCode.encode i))).denominator.natDegree ≤
      coordinateDegree count D b c := (le_max_right _ _).trans H.1
  simpa only [numerator, denominator, pairFst_pair, coordinateMass, coordinateDegree] using ⟨hn, hd, H.2.1, H.2.2⟩

end LeanCanny.Algebra.FiniteLeafSignBits
