/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.IntegerPolynomialIndexedSampleTest
public import LeanCanny.Encoding.BoundedAlgebraicSliceSource
public import LeanCanny.Algebra.BivariateReaderCanonical

/-! # Native coefficient signs and degrees at complete algebraic samples

Bivariate integer sources specialize at any complete scalar-root label,
including repeated roots. Extra query records preserve that root. Invalid
labels denote the zero polynomial. All coefficient signs and actual-degree
scans are computed from the original modular readers.
-/

@[expose] public section
namespace LeanCanny.Encoding.IntegerPolynomialSampleSlice
open LeanCanny.Algebra LeanCanny.Computation MatrixPower
open IntegerPolynomialRootQueriesBits (Source)
open BoundedAlgebraicSlice (Family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000

def scalarContext (z : List Bool) : List Bool := pair (pairFst z) (pairFst (pairSnd z))
theorem scalarContext_FP : scalarContext ∈ FP := by polytime [scalarContext]

noncomputable def scalar (F : Family) : Source where
  polynomial z := (F.polynomial (scalarContext z)).coeff (Nat.fromBitsLE (pairSnd (pairSnd z)))
  degree z := F.parameterDegree (scalarContext z)
  mass z := F.mass (scalarContext z)
  degree_bound z := F.coefficient_degree (scalarContext z) _
  mass_bound z := F.coefficient_mass (scalarContext z) _

def scalarQuery (q : List Bool) : List Bool :=
  pair (pair (scalarContext (pairFst (pairFst q))) (pairSnd q))
    (pair (pairSnd (pairFst q)) (pairSnd (pairSnd (pairFst (pairFst q)))))
theorem scalarQuery_FP : scalarQuery ∈ FP := by polytime [scalarQuery, scalarContext]

theorem scalarAccess {F : Family} (A : F.Access) : IntegerPolynomialRootQueriesBits.Access (scalar F) := by
  refine ⟨((BivariateReaderCanonical.evaluator A.reader).precompose scalarQuery scalarQuery_FP).congr (funext fun q => ?_),
    A.parameterDegree_binary.comp scalarContext_FP, A.mass_binary.comp scalarContext_FP⟩
  simp only [Function.comp_apply, scalarQuery, SymbolicFixedTableEntryBits.coefficient,
    PrimitivePairBits.coefficient, RationalSubstitution.IntegerBits.context,
    RationalSubstitution.IntegerBits.selectedDegree, RationalSubstitution.IntegerBits.mValue,
    pairFst_pair, pairSnd_pair, scalar]
  rfl

def context (u : List Bool) : List Bool := pair (pairFst (pairFst u)) (pairSnd u)
theorem context_FP : context ∈ FP := by polytime [context]

noncomputable def valid (S : Source) : Language :=
  {u | SquareSampleCompleteVertices.Valid (IntegerPolynomialSampleInput.input S)
    (pairFst (pairFst u)) (pairSnd (pairFst u))}

theorem validDecider {S : Source} (A : IntegerPolynomialRootQueriesBits.Access S) : SpaceDecider (valid S) :=
  (SquareSampleCompleteVertices.decider (IntegerPolynomialSampleInput.access A)).precompose pairFst pairFst_mem_FP

noncomputable def point (S : Source) (u : List Bool) : ℝ :=
  if hu : u ∈ valid S then (SquareSampleCompleteVertices.candidate (IntegerPolynomialSampleInput.input S)
    (pairFst (pairFst u)) (pairSnd (pairFst u)) hu).val (0 : Fin 1) else 0

noncomputable def specialized (S : Source) (F : Family) (u : List Bool) : Polynomial ℝ :=
  if u ∈ valid S then F.slice (context u) (point S u) else 0

def coefficientQuery (q : List Bool) : List Bool :=
  pair (pair (pairFst (pairFst (pairFst q))) (pairSnd (pairFst (pairFst q))))
  (pair (pairSnd (pairFst q)) (pairSnd q))
theorem coefficientQuery_FP : coefficientQuery ∈ FP := by polytime [coefficientQuery]

noncomputable def rawSign (S : Source) (F : Family) : List Bool → List Bool :=
  IntegerPolynomialIndexedSampleTest.value S (scalar F) ∘ coefficientQuery

theorem rawSignEvaluator {S : Source} (A : IntegerPolynomialRootQueriesBits.Access S)
    {F : Family} (B : F.Access) : SpaceFunction (rawSign S F) :=
  (IntegerPolynomialIndexedSampleTest.evaluator A (scalarAccess B)).precompose coefficientQuery coefficientQuery_FP

noncomputable def coefficientSign (S : Source) (F : Family) (q : List Bool) : List Bool :=
  if pairFst q ∈ valid S then rawSign S F q else []

theorem coefficientSignEvaluator {S : Source} (A : IntegerPolynomialRootQueriesBits.Access S)
    {F : Family} (B : F.Access) : SpaceFunction (coefficientSign S F) :=
  SpaceFunction.branchDecider ((validDecider A).precompose pairFst pairFst_mem_FP)
    (rawSignEvaluator A B) (SpaceFunction.ofFP _ (constFn_mem_FP []))

theorem coefficientSign_packet (S : Source) (F : Family) (u : List Bool) (k : ℕ) :
    coefficientSign S F (pair u (BinaryNatCode.encode k)) =
      InfinitesimalSign.encode (SignType.sign ((specialized S F u).coeff k)) := by
  by_cases hu : u ∈ valid S
  · have H := IntegerPolynomialIndexedSampleTest.packet S (scalar F)
      (pairFst (pairFst u)) (pairSnd (pairFst u)) (pair (pairSnd u) (BinaryNatCode.encode k)) hu
    have hq : coefficientQuery (pair u (BinaryNatCode.encode k)) =
        pair (pair (pairFst (pairFst u)) (pairSnd (pairFst u))) (pair (pairSnd u) (BinaryNatCode.encode k)) := by
      simp only [coefficientQuery, pairFst_pair, pairSnd_pair]
    rw [coefficientSign, pairFst_pair, ite_eq_left hu, rawSign, Function.comp_apply, hq, H]
    simp only [scalar, scalarContext, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
      specialized, ite_eq_left hu, BoundedAlgebraicSlice.Family.slice, Polynomial.coeff_map,
      ParameterTarski.evalHom, Polynomial.coe_eval₂RingHom, context, point, dite_eq_left hu]
  · simp only [coefficientSign, pairFst_pair, hu, ite_false, specialized, Polynomial.coeff_zero, sign_zero, InfinitesimalSign.encode]

theorem specialized_degree (S : Source) (F : Family) (u : List Bool) :
    (specialized S F u).natDegree ≤ F.degree (context u) := by
  unfold specialized Family.slice
  split_ifs
  · exact Polynomial.natDegree_map_le.trans (F.polynomial_degree _)
  · simp only [Polynomial.natDegree_zero, Nat.zero_le]

theorem coefficient_zero (S : Source) (F : Family) (u : List Bool) (k : ℕ) :
    coefficientSign S F (pair u (BinaryNatCode.encode k)) = [] ↔ (specialized S F u).coeff k = 0 := by
  rw [coefficientSign_packet]
  have he (s : SignType) : InfinitesimalSign.encode s = [] ↔ s = 0 := by cases s <;> decide
  rw [he, sign_eq_zero_iff]

theorem degreeEvaluator {S : Source} (A : IntegerPolynomialRootQueriesBits.Access S)
    {F : Family} (B : F.Access) : SpaceFunction (fun u => BinaryNatCode.encode (specialized S F u).natDegree) := by
  have hD : BinaryFn (fun u => F.degree (context u)) := B.degree_binary.comp context_FP
  exact PolynomialDegreeBits.degreeEvaluator (coefficientSignEvaluator A B)
    (fun u => BinaryNatCode.encode (F.degree (context u))) hD.bits_mem_FP (specialized S F)
    (by intro u; rw [BinaryNatCode.encode, Nat.fromBitsLE_bits]; exact specialized_degree S F u)
    (coefficient_zero S F)

end LeanCanny.Encoding.IntegerPolynomialSampleSlice
