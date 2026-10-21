/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeCoefficientSpace
public import LeanCanny.ETR.TubeSource

/-! # Full tube coefficient residues for compiled ETR inputs

Queries are `pair (pair (pair bits activeMask) exponentWord) modulusPredecessor`.
The exact source arity determines the coordinate layout. Exponent blocks have
width `8*N²+5` for compiled source size N. Every nonzero coefficient has a
representable query. All input fields and coefficient children are certified.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeSourceCoefficient
open Complexity
open LeanCanny.Encoding LeanCanny.Computation
open Geometry TubeEncoding
open Algebra.MatrixPower

attribute [local irreducible] RationalSubstitutionBits.compiledTerm

def input (q : List Bool) : List Bool := pairFst (pairFst (pairFst q))
def active (q : List Bool) : List Bool := pairSnd (pairFst (pairFst q))
def target (q : List Bool) : List Bool := pairSnd (pairFst q)
def base : List Bool → List Bool := RationalSubstitutionBits.compiledTerm ∘ input

def width (q : List Bool) : ℕ := 8 * CompactSource.size (input q) ^ 2 + 5

theorem input_mem_FP : input ∈ FP := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairFst_mem_FP
theorem active_mem_FP : active ∈ FP := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP
theorem target_mem_FP : target ∈ FP := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP

theorem base_mem_FP : base ∈ FP :=
  mem_FP_comp (f := input) (g := RationalSubstitutionBits.compiledTerm) input_mem_FP RationalSubstitutionBits.compiledTerm_mem_FP

theorem width_unary : UnaryFn width :=
  ((UnaryFn.const 8).mul ((CompactSource.size_unary.comp input_mem_FP).pow_const 2)).add (UnaryFn.const 5)

noncomputable def value : List Bool → List Bool := TubeCoefficient.value base width active target pairSnd

theorem evaluator : SpaceFunction value :=
  TubeCoefficient.evaluator base width active target pairSnd base_mem_FP width_unary active_mem_FP target_mem_FP pairSnd_mem_FP

noncomputable def exponentCode (bits : List Bool) (m : Coordinate (CompactSource.term bits).arity →₀ ℕ) : List Bool :=
  FixedWidthNatVector.encode (dimension (CompactSource.term bits).arity) (8 * CompactSource.size bits ^ 2 + 5)
    (TubeZero.paddedExponent (CompactSource.term bits).arity m)

@[simp] theorem exponentCode_length (bits : List Bool) (m : Coordinate (CompactSource.term bits).arity →₀ ℕ) :
    (exponentCode bits m).length = dimension (CompactSource.term bits).arity * (8 * CompactSource.size bits ^ 2 + 5) :=
  FixedWidthNatVector.length_encode _ _ _

noncomputable def query (bits : List Bool) (s : Finset (Constraint (CompactSource.term bits).arity))
    (m : Coordinate (CompactSource.term bits).arity →₀ ℕ) (modulus : ℕ) : List Bool :=
  pair (pair (pair bits (activeCode (CompactSource.term bits).arity s)) (exponentCode bits m)) (BinaryNatCode.encode (modulus - 1))

theorem value_query (bits : List Bool) (s : Finset (Constraint (CompactSource.term bits).arity))
    (e : Coordinate (CompactSource.term bits).arity →₀ ℕ) (m : ℕ) (hm : 0 < m)
    (he : ∀ j, e j < 2 ^ (8 * CompactSource.size bits ^ 2 + 5)) :
    value (query bits s e m) = residueBits (((TubeSource.integerPolynomial bits s).coeff e : ℤ) : ZMod m) := by
  let q := query bits s e m
  have hi : input q = bits := by simp only [q, query, input, pairFst_pair]
  have hb : base q = RationalSubstitutionBits.compiledTerm bits := by rw [base, Function.comp_apply, hi]
  have ha : active q = activeCode (CompactSource.term bits).arity s := by
    simp only [q, query, active, pairFst_pair, pairSnd_pair]
  have ht : target q = exponentCode bits e := by simp only [q, query, target, pairFst_pair, pairSnd_pair]
  have hw : width q = 8 * CompactSource.size bits ^ 2 + 5 := by rw [width, hi]
  have hc := TubeCoefficient.coefficient_eq_native base width active target q
  unfold TubeDense.polynomial TubeDense.arity TermArity.arity at hc
  rw [hb, hw] at hc
  change ∀ f : Coordinate (CompactSource.term bits).arity →₀ ℕ,
    target q = FixedWidthNatVector.encode (dimension (CompactSource.term bits).arity)
      (8 * CompactSource.size bits ^ 2 + 5)
      (TubeZero.paddedExponent (CompactSource.term bits).arity f) →
    (∀ j, f j < 2 ^ (8 * CompactSource.size bits ^ 2 + 5)) →
    TubeCoefficient.coefficient base width active target q =
      (TubeSource.integerPolynomial bits
        (activeSet (CompactSource.term bits).arity (active q))).coeff f at hc
  rw [ha, activeSet_activeCode] at hc
  have hc' := hc e (by rw [ht]; rfl) he
  change TubeCoefficient.coefficient base width active target q = (TubeSource.integerPolynomial bits s).coeff e at hc'
  change residueBits ((TubeCoefficient.coefficient base width active target q : ℤ) : ZMod (Nat.fromBitsLE (pairSnd q) + 1)) = _
  have hmod : Nat.fromBitsLE (pairSnd q) + 1 = m := by
    simp only [q, query, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.sub_add_cancel hm]
  have hcast := congrArg (fun n : ℕ => residueBits ((TubeCoefficient.coefficient base width active target q : ℤ) : ZMod n)) hmod
  have hvalue := congrArg (fun z : ℤ => residueBits (z : ZMod m)) hc'
  exact hcast.trans hvalue

theorem value_query_of_nonzero (bits : List Bool) (s : Finset (Constraint (CompactSource.term bits).arity))
    (e : Coordinate (CompactSource.term bits).arity →₀ ℕ) (m : ℕ) (hm : 0 < m)
    (he : (TubeSource.integerPolynomial bits s).coeff e ≠ 0) :
    value (query bits s e m) = residueBits (((TubeSource.integerPolynomial bits s).coeff e : ℤ) : ZMod m) := by
  apply value_query bits s e m hm
  intro j
  have hj := MvPolynomial.monomial_le_degreeOf j (MvPolynomial.mem_support_iff.mpr he)
  have hd := TubeSource.integer_polynomial_degree_le_code bits s
  simp only [RadiusSource.degreeCode, BinaryNatCode.encode, Nat.fromBitsLE_bits] at hd
  have h := hj.trans ((MvPolynomial.degreeOf_le_totalDegree _ j).trans hd)
  exact h.trans_lt ((Nat.lt_succ_self _).trans_le (Nat.lt_two_pow_self.le))

theorem exponentCode_length_le (bits : List Bool) (e : Coordinate (CompactSource.term bits).arity →₀ ℕ) :
    (exponentCode bits e).length ≤ (3 * CompactSource.size bits + 5) * (8 * CompactSource.size bits ^ 2 + 5) := by
  rw [exponentCode_length]
  apply Nat.mul_le_mul_right
  have h := (CompactSource.term bits).arity_le_dataSize
  rw [← CompactSource.size_eq bits] at h
  unfold dimension constraintCount
  omega

end LeanCanny.ETR.TubeSourceCoefficient
