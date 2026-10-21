/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.TubeProjectionNative
public import LeanCanny.ETR.TubeSource

/-! # Full projection coefficient residues for compiled ETR inputs

Packets contain source, active mask, row, exponent, and modulus-predecessor
fields. Every native row and every nonzero coefficient has a representable
query with polynomially many exponent bits. All field readers are certified FP.
-/

@[expose] public section

namespace LeanCanny.ETR.TubeSourceProjectionCoefficient

open LeanCanny.Encoding LeanCanny.Computation
open Geometry TubeEncoding TubeProjectionEncoding
open Algebra.MatrixPower

attribute [local irreducible] RationalSubstitutionBits.compiledTerm

def input (q : List Bool) : List Bool := pairFst (pairFst (pairFst (pairFst q)))
def active (q : List Bool) : List Bool := pairSnd (pairFst (pairFst (pairFst q)))
def row (q : List Bool) : List Bool := pairSnd (pairFst (pairFst q))
def target (q : List Bool) : List Bool := pairSnd (pairFst q)
def base : List Bool → List Bool := RationalSubstitutionBits.compiledTerm ∘ input

def width (q : List Bool) : ℕ := 8 * CompactSource.size (input q) ^ 2 + 5

theorem input_mem_FP : input ∈ FP := mem_FP_comp (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairFst_mem_FP) pairFst_mem_FP
theorem active_mem_FP : active ∈ FP := mem_FP_comp (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairFst_mem_FP) pairSnd_mem_FP
theorem row_mem_FP : row ∈ FP := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP
theorem target_mem_FP : target ∈ FP := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP

theorem base_mem_FP : base ∈ FP :=
  mem_FP_comp (f := input) (g := RationalSubstitutionBits.compiledTerm) input_mem_FP RationalSubstitutionBits.compiledTerm_mem_FP

theorem width_unary : UnaryFn width :=
  ((UnaryFn.const 8).mul ((CompactSource.size_unary.comp input_mem_FP).pow_const 2)).add (UnaryFn.const 5)

noncomputable def coefficient : List Bool → ℤ := TubeProjection.coefficient base width active row target
noncomputable def value : List Bool → List Bool := TubeProjection.value base width active row target pairSnd

theorem evaluator : SpaceFunction value :=
  TubeProjection.evaluator base width active row target pairSnd base_mem_FP width_unary active_mem_FP row_mem_FP target_mem_FP pairSnd_mem_FP

noncomputable def exponentCode (bits : List Bool) (e : TubeSource.IntegerProjectionVariable bits →₀ ℕ) : List Bool :=
  TubeProjection.exponentCode (CompactSource.term bits).arity (8 * CompactSource.size bits ^ 2 + 5) e

noncomputable def query (bits : List Bool) (s : Finset (Constraint (CompactSource.term bits).arity))
    (j : TubeSource.ProjectionIndex bits) (e : TubeSource.IntegerProjectionVariable bits →₀ ℕ) (m : ℕ) : List Bool :=
  pair (pair (pair (pair bits (activeCode (CompactSource.term bits).arity s))
    (BinaryNatCode.encode (TubeProjectionRow.code (CompactSource.term bits).arity j))) (exponentCode bits e)) (BinaryNatCode.encode (m - 1))

theorem coefficient_query (bits : List Bool) (s : Finset (Constraint (CompactSource.term bits).arity))
    (j : TubeSource.ProjectionIndex bits) (e : TubeSource.IntegerProjectionVariable bits →₀ ℕ) (m : ℕ)
    (he : ∀ i, e i < 2 ^ (8 * CompactSource.size bits ^ 2 + 5)) :
    coefficient (query bits s j e m) = (TubeSource.integerProjection bits s j).coeff e := by
  let q := query bits s j e m
  have hi : input q = bits := by simp only [q, query, input, pairFst_pair]
  have hb : base q = RationalSubstitutionBits.compiledTerm bits := by rw [base, Function.comp_apply, hi]
  have ha : active q = activeCode (CompactSource.term bits).arity s := by
    simp only [q, query, active, pairFst_pair, pairSnd_pair]
  have hr : row q = BinaryNatCode.encode (TubeProjectionRow.code (CompactSource.term bits).arity j) := by
    simp only [q, query, row, pairFst_pair, pairSnd_pair]
  have ht : target q = exponentCode bits e := by simp only [q, query, target, pairFst_pair, pairSnd_pair]
  have hw : width q = 8 * CompactSource.size bits ^ 2 + 5 := by rw [width, hi]
  have hc := TubeProjection.coefficient_eq_native base width active row target q
  unfold TubeDense.polynomial TubeDense.arity TermArity.arity at hc
  rw [hb, hw] at hc
  change ∀ j : TubeSource.ProjectionIndex bits, ∀ e : TubeSource.IntegerProjectionVariable bits →₀ ℕ,
    row q = BinaryNatCode.encode (TubeProjectionRow.code (CompactSource.term bits).arity j) →
    target q = TubeProjection.exponentCode (CompactSource.term bits).arity (8 * CompactSource.size bits ^ 2 + 5) e →
    (∀ i, e i < 2 ^ (8 * CompactSource.size bits ^ 2 + 5)) →
    TubeProjection.coefficient base width active row target q =
      (TubeSource.integerProjection bits (activeSet (CompactSource.term bits).arity (active q)) j).coeff e at hc
  rw [ha, activeSet_activeCode] at hc
  exact hc j e hr ht he

theorem value_query (bits : List Bool) (s : Finset (Constraint (CompactSource.term bits).arity))
    (j : TubeSource.ProjectionIndex bits) (e : TubeSource.IntegerProjectionVariable bits →₀ ℕ) (m : ℕ) (hm : 0 < m)
    (he : ∀ i, e i < 2 ^ (8 * CompactSource.size bits ^ 2 + 5)) :
    value (query bits s j e m) = residueBits (((TubeSource.integerProjection bits s j).coeff e : ℤ) : ZMod m) := by
  let q := query bits s j e m
  have hc := coefficient_query bits s j e m he
  change TubeProjection.coefficient base width active row target q = (TubeSource.integerProjection bits s j).coeff e at hc
  rw [value, TubeProjection.value_eq_coefficient]
  change residueBits ((TubeProjection.coefficient base width active row target q : ℤ) : ZMod (Nat.fromBitsLE (pairSnd q) + 1)) = _
  have hmod : Nat.fromBitsLE (pairSnd q) + 1 = m := by
    simp only [q, query, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.sub_add_cancel hm]
  have hcast := congrArg (fun n : ℕ => residueBits ((TubeProjection.coefficient base width active row target q : ℤ) : ZMod n)) hmod
  have hvalue := congrArg (fun z : ℤ => residueBits (z : ZMod m)) hc
  exact hcast.trans hvalue

theorem value_query_of_nonzero (bits : List Bool) (s : Finset (Constraint (CompactSource.term bits).arity))
    (j : TubeSource.ProjectionIndex bits) (e : TubeSource.IntegerProjectionVariable bits →₀ ℕ) (m : ℕ) (hm : 0 < m)
    (he : (TubeSource.integerProjection bits s j).coeff e ≠ 0) :
    value (query bits s j e m) = residueBits (((TubeSource.integerProjection bits s j).coeff e : ℤ) : ZMod m) := by
  apply value_query bits s j e m hm
  intro i
  have hi := MvPolynomial.monomial_le_degreeOf i (MvPolynomial.mem_support_iff.mpr he)
  have hd := TubeSource.integer_projection_degree_le_code bits s j
  simp only [RadiusSource.degreeCode, BinaryNatCode.encode, Nat.fromBitsLE_bits] at hd
  have h := hi.trans ((MvPolynomial.degreeOf_le_totalDegree _ i).trans hd)
  exact h.trans_lt ((Nat.lt_succ_self _).trans_le (Nat.lt_two_pow_self.le))

theorem exponentCode_length_le (bits : List Bool) (e : TubeSource.IntegerProjectionVariable bits →₀ ℕ) :
    (exponentCode bits e).length ≤ (6 * CompactSource.size bits + 7) * (8 * CompactSource.size bits ^ 2 + 5) := by
  rw [exponentCode, TubeProjection.exponentCode_length]
  apply Nat.mul_le_mul_right
  have h := (CompactSource.term bits).arity_le_dataSize
  rw [← CompactSource.size_eq bits] at h
  unfold TubeProjectionEncoding.dimension pointCount constraintCount
  omega

end LeanCanny.ETR.TubeSourceProjectionCoefficient
