/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.CompactCoefficientSpace
public import LeanCanny.ETR.CompactCoefficientPadding
public import LeanCanny.ETR.SourceCoefficientSpace

/-! # Coefficient residues of the compactified compiled ETR source

Queries are `pair (pair bits exponentWord) modulusPredecessor`. Blocks have
width `4*N²+1`, where N is the normalized compiled source length. The evaluator
is certified on every binary input. Padding preserves coefficients of the
original-arity `CompactSource.polynomial`, and every nonzero coefficient has
a representable exponent query.
-/

@[expose] public section

namespace LeanCanny.ETR.CompactSourceCoefficient
open Complexity
open LeanCanny.Encoding LeanCanny.Computation
open Algebra.RationalSubstitution.Indexed Algebra.MatrixPower

-- Compose source readers through their proved FP interface.
attribute [local irreducible] RationalSubstitutionBits.compiledTerm

noncomputable def value : List Bool → List Bool :=
  CompactCoefficient.value SourceCoefficient.source SourceCoefficient.target pairSnd

theorem evaluator : SpaceFunction value :=
  CompactCoefficient.evaluator SourceCoefficient.source SourceCoefficient.target pairSnd
    SourceCoefficient.source_mem_FP SourceCoefficient.target_mem_FP pairSnd_mem_FP

def exponentCode (bits : List Bool) (e : ℕ → ℕ) : List Bool :=
  FixedWidthNatVector.encode (CompactSource.size bits) (4 * CompactSource.size bits ^ 2 + 1) e

@[simp] theorem exponentCode_length (bits : List Bool) (e : ℕ → ℕ) :
    (exponentCode bits e).length = CompactSource.size bits * (4 * CompactSource.size bits ^ 2 + 1) :=
  FixedWidthNatVector.length_encode _ _ _

theorem value_packet (bits : List Bool) (e : ℕ → ℕ) (m : ℕ) (hm : 0 < m)
    (he : ∀ i < CompactSource.size bits, e i < 2 ^ (4 * CompactSource.size bits ^ 2 + 1)) :
    value (pair (pair bits (exponentCode bits e)) (BinaryNatCode.encode (m - 1))) =
      residueBits (((Geometry.CubePolynomial.cleared
        (Term.finitePolynomial (CompactSource.size bits) (CompactSource.term bits))).coeff
          (exponentVector (CompactSource.size bits) e) : ℤ) : ZMod m) := by
  let q := pair (pair bits (exponentCode bits e)) (BinaryNatCode.encode (m - 1))
  have hs : SourceCoefficient.source q = RationalSubstitutionBits.compiledTerm bits := by
    simp only [SourceCoefficient.source, Function.comp_apply, q, pairFst_pair]
  have hd : CollectedCoefficient.dimension SourceCoefficient.source q = CompactSource.size bits := by
    rw [CollectedCoefficient.dimension, hs]
    rfl
  have hw : CompactCoefficient.width SourceCoefficient.source q = 4 * CompactSource.size bits ^ 2 + 1 := by
    rw [CompactCoefficient.width, hd]
  have ht : SourceCoefficient.target q = FixedWidthNatVector.encode
      (CollectedCoefficient.dimension SourceCoefficient.source q) (CompactCoefficient.width SourceCoefficient.source q) e := by
    rw [hd, hw]
    simp only [SourceCoefficient.target, q, pairFst_pair, pairSnd_pair, exponentCode]
  have hfit : ∀ i < CollectedCoefficient.dimension SourceCoefficient.source q,
      e i < 2 ^ CompactCoefficient.width SourceCoefficient.source q := by
    rw [hd, hw]
    exact he
  have hc := CompactCoefficient.coefficient_eq_of_encoded_target SourceCoefficient.source SourceCoefficient.target q e ht hfit
  rw [hd, hs] at hc
  change residueBits ((CompactCoefficient.coefficient SourceCoefficient.source SourceCoefficient.target q : ℤ) :
    ZMod (Nat.fromBitsLE (pairSnd q) + 1)) = _
  have hmod : Nat.fromBitsLE (pairSnd q) + 1 = m := by
    simp only [q, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.sub_add_cancel hm]
  have hcast := congrArg (fun n : ℕ => residueBits
    ((CompactCoefficient.coefficient SourceCoefficient.source SourceCoefficient.target q : ℤ) : ZMod n)) hmod
  have hvalue := congrArg (fun z : ℤ => residueBits (z : ZMod m)) hc
  exact hcast.trans hvalue

noncomputable def paddedExponent (bits : List Bool) (e : Fin (CompactSource.term bits).arity →₀ ℕ) (i : ℕ) : ℕ :=
  if hi : i < (CompactSource.term bits).arity then e ⟨i, hi⟩ else 0

theorem value_packet_original (bits : List Bool) (e : Fin (CompactSource.term bits).arity →₀ ℕ)
    (m : ℕ) (hm : 0 < m) (he : ∀ i, e i < 2 ^ (4 * CompactSource.size bits ^ 2 + 1)) :
    value (pair (pair bits (exponentCode bits (paddedExponent bits e))) (BinaryNatCode.encode (m - 1))) =
      residueBits (((CompactSource.polynomial bits).coeff e : ℤ) : ZMod m) := by
  have hn : (CompactSource.term bits).arity ≤ CompactSource.size bits := by
    rw [CompactSource.size_eq]
    exact (CompactSource.term bits).arity_le_dataSize
  rw [value_packet bits _ m hm (by
    intro i _
    unfold paddedExponent
    split_ifs with hi
    · exact he ⟨i, hi⟩
    · exact Nat.two_pow_pos _)]
  rw [Term.coeff_cleared_padding _ _ _ le_rfl hn _ (by
    intro i hi _
    exact dite_eq_right (by omega))]
  have hexp : exponentVector (CompactSource.term bits).arity (paddedExponent bits e) = e := by
    ext i
    simp only [exponentVector, Finsupp.coe_equivFunOnFinite_symm, paddedExponent, i.isLt, dite_true]
  rw [hexp]
  rfl

theorem value_packet_original_of_nonzero (bits : List Bool) (e : Fin (CompactSource.term bits).arity →₀ ℕ)
    (m : ℕ) (hm : 0 < m) (hne : (CompactSource.polynomial bits).coeff e ≠ 0) :
    value (pair (pair bits (exponentCode bits (paddedExponent bits e))) (BinaryNatCode.encode (m - 1))) =
      residueBits (((CompactSource.polynomial bits).coeff e : ℤ) : ZMod m) := by
  apply value_packet_original bits e m hm
  intro i
  have hi := MvPolynomial.monomial_le_degreeOf i (MvPolynomial.mem_support_iff.mpr hne)
  have hd := CompactSource.polynomial_degree bits
  rw [← CompactSource.size_eq bits] at hd
  have h := hi.trans ((MvPolynomial.degreeOf_le_totalDegree _ i).trans hd)
  exact h.trans_lt ((Nat.lt_succ_self _).trans_le (Nat.lt_two_pow_self.le))

end LeanCanny.ETR.CompactSourceCoefficient
