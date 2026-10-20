/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.CollectedCoefficientSpace
public import LeanCanny.ETR.CompactSource
public import LeanCanny.Encoding.FixedWidthNatVector

/-! # Collected coefficient residues of the compiled ETR source

The input is `pair (pair bits exponentWord) modulusPredecessor`. The source
polynomial uses N variables, where N is the normalized compiled term length;
unused coordinates are zero-padded. Each exponent takes N+1 bits, so every
potentially nonzero coefficient has a representable query. The certified
evaluator computes its residue in polynomial space on every binary input.
Compactification coefficient access is supplied by `CompactSourceCoefficient`.
-/

@[expose] public section

namespace LeanCanny.ETR.SourceCoefficient
open Complexity
open LeanCanny.Encoding LeanCanny.Computation
open Algebra.RationalSubstitution.Indexed Algebra.MatrixPower

-- Check FP composition without unfolding the equation compiler.
attribute [local irreducible] RationalSubstitutionBits.compiledTerm

def source : List Bool → List Bool := RationalSubstitutionBits.compiledTerm ∘ (pairFst ∘ pairFst)
def target (q : List Bool) : List Bool := pairSnd (pairFst q)

theorem source_mem_FP : source ∈ FP := by
  exact mem_FP_comp (f := pairFst ∘ pairFst) (g := RationalSubstitutionBits.compiledTerm)
    (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) RationalSubstitutionBits.compiledTerm_mem_FP
theorem target_mem_FP : target ∈ FP := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP

noncomputable def value : List Bool → List Bool := CollectedCoefficient.value source target pairSnd
noncomputable def evaluator : SpaceFunction value := by
  have E := CollectedCoefficient.evaluator source target pairSnd source_mem_FP target_mem_FP pairSnd_mem_FP
  exact E

def exponentCode (bits : List Bool) (e : ℕ → ℕ) : List Bool :=
  FixedWidthNatVector.encode (CompactSource.size bits) (CompactSource.size bits + 1) e

@[simp] theorem exponentCode_length (bits : List Bool) (e : ℕ → ℕ) :
    (exponentCode bits e).length = CompactSource.size bits * (CompactSource.size bits + 1) :=
  FixedWidthNatVector.length_encode _ _ _

theorem exponent_fits_of_degree (bits : List Bool) (e : ℕ → ℕ)
    (he : ∀ i < CompactSource.size bits, e i ≤ (CompactSource.term bits).degreeBound) :
    ∀ i < CompactSource.size bits, e i < 2 ^ (CompactSource.size bits + 1) := by
  intro i hi
  have h := (he i hi).trans (CompactSource.term bits).degreeBound_le_dataSize
  rw [← CompactSource.size_eq bits] at h
  exact h.trans_lt ((Nat.lt_two_pow_self : CompactSource.size bits < 2 ^ CompactSource.size bits).trans_le
    (Nat.pow_le_pow_right (by decide) (by omega)))

theorem value_packet (bits : List Bool) (e : ℕ → ℕ) (m : ℕ) (hm : 0 < m)
    (he : ∀ i < CompactSource.size bits, e i < 2 ^ (CompactSource.size bits + 1)) :
    value (pair (pair bits (exponentCode bits e)) (BinaryNatCode.encode (m - 1))) =
      residueBits (((Term.finitePolynomial (CompactSource.size bits) (CompactSource.term bits)).coeff
        (exponentVector (CompactSource.size bits) e) : ℤ) : ZMod m) := by
  let q := pair (pair bits (exponentCode bits e)) (BinaryNatCode.encode (m - 1))
  have hs : source q = RationalSubstitutionBits.compiledTerm bits := by
    simp only [source, Function.comp_apply, q, pairFst_pair]
  have hd : CollectedCoefficient.dimension source q = CompactSource.size bits := by
    rw [CollectedCoefficient.dimension, hs]
    rfl
  have ht : target q = FixedWidthNatVector.encode
      (CollectedCoefficient.dimension source q) (CollectedCoefficient.dimension source q + 1) e := by
    rw [hd]
    simp only [target, q, pairFst_pair, pairSnd_pair, exponentCode]
  have hfit : ∀ i < CollectedCoefficient.dimension source q, e i < 2 ^ (CollectedCoefficient.dimension source q + 1) := by
    rw [hd]
    exact he
  have hc := CollectedCoefficient.coefficient_eq_of_encoded_target source target q e ht hfit
  rw [hd, hs] at hc
  change residueBits ((CollectedCoefficient.coefficient source target q : ℤ) :
    ZMod (Nat.fromBitsLE (pairSnd q) + 1)) = _
  have hmod : Nat.fromBitsLE (pairSnd q) + 1 = m := by
    simp only [q, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.sub_add_cancel hm]
  have hcast := congrArg (fun n : ℕ => residueBits ((CollectedCoefficient.coefficient source target q : ℤ) : ZMod n)) hmod
  have hvalue := congrArg (fun z : ℤ => residueBits (z : ZMod m)) hc
  exact hcast.trans hvalue

theorem value_packet_of_nonzero (bits : List Bool) (e : ℕ → ℕ) (m : ℕ) (hm : 0 < m)
    (hne : (Term.finitePolynomial (CompactSource.size bits) (CompactSource.term bits)).coeff
      (exponentVector (CompactSource.size bits) e) ≠ 0) :
    value (pair (pair bits (exponentCode bits e)) (BinaryNatCode.encode (m - 1))) =
      residueBits (((Term.finitePolynomial (CompactSource.size bits) (CompactSource.term bits)).coeff
        (exponentVector (CompactSource.size bits) e) : ℤ) : ZMod m) := by
  apply value_packet bits e m hm
  apply exponent_fits_of_degree bits e
  exact Term.exponent_le_of_finitePolynomial_coeff_ne_zero _ _ e hne

end LeanCanny.ETR.SourceCoefficient
