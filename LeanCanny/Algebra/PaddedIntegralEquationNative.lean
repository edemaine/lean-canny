/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PaddedIntegralEquationSource

/-! # Native lower-equation coefficients from creating companion queries

One original-source companion request and modular negation read a lower
coefficient. The request retains the original source and caller modulus;
its two basis ranks are computed in binary from native dimensions.
-/

@[expose] public section
namespace LeanCanny.Algebra.PaddedIntegralEquationBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralCoordinateBasis FixedWidthPolynomial PaddedIntegralParameterExtension
open PaddedIntegralGeneratorSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ArithmeticBits.negate

def oldRank (S : Source) (q : List Bool) : ℕ := count (S.arity (base q)) (S.width (base q))
def scalarDegree (S : Source) (q : List Bool) : ℕ := 2 ^ S.width (base q)
def basisRank (S : Source) (q : List Bool) : ℕ := Nat.fromBitsLE (col q) % oldRank S q
def power (S : Source) (q : List Bool) : ℕ := Nat.fromBitsLE (row q) % scalarDegree S q

def query (S : Source) (q : List Bool) : List Bool :=
  pair (pair (base q) (modulus q))
    (pair (BinaryNatCode.encode (basisRank S q * scalarDegree S q + power S q))
      (BinaryNatCode.encode (scalarDegree S q - 1)))

theorem oldRank_binary (S : Source) (ha : UnaryFn S.arity) (hw : UnaryFn S.width) :
    BinaryFn (oldRank S) := by
  apply BinaryFn.of_bits
  exact mem_FP_of_eq (countCode_mem_FP (ha.comp base_FP) (hw.comp base_FP))
    (fun q => countCode_code _ _ q)

theorem scalarDegree_binary (S : Source) (hw : UnaryFn S.width) : BinaryFn (scalarDegree S) :=
  (BinaryFn.const 2).powUnary (hw.comp base_FP)

theorem query_FP (S : Source) (ha : UnaryFn S.arity) (hw : UnaryFn S.width) : query S ∈ FP := by
  have HR := (BinaryFn.fromBits col_FP).mod (oldRank_binary S ha hw)
  have HD := scalarDegree_binary S hw
  have HI := (BinaryFn.fromBits row_FP).mod HD
  exact mem_FP_pair (mem_FP_pair base_FP modulus_FP)
    (mem_FP_pair ((HR.mul HD).add HI).bits_mem_FP (HD.sub (BinaryFn.const 1)).bits_mem_FP)

def finish (z : List Bool) : List Bool :=
  ArithmeticBits.negate (pair (BinaryNatCode.encode (Nat.fromBitsLE (modulus (pairFst z)) + 1)) (pairSnd z))

theorem finish_FP : finish ∈ FP := by
  have HM0 : BinaryFn (fun z => Nat.fromBitsLE (modulus (pairFst z))) :=
    (BinaryFn.fromBits modulus_FP).comp pairFst_mem_FP
  have HM := HM0.add (BinaryFn.const 1)
  exact mem_FP_comp (mem_FP_pair HM.bits_mem_FP pairSnd_mem_FP) ArithmeticBits.negate_mem_FP

noncomputable def lowerCoefficient (S : Source) (q : List Bool) : ℤ :=
  ((S.equation (base q)).coeff (power S q)).coeff
    (vector (S.arity (base q)) (S.width (base q))
      ⟨basisRank S q, Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩)

noncomputable def value (S : Source) (q : List Bool) : List Bool :=
  residueBits (lowerCoefficient S q : ZMod (Nat.fromBitsLE (modulus q) + 1))

attribute [local irreducible] Source.matrix

theorem query_value (S : Source) (q : List Bool) :
    PaddedIntegralGeneratorSource.value S (query S q) =
      residueBits ((-lowerCoefficient S q : ℤ) : ZMod (Nat.fromBitsLE (modulus q) + 1)) := by
  let r : Fin (count (S.arity (base q)) (S.width (base q))) :=
    ⟨basisRank S q, Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩
  let i : Fin (2 ^ S.width (base q)) := ⟨power S q, Nat.mod_lt _ (Nat.two_pow_pos _)⟩
  have HQ : query S q = pair (pair (base q) (modulus q))
      (pair (BinaryNatCode.encode (pairIndex (S.arity (base q)) (S.width (base q)) (r, i)).val)
        (BinaryNatCode.encode (pairIndex (S.arity (base q)) (S.width (base q))
          (zeroFin (S.arity (base q)) (S.width (base q)), lastDigit (S.width (base q)))).val)) := by
    simp only [query, pairIndex_value, r, i, zeroFin, lastDigit, scalarDegree,
      Nat.zero_mul, Nat.zero_add, Nat.add_comm, Nat.mul_comm]
  rw [HQ, value_packet]
  have HE := S.equation_lower (base q) r i
  change lowerCoefficient S q = -_ at HE
  rw [HE, neg_neg]

theorem finish_value (S : Source) (q : List Bool) :
    finish (pair q (PaddedIntegralGeneratorSource.value S (query S q))) = value S q := by
  let : NeZero (Nat.fromBitsLE (modulus q) + 1) := ⟨by omega⟩
  rw [query_value]
  simp only [finish, pairFst_pair, pairSnd_pair, ArithmeticBits.negate_residueBits, value,
    Int.cast_neg, neg_neg]

theorem evaluator (S : Source) (ha : UnaryFn S.arity) (hw : UnaryFn S.width)
    (E : SpaceFunction (PaddedIntegralGeneratorSource.value S)) : SpaceFunction (value S) := by
  have H := ((E.precompose (query S) (query_FP S ha hw)).withInput).postcompose finish finish_FP
  exact H.congr (funext (finish_value S))


end LeanCanny.Algebra.PaddedIntegralEquationBits
