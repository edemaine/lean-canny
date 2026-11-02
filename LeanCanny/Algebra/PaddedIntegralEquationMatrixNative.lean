/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.PaddedIntegralEquationMatrix
public import LeanCanny.Algebra.PaddedIntegralEquationNative

/-! # Native lower-equation multiplication matrices

Each coefficient-matrix request becomes one creating-companion entry and
modular negation. Source words, coefficient indices and caller moduli remain
in the original query. All matrix entry costs stay charged to that companion.
-/

@[expose] public section
namespace LeanCanny.Algebra.PaddedIntegralEquationMatrixBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralCoordinateBasis FixedWidthPolynomial PaddedIntegralParameterExtension
open PaddedIntegralGeneratorSource
open scoped Classical
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] Source.matrix IntegralCoordinateCoefficientBits.Family.matrix
  PaddedIntegralEquationBits.finish ArithmeticBits.negate

def rank (S : Source) (q : List Bool) := count (S.arity (pairFst (base q))) (S.width (pairFst (base q)))
def degree (S : Source) (q : List Bool) := 2^S.width (pairFst (base q))
def lowerPower (S : Source) (q : List Bool) := Nat.fromBitsLE (pairSnd (base q)) % degree S q

def oldIndex (S : Source) (reader : List Bool → List Bool) (q : List Bool) : Fin (rank S q) :=
  ⟨Nat.fromBitsLE (reader q) % rank S q,Nat.mod_lt _ (pow_pos (Nat.two_pow_pos _) _)⟩

def query (S : Source) (q : List Bool) : List Bool :=
  pair (pair (pairFst (base q)) (modulus q))
    (pair (BinaryNatCode.encode ((oldIndex S row q).val*degree S q+lowerPower S q))
      (BinaryNatCode.encode ((oldIndex S col q).val*degree S q+(degree S q-1))))

theorem query_FP (S : Source) (ha : UnaryFn S.arity) (hw : UnaryFn S.width) : query S∈FP := by
  have HC : (fun q => pairFst (base q))∈FP := mem_FP_comp base_FP pairFst_mem_FP
  have HR : BinaryFn (rank S) := by
    apply BinaryFn.of_bits
    exact mem_FP_of_eq (countCode_mem_FP (ha.comp HC) (hw.comp HC)) (fun q => countCode_code _ _ q)
  have HD : BinaryFn (degree S) := (BinaryFn.const 2).powUnary (hw.comp HC)
  have HK := (BinaryFn.fromBits (mem_FP_comp base_FP pairSnd_mem_FP)).mod HD
  have HI := (BinaryFn.fromBits row_FP).mod HR
  have HJ := (BinaryFn.fromBits col_FP).mod HR
  exact mem_FP_pair (mem_FP_pair HC modulus_FP)
    (mem_FP_pair ((HI.mul HD).add HK).bits_mem_FP ((HJ.mul HD).add (HD.sub (BinaryFn.const 1))).bits_mem_FP)

noncomputable def entry (S : Source) (q : List Bool) : List Bool :=
  residueBits (((family S).matrix (base q) (oldIndex S row q) (oldIndex S col q) : ℤ) :
    ZMod (Nat.fromBitsLE (modulus q)+1))

theorem query_value (S : Source) (q : List Bool) :
    PaddedIntegralGeneratorSource.value S (query S q) =
      residueBits ((-(family S).matrix (base q) (oldIndex S row q) (oldIndex S col q) : ℤ) :
        ZMod (Nat.fromBitsLE (modulus q)+1)) := by
  have HQ : query S q = pair (pair (pairFst (base q)) (modulus q))
      (pair (BinaryNatCode.encode (pairIndex (S.arity (pairFst (base q))) (S.width (pairFst (base q)))
        (oldIndex S row q,power S (base q))).val)
      (BinaryNatCode.encode (pairIndex (S.arity (pairFst (base q))) (S.width (pairFst (base q)))
        (oldIndex S col q,lastDigit (S.width (pairFst (base q))))).val)) := by
    simp only [query,pairIndex_value,power,degree,lowerPower,lastDigit,Nat.add_comm,Nat.mul_comm]
  rw [HQ,PaddedIntegralGeneratorSource.value_packet]
  have HE := matrix_eq S (base q) (oldIndex S row q) (oldIndex S col q)
  rw [HE,neg_neg]

theorem finish_value (S : Source) (q : List Bool) :
    PaddedIntegralEquationBits.finish (pair q (PaddedIntegralGeneratorSource.value S (query S q))) = entry S q := by
  rw [query_value]
  let : NeZero (Nat.fromBitsLE (modulus q)+1) := ⟨by omega⟩
  simp only [PaddedIntegralEquationBits.finish,pairFst_pair,pairSnd_pair,
    ArithmeticBits.negate_residueBits,entry,Int.cast_neg,neg_neg]

theorem evaluator (S : Source) (ha : UnaryFn S.arity) (hw : UnaryFn S.width)
    (E : SpaceFunction (PaddedIntegralGeneratorSource.value S)) : SpaceFunction (entry S) := by
  have H := ((E.precompose (query S) (query_FP S ha hw)).withInput).postcompose
    PaddedIntegralEquationBits.finish PaddedIntegralEquationBits.finish_FP
  exact H.congr (funext (finish_value S))

end LeanCanny.Algebra.PaddedIntegralEquationMatrixBits
