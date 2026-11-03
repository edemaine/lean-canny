/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCoordinatePoweredLocalSpace
public import LeanCanny.Algebra.IntegralCoordinatePullSpace
/-! # Original coefficient-algebra families over external query data -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCoordinateCoefficientBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open scoped Classical
universe u

theorem local_pull_packet (F : Family.{u}) (base modulus entry : List Bool→List Bool)
    (he : ∀c (r t : Fin (count (F.arity c) (F.width c))),
      entry (pair (pair c (modulus c)) (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))=
        residueBits (F.matrix c r t : ZMod (Nat.fromBitsLE (modulus c)+1)))
    (q : List Bool) (r t : Fin (count ((F.pull base).arity q) ((F.pull base).width q))) :
    (entry∘pullPacket base) (pair (pair q (modulus (base q)))
      (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))=
      residueBits ((F.pull base).matrix q r t : ZMod (Nat.fromBitsLE (modulus (base q))+1)) := by
  simp only [Function.comp_apply,pullPacket,PaddedIntegralGeneratorSource.base,PaddedIntegralGeneratorSource.modulus,
    PaddedIntegralGeneratorSource.row,PaddedIntegralGeneratorSource.col,pairFst_pair,pairSnd_pair]
  exact he (base q) r t

theorem powered_pull_evaluator (F : Family.{u}) (base : List Bool→List Bool) (hb : base∈FP)
    (S V : List Bool→ℕ) (target modulus entry : List Bool→List Bool)
    (hA : UnaryFn F.arity) (hB : UnaryFn F.width) (hS : UnaryFn S) (hV : UnaryFn V)
    (ht : target∈FP) (hm : modulus∈FP) (E : SpaceFunction entry)
    (he : ∀c (r t : Fin (count (F.arity c) (F.width c))),
      entry (pair (pair c (modulus c)) (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))=
        residueBits (F.matrix c r t : ZMod (Nat.fromBitsLE (modulus c)+1))) :
    SpaceFunction (FixedWidthRowBits.value (F.pull base).arity V
      ((F.pull base).poweredPolynomial (S∘base)) target (modulus∘base)) := by
  exact powered_evaluator_local (F.pull base) (S∘base) V target (modulus∘base) (entry∘pullPacket base)
    (hS.comp hb) (hA.comp hb) (hB.comp hb) hV ht (mem_FP_comp hb hm)
    (E.precompose _ (pullPacket_FP base hb)) (local_pull_packet F base modulus entry he)

end LeanCanny.Algebra.IntegralCoordinateCoefficientBits
