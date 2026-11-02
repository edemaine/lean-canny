/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCoordinatePoweredSpace
public import LeanCanny.Algebra.PaddedIntegralGeneratorSource
/-! # Native canonical coefficient readers survive original query pullback -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCoordinateCoefficientBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open scoped Classical

noncomputable def Family.pull (F : Family) (f : List Bool→List Bool) : Family where
  arity := F.arity∘f
  width := F.width∘f
  carrier := F.carrier∘f
  ring c := F.ring (f c)
  basis c := F.basis (f c)
  element c := F.element (f c)

def pullPacket (f : List Bool→List Bool) (q : List Bool) : List Bool :=
  pair (pair (f (PaddedIntegralGeneratorSource.base q)) (PaddedIntegralGeneratorSource.modulus q))
    (pair (PaddedIntegralGeneratorSource.row q) (PaddedIntegralGeneratorSource.col q))
theorem pullPacket_FP (f : List Bool→List Bool) (hf : f∈FP) : pullPacket f∈FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp PaddedIntegralGeneratorSource.base_FP hf) PaddedIntegralGeneratorSource.modulus_FP)
    (mem_FP_pair PaddedIntegralGeneratorSource.row_FP PaddedIntegralGeneratorSource.col_FP)

theorem pull_packet (F : Family) (f entry : List Bool→List Bool)
    (he : ∀ c mw (i j : Fin (count (F.arity c) (F.width c))),
      entry (pair (pair c mw) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))=
        residueBits ((F.matrix c i j : ℤ) : ZMod (Nat.fromBitsLE mw+1)))
    (c mw : List Bool) (i j : Fin (count ((F.pull f).arity c) ((F.pull f).width c))) :
    (entry∘pullPacket f) (pair (pair c mw) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))=
      residueBits (((F.pull f).matrix c i j : ℤ) : ZMod (Nat.fromBitsLE mw+1)) := by
  simp only [Function.comp_apply,pullPacket,PaddedIntegralGeneratorSource.base,PaddedIntegralGeneratorSource.modulus,
    PaddedIntegralGeneratorSource.row,PaddedIntegralGeneratorSource.col,pairFst_pair,pairSnd_pair]
  exact he (f c) mw i j

theorem pulled_powered_evaluator (F : Family) (f : List Bool→List Bool) (hf : f∈FP)
    (S V : List Bool→ℕ) (target modulus entry : List Bool→List Bool)
    (hS : UnaryFn S) (hA : UnaryFn F.arity) (hB : UnaryFn F.width) (hV : UnaryFn V)
    (ht : target∈FP) (hm : modulus∈FP) (E : SpaceFunction entry)
    (he : ∀ c mw (i j : Fin (count (F.arity c) (F.width c))),
      entry (pair (pair c mw) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))=
        residueBits ((F.matrix c i j : ℤ) : ZMod (Nat.fromBitsLE mw+1))) :
    SpaceFunction (FixedWidthRowBits.value (F.pull f).arity V ((F.pull f).poweredPolynomial S) target modulus) :=
  powered_evaluator (F.pull f) S V target modulus (entry∘pullPacket f) hS (hA.comp hf) (hB.comp hf) hV ht hm
    (E.precompose (pullPacket f) (pullPacket_FP f hf)) (pull_packet F f entry he)

end LeanCanny.Algebra.IntegralCoordinateCoefficientBits
