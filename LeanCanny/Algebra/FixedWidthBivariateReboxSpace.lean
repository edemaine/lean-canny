/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.FixedWidthRowReboxSpace
/-! # One bivariate source supports a new common coefficient box

Every coefficient request still uses the original certified reader. Large
new exponent blocks are rejected before they can truncate into the old box.
-/
@[expose] public section
namespace LeanCanny.Algebra.FixedWidthBivariateReboxBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open scoped Classical

variable (A U V : List Bool→ℕ)
variable (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (A c)) ℤ))

theorem row_evaluator
    (R : CertifiedPolynomial.BivariateReader (FixedWidthBivariateReader.polynomial A U p))
    (hA : UnaryFn A) (hU : UnaryFn U) (hfit : ∀ c y,((p c).coeff y).totalDegree<2^U c)
    (read : List Bool→List Bool) (hr : read∈FP) (y : List Bool→ℕ) (hy : BinaryFn y)
    (hV : UnaryFn V) (target modulus : List Bool→List Bool) (ht : target∈FP) (hm : modulus∈FP) :
    SpaceFunction (FixedWidthRowBits.value (A ∘ read) V (fun c=>(p (read c)).coeff (y c)) target modulus) :=by
  have HA:=hA.comp hr
  have HU:=hU.comp hr
  have HT:=FixedWidthQuery.repack_mem_FP HA hV HA HU ht
  have EO:=FixedWidthBivariateRowBits.evaluator A U p R hA hU hfit read hr y hy
    (FixedWidthQuery.repack (A ∘ read) V (A ∘ read) (U ∘ read) target) modulus HT hm
  exact FixedWidthRowReboxBits.evaluator (A ∘ read) (U ∘ read) V target
    (fun c=>(p (read c)).coeff (y c)) modulus HA HU hV ht (fun c=>hfit (read c) (y c)) EO

def target (z : List Bool) :=pairFst (pairSnd z)
def modulus (z : List Bool) :=pairSnd (pairFst z)
def outer (z : List Bool) :=Nat.fromBitsLE (pairSnd (pairSnd z))

noncomputable def coefficient : List Bool→List Bool :=
  FixedWidthRowBits.value (A ∘ FixedWidthBivariateReader.origin) (V ∘ FixedWidthBivariateReader.origin)
    (fun z=>(p (FixedWidthBivariateReader.origin z)).coeff (outer z)) target modulus

theorem coefficient_evaluator
    (R : CertifiedPolynomial.BivariateReader (FixedWidthBivariateReader.polynomial A U p))
    (hA : UnaryFn A) (hU : UnaryFn U) (hV : UnaryFn V)
    (hfit : ∀ c y,((p c).coeff y).totalDegree<2^U c) :
    SpaceFunction (coefficient A V p) :=
  row_evaluator A U (V ∘ FixedWidthBivariateReader.origin) p R hA hU hfit
    FixedWidthBivariateReader.origin FixedWidthBivariateReader.origin_FP outer
    (BinaryFn.fromBits (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP))
    (hV.comp FixedWidthBivariateReader.origin_FP) target modulus
    (by polytime [target]) (by polytime [modulus])

private noncomputable def entryAt (A V : List Bool→ℕ)
    (p : (c : List Bool)→Polynomial (MvPolynomial (Fin (A c)) ℤ)) (c : List Bool) (y u : ℕ) (mw : List Bool) :=
  residueBits (((((p c).coeff y).coeff (nativeExponent (Equiv.refl _) (V c) u)) : ℤ) :
    ZMod (Nat.fromBitsLE mw+1))

private theorem coefficient_entry (z : List Bool) :
    coefficient A V p z=entryAt A V p (FixedWidthBivariateReader.origin z)
      (outer z) (Nat.fromBitsLE (target z)) (modulus z) :=rfl

private theorem entryAt_value (c : List Bool) (y u : ℕ) (mw : List Bool) :
    entryAt A V p c y u mw=residueBits (((((p c).coeff y).coeff
      (nativeExponent (Equiv.refl _) (V c) u)) : ℤ) : ZMod (Nat.fromBitsLE mw+1)) :=rfl

attribute [local irreducible] entryAt

theorem coefficient_packet (q : List Bool) (u v : ℕ) :
    coefficient A V p (pair q (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v)))=
      residueBits (((((p (pairFst q)).coeff v).coeff
        (nativeExponent (Equiv.refl _) (V (pairFst q)) u)) : ℤ) : ZMod (Nat.fromBitsLE (pairSnd q)+1)) :=by
  rw [coefficient_entry A V p,←entryAt_value A V p]
  simp only [FixedWidthBivariateReader.origin,outer,target,modulus,pairFst_pair,pairSnd_pair,
    BinaryNatCode.encode,Nat.fromBitsLE_bits]

noncomputable def reader
    (R : CertifiedPolynomial.BivariateReader (FixedWidthBivariateReader.polynomial A U p))
    (hA : UnaryFn A) (hU : UnaryFn U) (hV : UnaryFn V)
    (hold : ∀ c y,((p c).coeff y).totalDegree<2^U c) (D : List Bool→ℕ)
    (hdegree : ∀ c y,((p c).coeff y).totalDegree≤D c) (hfit : ∀ c,D c<2^V c) :
    CertifiedPolynomial.BivariateReader (FixedWidthBivariateReader.polynomial A V p) :=
  FixedWidthBivariateReader.reader A V p (coefficient A V p)
    (coefficient_evaluator A U V p R hA hU hV hold) hA hV D hdegree hfit
    (coefficient_packet A V p)

end LeanCanny.Algebra.FixedWidthBivariateReboxBits
