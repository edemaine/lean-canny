/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CertifiedPolynomial
public import LeanCanny.Algebra.ModularPowFP

/-! # Native summands for bivariate coefficient convolution

The original context and modulus are retained while two independent binary
indices select the outer and parameter convolution terms. All source indices
are normalized before invoking an original certified reader.
-/

@[expose] public section
namespace LeanCanny.Algebra.CertifiedPolynomial.BivariateProduct
open Polynomial LeanCanny.Encoding LeanCanny.Computation MatrixPower

def origin (z : List Bool) : List Bool := pairFst (pairFst z)
def modulus (z : List Bool) : ℕ := Nat.fromBitsLE (pairSnd (pairFst z)) + 1
def inner (z : List Bool) : ℕ := Nat.fromBitsLE (pairFst (pairSnd z))
def outer (z : List Bool) : ℕ := Nat.fromBitsLE (pairSnd (pairSnd z))
def modulusCode (z : List Bool) : List Bool := BinaryNat.succ (pairSnd (pairFst z))
theorem modulusCode_FP : modulusCode ∈ FP := by polytime [modulusCode]
theorem modulusCode_eq (z : List Bool) : modulusCode z = BinaryNatCode.encode (modulus z) :=
  BinaryNat.succ_eq_bits _

def request (r : List Bool) : List Bool := pairFst (pairFst r)
def outerIndex (r : List Bool) : List Bool := pairSnd (pairFst r)
def innerIndex (r : List Bool) : List Bool := pairSnd r
theorem request_FP : request ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP

def leftQuery (r : List Bool) : List Bool := pair (pairFst (request r))
  (pair (BinaryNat.normalize (innerIndex r)) (BinaryNat.normalize (outerIndex r)))
def rightQuery (r : List Bool) : List Bool := pair (pairFst (request r))
  (pair (BinaryNat.sub (pair (pairFst (pairSnd (request r))) (innerIndex r)))
    (BinaryNat.sub (pair (pairSnd (pairSnd (request r))) (outerIndex r))))
theorem leftQuery_FP : leftQuery ∈ FP := by polytime [leftQuery, request, outerIndex, innerIndex]
theorem rightQuery_FP : rightQuery ∈ FP := by polytime [rightQuery, request, outerIndex, innerIndex]

def finish (t : List Bool) : List Bool :=
  BinaryNat.mulMod (pair (modulusCode (request (pairFst t))) (pairSnd t))
theorem finish_FP : finish ∈ FP := by
  have hm := mem_FP_comp (mem_FP_comp pairFst_mem_FP request_FP) modulusCode_FP
  have H := mem_FP_comp (mem_FP_pair hm pairSnd_mem_FP) BinaryNat.mulMod_mem_FP
  exact mem_FP_of_eq H (fun t => by simp only [finish, Function.comp_apply])

def term {p q : List Bool → (ℤ[X])[X]} (A : BivariateReader p) (B : BivariateReader q) (r : List Bool) : List Bool :=
  finish (pair r (pair (A.coefficient (leftQuery r)) (B.coefficient (rightQuery r))))

theorem term_evaluator {p q : List Bool → (ℤ[X])[X]} (A : BivariateReader p) (B : BivariateReader q) :
    SpaceFunction (term A B) :=
  (((A.evaluator.precompose leftQuery leftQuery_FP).pairOutputs
    (B.evaluator.precompose rightQuery rightQuery_FP)).withInput.postcompose finish finish_FP).congr
      (funext fun r => by simp only [term, Function.comp_apply])

noncomputable def summand (p q : List Bool → (ℤ[X])[X]) (z : List Bool) (k l : ℕ) : ZMod (modulus z) :=
  ((((p (origin z)).coeff k).coeff l : ℤ) : ZMod (modulus z)) *
    ((((q (origin z)).coeff (outer z - k)).coeff (inner z - l) : ℤ) : ZMod (modulus z))
noncomputable def termCode (p q : List Bool → (ℤ[X])[X]) (z : List Bool) (k l : ℕ) : List Bool :=
  residueBits (summand p q z k l)

theorem term_eq {p q : List Bool → (ℤ[X])[X]} (A : BivariateReader p) (B : BivariateReader q) (r : List Bool) :
    term A B r = termCode p q (request r) (Nat.fromBitsLE (outerIndex r)) (Nat.fromBitsLE (innerIndex r)) := by
  have hl : A.coefficient (leftQuery r) = residueBits
      ((((p (origin (request r))).coeff (Nat.fromBitsLE (outerIndex r))).coeff (Nat.fromBitsLE (innerIndex r)) : ℤ) :
        ZMod (modulus (request r))) := by
    simp only [leftQuery, BinaryNat.normalize_eq_bits]
    exact A.coefficient_eq (pairFst (request r)) _ _
  have hr : B.coefficient (rightQuery r) = residueBits
      ((((q (origin (request r))).coeff (outer (request r) - Nat.fromBitsLE (outerIndex r))).coeff
        (inner (request r) - Nat.fromBitsLE (innerIndex r)) : ℤ) : ZMod (modulus (request r))) := by
    simp only [rightQuery, BinaryNat.sub_pair]
    exact B.coefficient_eq (pairFst (request r)) _ _
  rw [term]
  simp only [finish, pairFst_pair, pairSnd_pair, modulusCode_eq]
  rw [hl, hr, ArithmeticBits.mulMod_residueBits]
  rfl

end LeanCanny.Algebra.CertifiedPolynomial.BivariateProduct
