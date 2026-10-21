/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ModularPowFP
public import LeanCanny.Computation.SpaceFunctionBranch
public import Mathlib.Algebra.Polynomial.Derivative

/-! # Streamed derivative coefficients from original coefficient residues

The index remains binary. A single space-bounded source call reads coefficient
k+1, and FP modular multiplication supplies the derivative's factor k+1.
No derivative polynomial or unreduced coefficient is stored.
-/

@[expose] public section

namespace LeanCanny.Algebra.DerivativeBits
open Complexity Polynomial
open LeanCanny.Encoding
open LeanCanny.Computation
open MatrixPower

def query (q : List Bool) : List Bool := pair (pairFst q) (BinaryNat.succ (pairSnd q))
def finish (modulus : List Bool → List Bool) (z : List Bool) : List Bool :=
  BinaryNat.mulMod (pair (modulus (pairFst (pairFst z)))
    (pair (pairSnd z) (BinaryNat.succ (pairSnd (pairFst z)))))
def value (modulus coefficient : List Bool → List Bool) (q : List Bool) : List Bool :=
  finish modulus (pair q (coefficient (query q)))

theorem query_mem_FP : query ∈ FP := by
  have h := mem_FP_pair pairFst_mem_FP (mem_FP_comp pairSnd_mem_FP BinaryNat.succ_mem_FP)
  refine mem_FP_of_eq (g := query) h ?_
  intro q
  simp only [query, Function.comp_apply]

theorem finish_mem_FP {modulus : List Bool → List Bool} (hm : modulus ∈ FP) :
    finish modulus ∈ FP := by
  have hmod := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) hm
  have hi := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) BinaryNat.succ_mem_FP
  have h := mem_FP_comp (mem_FP_pair hmod (mem_FP_pair pairSnd_mem_FP hi)) BinaryNat.mulMod_mem_FP
  refine mem_FP_of_eq (g := finish modulus) h ?_
  intro z
  simp only [finish, Function.comp_apply]

theorem evaluator {coefficient : List Bool → List Bool} (P : SpaceFunction coefficient)
    (modulus : List Bool → List Bool) (hm : modulus ∈ FP) :
    SpaceFunction (value modulus coefficient) := by
  let E := ((P.precompose query query_mem_FP).withInput).postcompose (finish modulus) (finish_mem_FP hm)
  refine E.congr (funext fun q => ?_)
  simp only [value, Function.comp_apply]

theorem packet (modulus coefficient : List Bool → List Bool) (c : List Bool) (m : ℕ)
    (p : (ZMod m)[X]) (hm : modulus c = BinaryNatCode.encode m)
    (hp : ∀ k, coefficient (pair c (BinaryNatCode.encode k)) = residueBits (p.coeff k)) (k : ℕ) :
    value modulus coefficient (pair c (BinaryNatCode.encode k)) = residueBits (p.derivative.coeff k) := by
  have hs : BinaryNat.succ (BinaryNatCode.encode k) = BinaryNatCode.encode (k + 1) := by
    simp only [BinaryNat.succ_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have hder : p.derivative.coeff k = p.coeff (k + 1) * ((k + 1 : ℕ) : ZMod m) := by
    simpa only [Nat.cast_add, Nat.cast_one] using coeff_derivative p k
  rw [value, query, pairFst_pair, pairSnd_pair, hs, hp]
  simp only [finish, pairFst_pair, pairSnd_pair, hs, hm, hder]
  simp only [BinaryNat.mulMod_pair, residueBits, ZMod.val_mul, ZMod.val_natCast,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]
  congr 1
  simp only [Nat.mul_mod, Nat.mod_mod]

end LeanCanny.Algebra.DerivativeBits
