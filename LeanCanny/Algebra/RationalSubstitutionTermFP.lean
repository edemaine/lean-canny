/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.RationalMonomialSpace
public import LeanCanny.Encoding.BinaryPowModFP

/-!
# FP preparation and scalar finishing for substitution terms

The monomial context pairs the source context with a term index. Index
normalization and out-of-range masking make every callback total, without
requiring a semantic source contract outside the term family. Coordinate
queries drop the term field; exponent queries retain it. FP modular
multiplication combines one source coefficient with one monomial coefficient.
-/

@[expose] public section

namespace LeanCanny.Algebra.RationalSubstitution.TermBits
open Complexity
open LeanCanny.Encoding
open LeanCanny.Computation
open MatrixPower

def sourceQuery (p : List Bool) : List Bool := pair (pairFst (pairFst p)) (pairSnd p)
def exponentQuery (p : List Bool) : List Bool :=
  pair (pairFst (pairFst p)) (pair (BinaryNat.normalize (pairSnd (pairFst p))) (pairSnd p))
def coefficientQuery (q : List Bool) : List Bool := pair (pairFst q) (BinaryNat.normalize (pairSnd q))
def valid (terms : List Bool → List Bool) (q : List Bool) : Bool :=
  decide (Nat.fromBitsLE (pairSnd q) < Nat.fromBitsLE (terms (pairFst q)))
def safeExponent (terms exponent : List Bool → List Bool) (p : List Bool) : List Bool :=
  if valid terms (pairFst p) then exponent (exponentQuery p) else []
def coefficientValue (terms coefficient : List Bool → List Bool) (q : List Bool) : List Bool :=
  if valid terms q then coefficient (coefficientQuery q) else []

theorem sourceQuery_mem_FP : sourceQuery ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairSnd_mem_FP

theorem exponentQuery_mem_FP : exponentQuery ∈ FP := by
  have hc := mem_FP_comp pairFst_mem_FP pairFst_mem_FP
  have hr := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) BinaryNat.normalize_mem_FP
  have h := mem_FP_pair hc (mem_FP_pair hr pairSnd_mem_FP)
  refine mem_FP_of_eq (g := exponentQuery) h ?_
  intro p
  simp only [Function.comp_apply, exponentQuery]

theorem coefficientQuery_mem_FP : coefficientQuery ∈ FP := by
  have hr := mem_FP_comp pairSnd_mem_FP BinaryNat.normalize_mem_FP
  have h := mem_FP_pair pairFst_mem_FP hr
  exact mem_FP_of_eq h (fun _ => rfl)

theorem valid_mem_FP {terms : List Bool → List Bool} (ht : terms ∈ FP) : (fun q => [valid terms q]) ∈ FP :=
  (BinaryNat.lt_fppred pairSnd_mem_FP (mem_FP_comp pairFst_mem_FP ht)).flag_mem_FP

theorem safeExponent_mem_FP {terms exponent : List Bool → List Bool} (ht : terms ∈ FP) (he : exponent ∈ FP) :
    safeExponent terms exponent ∈ FP := by
  have hp := (FPPred.of_flag (valid_mem_FP ht)).comp pairFst_mem_FP
  have h := hp.ite_mem_FP (mem_FP_comp exponentQuery_mem_FP he) (constFn_mem_FP [])
  exact mem_FP_of_eq h (fun _ => rfl)

noncomputable def coefficientEvaluator {f : List Bool → List Bool} (E : SpaceFunction f)
    (terms : List Bool → List Bool) (ht : terms ∈ FP) : SpaceFunction (coefficientValue terms f) := by
  let Q := SpaceFunction.branch (valid terms) (valid_mem_FP ht)
    (E.precompose coefficientQuery coefficientQuery_mem_FP) (SpaceFunction.ofFP (fun _ => []) (constFn_mem_FP []))
  refine Q.congr (funext fun q => ?_)
  simp only [coefficientValue, Function.comp_apply]

theorem normalize_code (b : List Bool) : BinaryNat.normalize b = BinaryNatCode.encode (Nat.fromBitsLE b) :=
  BinaryNat.normalize_eq_bits b

theorem coefficientQuery_code (q : List Bool) : coefficientQuery q =
    pair (pairFst q) (BinaryNatCode.encode (Nat.fromBitsLE (pairSnd q))) := by
  simp only [coefficientQuery, normalize_code]

theorem safeExponent_packet (terms exponent : List Bool → List Bool) (q : List Bool) (i : ℕ) :
    Nat.fromBitsLE (safeExponent terms exponent (pair q (BinaryNatCode.encode i))) =
      if Nat.fromBitsLE (pairSnd q) < Nat.fromBitsLE (terms (pairFst q)) then
        Nat.fromBitsLE (exponent (pair (pairFst q)
          (pair (BinaryNatCode.encode (Nat.fromBitsLE (pairSnd q))) (BinaryNatCode.encode i)))) else 0 := by
  simp only [safeExponent, valid, exponentQuery, pairFst_pair, pairSnd_pair, normalize_code, decide_eq_true_eq]
  split_ifs <;> rfl

theorem coefficientValue_correct (terms f : List Bool → List Bool) (m : List Bool → ℕ)
    (a : (c : List Bool) → ℕ → ZMod (m c))
    (hf : ∀ c r, r < Nat.fromBitsLE (terms c) → f (pair c (BinaryNatCode.encode r)) = residueBits (a c r))
    (q : List Bool) : coefficientValue terms f q =
      residueBits (if Nat.fromBitsLE (pairSnd q) < Nat.fromBitsLE (terms (pairFst q)) then
        a (pairFst q) (Nat.fromBitsLE (pairSnd q)) else 0) := by
  simp only [coefficientValue, valid, coefficientQuery_code, decide_eq_true_eq]
  split_ifs with h
  · exact hf _ _ h
  · simp [residueBits, BinaryNatCode.encode]

def productOutput (modulus : List Bool → List Bool) (z : List Bool) : List Bool :=
  BinaryNat.mulMod (pair (BinaryNat.succ (modulus (pairFst (pairFst (pairFst z)))))
    (pair (pairSnd (pairFst z)) (pairSnd z)))

theorem productOutput_mem_FP {modulus : List Bool → List Bool} (hm : modulus ∈ FP) : productOutput modulus ∈ FP := by
  have hc := mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairFst_mem_FP
  have hmod := mem_FP_comp (mem_FP_comp hc hm) BinaryNat.succ_mem_FP
  have ha := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  have h := mem_FP_comp (mem_FP_pair hmod (mem_FP_pair ha pairSnd_mem_FP)) BinaryNat.mulMod_mem_FP
  refine mem_FP_of_eq (g := productOutput modulus) h ?_
  intro z
  simp only [Function.comp_apply, productOutput]

theorem productOutput_packet (modulus : List Bool → List Bool) (q : List Bool)
    (a b : ZMod (Nat.fromBitsLE (modulus (pairFst q)) + 1)) :
    productOutput modulus (pair (pair q (residueBits a)) (residueBits b)) = residueBits (a * b) := by
  let : NeZero (Nat.fromBitsLE (modulus (pairFst q)) + 1) := ⟨by omega⟩
  simp only [productOutput, pairFst_pair, pairSnd_pair, BinaryNat.mulMod_pair, BinaryNat.succ_eq_bits,
    residueBits, BinaryNatCode.encode, Nat.fromBitsLE_bits, ZMod.val_mul]

end LeanCanny.Algebra.RationalSubstitution.TermBits
