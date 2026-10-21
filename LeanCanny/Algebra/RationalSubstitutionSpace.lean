/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IndexedRationalSubstitution
public import LeanCanny.Algebra.RationalSubstitutionTermFP
public import LeanCanny.Algebra.ModularSumSpace
public import LeanCanny.Computation.SpaceFunctionChain

/-!
# Modular coefficient evaluation for indexed rational substitution

Source coefficients and coordinate coefficients run through certified space-bounded
routines. Binary term/variable counts, exponent access, width, selected degree,
and a positive-modulus predecessor are FP. The evaluator multiplies selected
monomial coefficients by source coefficients and sums the residues. No expanded
polynomial or exponent vector is stored, and invalid term indices are masked.
-/

@[expose] public section

namespace LeanCanny.Algebra.RationalSubstitution
open Complexity
open LeanCanny.Encoding
open LeanCanny.Computation
open MatrixPower
open scoped BigOperators

def safePower (terms : List Bool → List Bool) (e : List Bool → ℕ → ℕ → ℕ) (c : List Bool) (r i : ℕ) : ℕ :=
  if r < Nat.fromBitsLE (terms c) then e c r i else 0

noncomputable def termPolynomial (arity width terms modulus : List Bool → List Bool)
    (e : List Bool → ℕ → ℕ → ℕ)
    (np dp : (c : List Bool) → ℕ → Polynomial (ZMod (Nat.fromBitsLE (modulus c) + 1)))
    (c : List Bool) (r : ℕ) : Polynomial (ZMod (Nat.fromBitsLE (modulus c) + 1)) :=
  ∏ i ∈ Finset.range (Nat.fromBitsLE (arity c)),
    np c i ^ safePower terms e c r i * dp c i ^ (Nat.fromBitsLE (width c) - safePower terms e c r i)

noncomputable def termAt (arity width terms modulus degree : List Bool → List Bool)
    (e : List Bool → ℕ → ℕ → ℕ)
    (a : (c : List Bool) → ℕ → ZMod (Nat.fromBitsLE (modulus c) + 1))
    (np dp : (c : List Bool) → ℕ → Polynomial (ZMod (Nat.fromBitsLE (modulus c) + 1)))
    (c : List Bool) (r : ℕ) : List Bool :=
  residueBits ((if r < Nat.fromBitsLE (terms c) then a c r else 0) *
    (termPolynomial arity width terms modulus e np dp c r).coeff (Nat.fromBitsLE (degree c)))

noncomputable def termValue (arity width terms modulus degree : List Bool → List Bool)
    (e : List Bool → ℕ → ℕ → ℕ)
    (a : (c : List Bool) → ℕ → ZMod (Nat.fromBitsLE (modulus c) + 1))
    (np dp : (c : List Bool) → ℕ → Polynomial (ZMod (Nat.fromBitsLE (modulus c) + 1))) (q : List Bool) : List Bool :=
  termAt arity width terms modulus degree e a np dp (pairFst q) (Nat.fromBitsLE (pairSnd q))

theorem termEvaluator {f n d : List Bool → List Bool}
    (C : SpaceFunction f) (N : SpaceFunction n) (D : SpaceFunction d)
    (arity width terms exponent modulus degree : List Bool → List Bool)
    (ha : arity ∈ FP) (hw : width ∈ FP) (ht : terms ∈ FP) (he : exponent ∈ FP) (hm : modulus ∈ FP) (hk : degree ∈ FP)
    (e : List Bool → ℕ → ℕ → ℕ)
    (a : (c : List Bool) → ℕ → ZMod (Nat.fromBitsLE (modulus c) + 1))
    (np dp : (c : List Bool) → ℕ → Polynomial (ZMod (Nat.fromBitsLE (modulus c) + 1)))
    (hbound : ∀ c r, r < Nat.fromBitsLE (terms c) → ∀ i, i < Nat.fromBitsLE (arity c) → e c r i ≤ Nat.fromBitsLE (width c))
    (hexp : ∀ c r, r < Nat.fromBitsLE (terms c) → ∀ i, i < Nat.fromBitsLE (arity c) →
      Nat.fromBitsLE (exponent (pair c (pair (BinaryNatCode.encode r) (BinaryNatCode.encode i)))) = e c r i)
    (hf : ∀ c r, r < Nat.fromBitsLE (terms c) → f (pair c (BinaryNatCode.encode r)) = residueBits (a c r))
    (hn : ∀ c i, i < Nat.fromBitsLE (arity c) → ∀ k,
      n (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) = residueBits ((np c i).coeff k))
    (hd : ∀ c i, i < Nat.fromBitsLE (arity c) → ∀ k,
      d (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) = residueBits ((dp c i).coeff k)) :
    SpaceFunction (termValue arity width terms modulus degree e a np dp) := by
  have hA := mem_FP_comp pairFst_mem_FP ha
  have hW := mem_FP_comp pairFst_mem_FP hw
  have hM := mem_FP_comp pairFst_mem_FP hm
  have hK := mem_FP_comp pairFst_mem_FP hk
  let B := monomialEvaluator (N.precompose TermBits.sourceQuery TermBits.sourceQuery_mem_FP)
    (D.precompose TermBits.sourceQuery TermBits.sourceQuery_mem_FP)
    (arity ∘ pairFst) (width ∘ pairFst) (TermBits.safeExponent terms exponent) (modulus ∘ pairFst) (degree ∘ pairFst)
    hA hW (TermBits.safeExponent_mem_FP ht he) hM hK
    (fun q i => safePower terms e (pairFst q) (Nat.fromBitsLE (pairSnd q)) i)
    (fun q => np (pairFst q)) (fun q => dp (pairFst q))
    (by
      intro q i hi
      unfold safePower
      split_ifs with hr
      · exact hbound _ _ hr i hi
      · exact Nat.zero_le _)
    (by
      intro q i hi
      rw [TermBits.safeExponent_packet]
      unfold safePower
      split_ifs with hr
      · exact hexp _ _ hr i hi
      · rfl)
    (by
      intro q i hi k
      simp only [Function.comp_apply, TermBits.sourceQuery, pairFst_pair, pairSnd_pair]
      exact hn _ i hi k)
    (by
      intro q i hi k
      simp only [Function.comp_apply, TermBits.sourceQuery, pairFst_pair, pairSnd_pair]
      exact hd _ i hi k)
  let A := TermBits.coefficientEvaluator C terms ht
  let Q := (A.withInput.chain ((B.precompose pairFst pairFst_mem_FP).withInput)).postcompose
    (TermBits.productOutput modulus) (TermBits.productOutput_mem_FP hm)
  refine Q.congr (funext fun q => ?_)
  simp only [Function.comp_apply, pairFst_pair]
  rw [TermBits.coefficientValue_correct terms f (fun c => Nat.fromBitsLE (modulus c) + 1) a hf]
  simp only [monomialValue, Function.comp_apply]
  rw [TermBits.productOutput_packet]
  rfl

noncomputable def value (arity width terms modulus degree : List Bool → List Bool)
    (e : List Bool → ℕ → ℕ → ℕ)
    (a : (c : List Bool) → ℕ → ZMod (Nat.fromBitsLE (modulus c) + 1))
    (np dp : (c : List Bool) → ℕ → Polynomial (ZMod (Nat.fromBitsLE (modulus c) + 1))) (c : List Bool) : List Bool :=
  residueBits ((Indexed.cleared (Nat.fromBitsLE (arity c)) (Nat.fromBitsLE (terms c))
    (Nat.fromBitsLE (width c)) (a c) (e c) (np c) (dp c)).coeff (Nat.fromBitsLE (degree c)))

theorem evaluator {f n d : List Bool → List Bool}
    (C : SpaceFunction f) (N : SpaceFunction n) (D : SpaceFunction d)
    (arity width terms exponent modulus degree : List Bool → List Bool)
    (ha : arity ∈ FP) (hw : width ∈ FP) (ht : terms ∈ FP) (he : exponent ∈ FP) (hm : modulus ∈ FP) (hk : degree ∈ FP)
    (e : List Bool → ℕ → ℕ → ℕ)
    (a : (c : List Bool) → ℕ → ZMod (Nat.fromBitsLE (modulus c) + 1))
    (np dp : (c : List Bool) → ℕ → Polynomial (ZMod (Nat.fromBitsLE (modulus c) + 1)))
    (hbound : ∀ c r, r < Nat.fromBitsLE (terms c) → ∀ i, i < Nat.fromBitsLE (arity c) → e c r i ≤ Nat.fromBitsLE (width c))
    (hexp : ∀ c r, r < Nat.fromBitsLE (terms c) → ∀ i, i < Nat.fromBitsLE (arity c) →
      Nat.fromBitsLE (exponent (pair c (pair (BinaryNatCode.encode r) (BinaryNatCode.encode i)))) = e c r i)
    (hf : ∀ c r, r < Nat.fromBitsLE (terms c) → f (pair c (BinaryNatCode.encode r)) = residueBits (a c r))
    (hn : ∀ c i, i < Nat.fromBitsLE (arity c) → ∀ k,
      n (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) = residueBits ((np c i).coeff k))
    (hd : ∀ c i, i < Nat.fromBitsLE (arity c) → ∀ k,
      d (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))) = residueBits ((dp c i).coeff k)) :
    SpaceFunction (value arity width terms modulus degree e a np dp) := by
  let E := termEvaluator C N D arity width terms exponent modulus degree ha hw ht he hm hk e a np dp hbound hexp hf hn hd
  have hmod := mem_FP_comp hm BinaryNat.succ_mem_FP
  let b := fun c r => a c r *
    (∏ i ∈ Finset.range (Nat.fromBitsLE (arity c)), np c i ^ e c r i *
      dp c i ^ (Nat.fromBitsLE (width c) - e c r i)).coeff (Nat.fromBitsLE (degree c))
  have hvalue : (fun c => Nat.fromBitsLE ((BinaryNat.succ ∘ modulus) c)) =
      (fun c => Nat.fromBitsLE (modulus c) + 1) := by
    funext c
    simp only [Function.comp_apply, BinaryNat.succ_eq_bits, Nat.fromBitsLE_bits]
  have Q := ModularSum.evaluatorWithModulus E terms (BinaryNat.succ ∘ modulus) ht hmod
    (fun c => Nat.fromBitsLE (modulus c) + 1) hvalue b (fun _ => by omega) (by
    intro c r hr
    simp only [termValue, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    simp only [termAt, hr, ↓reduceIte, termPolynomial, safePower]
    rfl)
  refine Q.congr (funext fun c => ?_)
  simp only [value, Indexed.cleared, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul]
  rfl

end LeanCanny.Algebra.RationalSubstitution
