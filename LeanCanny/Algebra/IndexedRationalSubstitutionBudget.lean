/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IndexedRationalSubstitutionBounds
public import LeanCanny.Algebra.RationalSubstitutionBudget

/-!
# FP binary budget writers for streamed term families

The term count stays binary. Its normalized word length gives the count's bit
size, so neither the term count nor any coefficient magnitude is expanded to
unary. Coordinate coefficient bounds are converted into coefficient-mass bounds
using their degree allowance.
-/

@[expose] public section

namespace LeanCanny.Algebra.RationalSubstitution.Indexed

open LeanCanny.Encoding
open Polynomial

def degreeCode (a w e : List Bool) : List Bool :=
  BinaryNat.mul (pair (BinaryNat.mul (pair a w)) e)

def massBudgetCode (a w t b s : List Bool) : List Bool :=
  BinaryNat.succ (BinaryNat.add (pair
    (BinaryNat.add (pair (BinaryNatCode.encode (BinaryNat.normalize t).length) s)) (degreeCode a w b)))

def coefficientBudgetCode (a w t e b s : List Bool) : List Bool :=
  massBudgetCode a w t (RationalSubstitution.sourceBudgetCode [true] e b) s

theorem degreeCode_mem_FP {a w e : List Bool → List Bool} (ha : a ∈ FP) (hw : w ∈ FP) (he : e ∈ FP) :
    (fun c => degreeCode (a c) (w c) (e c)) ∈ FP := by
  have hp := mem_FP_comp (mem_FP_pair ha hw) BinaryNat.mul_mem_FP
  have h := mem_FP_comp (mem_FP_pair hp he) BinaryNat.mul_mem_FP
  refine mem_FP_of_eq (g := fun c => degreeCode (a c) (w c) (e c)) h ?_
  intro c
  simp only [Function.comp_apply, degreeCode]

theorem massBudgetCode_mem_FP {a w t b s : List Bool → List Bool}
    (ha : a ∈ FP) (hw : w ∈ FP) (ht : t ∈ FP) (hb : b ∈ FP) (hs : s ∈ FP) :
    (fun c => massBudgetCode (a c) (w c) (t c) (b c) (s c)) ∈ FP := by
  have hsize := bits_mem_FP (UnaryFn.length (mem_FP_comp ht BinaryNat.normalize_mem_FP))
  have hsource := mem_FP_comp (mem_FP_pair hsize hs) BinaryNat.add_mem_FP
  have hsum := mem_FP_comp (mem_FP_pair hsource (degreeCode_mem_FP ha hw hb)) BinaryNat.add_mem_FP
  have h := mem_FP_comp hsum BinaryNat.succ_mem_FP
  refine mem_FP_of_eq (g := fun c => massBudgetCode (a c) (w c) (t c) (b c) (s c)) h ?_
  intro c
  simp only [Function.comp_apply, massBudgetCode, BinaryNatCode.encode]

theorem coefficientBudgetCode_mem_FP {a w t e b s : List Bool → List Bool}
    (ha : a ∈ FP) (hw : w ∈ FP) (ht : t ∈ FP) (he : e ∈ FP) (hb : b ∈ FP) (hs : s ∈ FP) :
    (fun c => coefficientBudgetCode (a c) (w c) (t c) (e c) (b c) (s c)) ∈ FP :=
  massBudgetCode_mem_FP ha hw ht (sourceBudgetCode_mem_FP (constFn_mem_FP [true]) he hb) hs

theorem degreeCode_code (a w e : List Bool) : degreeCode a w e =
    BinaryNatCode.encode (Nat.fromBitsLE a * Nat.fromBitsLE w * Nat.fromBitsLE e) := by
  simp only [degreeCode, BinaryNat.mul_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

theorem massBudgetCode_code (a w t b s : List Bool) : massBudgetCode a w t b s =
    BinaryNatCode.encode ((Nat.fromBitsLE t).size + Nat.fromBitsLE s + Nat.fromBitsLE a * Nat.fromBitsLE w * Nat.fromBitsLE b + 1) := by
  simp only [massBudgetCode, degreeCode_code, BinaryNat.normalize_eq_bits, BinaryNat.add_pair, BinaryNat.succ_eq_bits,
    BinaryNatCode.encode, Nat.fromBitsLE_bits, Nat.size_eq_bits_len]

theorem coefficientBudgetCode_code (a w t e b s : List Bool) : coefficientBudgetCode a w t e b s =
    BinaryNatCode.encode ((Nat.fromBitsLE t).size + Nat.fromBitsLE s +
      Nat.fromBitsLE a * Nat.fromBitsLE w * (Nat.fromBitsLE b + (Nat.fromBitsLE e + 1).size) + 1) := by
  simp only [coefficientBudgetCode, massBudgetCode_code, sourceBudgetCode_code, BinaryNatCode.encode,
    Nat.fromBitsLE_bits, show Nat.fromBitsLE [true] = 1 from rfl, Nat.one_mul]

theorem coeff_size_le_coefficientBudgetCode (A M W : ℕ) (a : ℕ → ℤ) (e : ℕ → ℕ → ℕ) (n d : ℕ → ℤ[X])
    (E b s : List Bool) (he : ∀ r, r < M → ∀ i, i < A → e r i ≤ W)
    (ha : ∀ r, r < M → (a r).natAbs ≤ 2 ^ Nat.fromBitsLE s)
    (hnD : ∀ i, i < A → (n i).natDegree ≤ Nat.fromBitsLE E)
    (hdD : ∀ i, i < A → (d i).natDegree ≤ Nat.fromBitsLE E)
    (hn : ∀ i, i < A → ∀ k, ((n i).coeff k).natAbs ≤ 2 ^ Nat.fromBitsLE b)
    (hd : ∀ i, i < A → ∀ k, ((d i).coeff k).natAbs ≤ 2 ^ Nat.fromBitsLE b) (k : ℕ) :
    ((cleared A M W a e n d).coeff k).natAbs.size ≤ Nat.fromBitsLE
      (coefficientBudgetCode (BinaryNatCode.encode A) (BinaryNatCode.encode W) (BinaryNatCode.encode M) E b s) := by
  simp only [coefficientBudgetCode_code, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  exact coeff_size_cleared_le A M W _ _ a e n d he ha
    (fun i hi => coefficientMass_le_pow_of_degree_coeff (n i) _ _ (hnD i hi) (hn i hi))
    (fun i hi => coefficientMass_le_pow_of_degree_coeff (d i) _ _ (hdD i hi) (hd i hi)) k

end LeanCanny.Algebra.RationalSubstitution.Indexed
