/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SylvesterAccessFP

/-!
# Correct streamed Sylvester access and resultant bit budgets

The specified degree parameters are retained even when they exceed the actual
degrees. Coefficient routines may return any scalar representation that encodes
zero as the empty word, in particular residues of integer coefficients.
-/

@[expose] public section

namespace LeanCanny.Algebra.SylvesterBits
open Complexity
open LeanCanny.Encoding

theorem code_value (k : ℕ) : Nat.fromBitsLE (BinaryNatCode.encode k) = k := Nat.fromBitsLE_bits k

@[simp] theorem row_packet (q : List Bool) (i j : ℕ) :
    row (pair q (pair (BinaryNatCode.encode i) (BinaryNatCode.encode j))) = BinaryNatCode.encode i := by
  simp [row]

@[simp] theorem col_packet (q : List Bool) (i j : ℕ) :
    col (pair q (pair (BinaryNatCode.encode i) (BinaryNatCode.encode j))) = BinaryNatCode.encode j := by
  simp [col]

@[simp] theorem context_packet (q : List Bool) (i j : ℕ) :
    context (pair q (pair (BinaryNatCode.encode i) (BinaryNatCode.encode j))) = pairFst q := by
  simp [context]

theorem bandEntry_spec {R : Type*} [Semiring R] (f : Polynomial R) (enc : R → List Bool)
    (coefficient width shift : List Bool → List Bool) (p : List Bool) (i s w : ℕ)
    (hi : row p = BinaryNatCode.encode i) (hs : shift p = BinaryNatCode.encode s)
    (hw : width p = BinaryNatCode.encode w)
    (hc : ∀ k, coefficient (pair (pairFst p) (BinaryNatCode.encode k)) = enc (f.coeff k)) :
    bandEntry coefficient width shift p =
      if s ≤ i ∧ i ≤ s + w then enc (f.coeff (i - s)) else [] := by
  have hend : bandEnd width shift p = BinaryNatCode.encode (s + w) := by
    simp only [bandEnd, hs, hw, BinaryNat.add_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have hin : coefficientInput shift p = pair (pairFst p) (BinaryNatCode.encode (i - s)) := by
    simp only [coefficientInput, hi, hs, BinaryNat.sub_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  simp only [bandEntry, hi, hs, hend, code_value, hin, hc]

structure CorrectAt (a : Access) (q : List Bool) {R : Type*} [Semiring R]
    (f g : Polynomial R) (m n : ℕ) (enc : R → List Bool) : Prop where
  leftDegree : a.leftDegree (pairFst q) = BinaryNatCode.encode m
  rightDegree : a.rightDegree (pairFst q) = BinaryNatCode.encode n
  leftCoefficient : ∀ k, a.leftCoefficient (pair q (BinaryNatCode.encode k)) = enc (f.coeff k)
  rightCoefficient : ∀ k, a.rightCoefficient (pair q (BinaryNatCode.encode k)) = enc (g.coeff k)
  zero : enc 0 = []

theorem sylvester_apply {R : Type*} [Semiring R] (f g : Polynomial R) (m n : ℕ)
    (i j : Fin (m + n)) :
    Polynomial.sylvester f g m n i j =
      if j.val < m then
        if j.val ≤ i.val ∧ i.val ≤ j.val + n then g.coeff (i.val - j.val) else 0
      else
        if j.val - m ≤ i.val ∧ i.val ≤ j.val - m + m then f.coeff (i.val - (j.val - m)) else 0 := by
  induction j using Fin.addCases with
  | left j => simp [Polynomial.sylvester, j.isLt, Set.mem_Icc]
  | right j => simp [Polynomial.sylvester, Set.mem_Icc]

theorem entry_correct (a : Access) (q : List Bool) {R : Type*} [Semiring R]
    (f g : Polynomial R) (m n : ℕ) (enc : R → List Bool) (hc : CorrectAt a q f g m n enc)
    (i j : Fin (m + n)) :
    entry a (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
      enc (Polynomial.sylvester f g m n i j) := by
  let p := pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))
  have hi : row p = BinaryNatCode.encode i.val := row_packet q i.val j.val
  have hj : col p = BinaryNatCode.encode j.val := col_packet q i.val j.val
  have hm : leftDegree a p = BinaryNatCode.encode m := by
    simpa only [leftDegree, p, context_packet] using hc.leftDegree
  have hn : rightDegree a p = BinaryNatCode.encode n := by
    simpa only [rightDegree, p, context_packet] using hc.rightDegree
  change entry a p = _
  rw [sylvester_apply]
  by_cases hblock : j.val < m
  · simp only [entry, hj, hm, code_value, hblock, ↓reduceIte]
    rw [bandEntry_spec g enc a.rightCoefficient (rightDegree a) col p i.val j.val n hi hj hn
      (by simpa only [p, pairFst_pair] using hc.rightCoefficient)]
    split_ifs <;> simp_all only [hc.zero]
  · have hs : rightShift a p = BinaryNatCode.encode (j.val - m) := by
      simp only [rightShift, hj, hm, BinaryNat.sub_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    simp only [entry, hj, hm, code_value, hblock, ↓reduceIte]
    rw [bandEntry_spec f enc a.leftCoefficient (leftDegree a) (rightShift a) p i.val
      (j.val - m) m hi hs hm (by simpa only [p, pairFst_pair] using hc.leftCoefficient)]
    split_ifs <;> simp_all only [hc.zero]

theorem sylvester_natAbs_le (f g : Polynomial ℤ) (m n b : ℕ)
    (hf : ∀ k, (f.coeff k).natAbs ≤ 2 ^ b) (hg : ∀ k, (g.coeff k).natAbs ≤ 2 ^ b)
    (i j : Fin (m + n)) : (Polynomial.sylvester f g m n i j).natAbs ≤ 2 ^ b := by
  rw [sylvester_apply]
  split_ifs
  · exact hg _
  · simp
  · exact hf _
  · simp

theorem resultant_size_le (f g : Polynomial ℤ) (m n b : ℕ)
    (hf : ∀ k, (f.coeff k).natAbs ≤ 2 ^ b) (hg : ∀ k, (g.coeff k).natAbs ≤ 2 ^ b) :
    (f.resultant g m n).natAbs.size ≤ (m + n).size * (m + n) + (m + n) * b + 1 :=
  IntegerModular.det_natAbs_size_le_uniform (Polynomial.sylvester f g m n) b
    (sylvester_natAbs_le f g m n b hf hg)

end LeanCanny.Algebra.SylvesterBits
