/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SymbolicPairRecovery
public import LeanCanny.Algebra.BivariateDeterminantInteger
public import LeanCanny.Algebra.SymbolicScaledQuotientSpace

/-! # Native bivariate first-subresultant recovery coefficients -/

@[expose] public section
namespace LeanCanny.Algebra.SymbolicPairRecoveryBits
open Polynomial SymbolicScaledSquarefree
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open SymbolicScaledQuotientBits (original modulus alpha target original_FP modulus_FP alpha_FP target_FP)
open scoped Classical
attribute [local irreducible] Matrix.det

abbrev Family := SymbolicFixedTableEntryBits.Family

lemma binary_sub {f g : List Bool → ℕ} (hf : BinaryFn f) (hg : BinaryFn g) :
    BinaryFn (fun c => f c - g c) := by
  apply BinaryFn.of_bits
  have H := mem_FP_comp (mem_FP_pair hf.bits_mem_FP hg.bits_mem_FP) BinaryNat.sub_mem_FP
  exact mem_FP_of_eq H (fun c => by simp only [Function.comp_apply, BinaryNat.sub_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits])

lemma binary_max_two {f : List Bool → ℕ} (hf : BinaryFn f) : BinaryFn (fun c => max 2 (f c)) := by
  have hp := BinaryNat.le_fppred (constFn_mem_FP (BinaryNatCode.encode 2)) hf.bits_mem_FP
  have H := hp.ite_mem_FP hf.bits_mem_FP (constFn_mem_FP (BinaryNatCode.encode 2))
  apply BinaryFn.of_bits
  refine mem_FP_of_eq H (fun c => ?_)
  simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits]
  split_ifs with h
  · rw [max_eq_right h]
  · rw [max_eq_left (by omega)]

lemma fromBits_one : Nat.fromBitsLE [true] = 1 := rfl

def Family.clipped (F : Family) : Family :=
  { F with leftOrder c := max 2 (F.leftOrder c), rightOrder c := max 2 (F.rightOrder c) }

def Family.minorAccess (F : Family) (r : ℕ) : SubresultantBits.Access where
  base := {
    leftDegree q := BinaryNatCode.encode (max 2 (F.leftOrder (original q)))
    rightDegree q := BinaryNatCode.encode (max 2 (F.rightOrder (original q)))
    modulus _ := [true]
    degree _ := []
    leftCoefficient _ := []
    rightCoefficient _ := [] }
  order _ := [true]
  coefficient _ := BinaryNatCode.encode r

lemma Family.minorAccess_controls (F : Family) (r : ℕ)
    (hm : BinaryFn F.leftOrder) (hn : BinaryFn F.rightOrder) :
    (F.minorAccess r).ControlsPolyTime := by
  have hM : BinaryFn (fun q => max 2 (F.leftOrder (original q))) :=
    (binary_max_two hm).comp original_FP
  have hN : BinaryFn (fun q => max 2 (F.rightOrder (original q))) :=
    (binary_max_two hn).comp original_FP
  exact ⟨⟨hM.bits_mem_FP, hN.bits_mem_FP, constFn_mem_FP _, constFn_mem_FP _⟩,
    constFn_mem_FP _, constFn_mem_FP _⟩

def flattenQuery (z : List Bool) : List Bool :=
  pair (pair (original (pairFst z)) (modulus (pairFst z))) (pairSnd z)
lemma flattenQuery_FP : flattenQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp (f := pairFst) (g := original) pairFst_mem_FP original_FP)
    (mem_FP_comp (f := pairFst) (g := modulus) pairFst_mem_FP modulus_FP)) pairSnd_mem_FP

noncomputable def Family.minorEntry (F : Family) (r : ℕ) : List Bool → List Bool :=
  F.clipped.entry ∘ flattenQuery ∘ (F.minorAccess r).query

lemma Family.minorEntryEvaluator (F : Family) (r : ℕ)
    (hm : BinaryFn F.leftOrder) (hn : BinaryFn F.rightOrder) (hc : BinaryFn F.direction)
    (P : SpaceFunction (SymbolicFixedTableEntryBits.coefficient F.left))
    (Q : SpaceFunction (SymbolicFixedTableEntryBits.coefficient F.right)) :
    SpaceFunction (F.minorEntry r) := by
  exact ((F.clipped.entryEvaluator (binary_max_two hm) (binary_max_two hn) hc P Q).precompose
    flattenQuery flattenQuery_FP).precompose (F.minorAccess r).query
      ((F.minorAccess r).query_mem_FP (F.minorAccess_controls r hm hn))

noncomputable def Family.minorMatrix (F : Family) (r : ℕ) (q : List Bool) :=
  Subresultant.minor (shiftFamily (F.left (original q)) (F.direction (original q)))
    ((F.right (original q)).map C) (max 2 (F.leftOrder (original q)))
      (max 2 (F.rightOrder (original q))) 1 r

lemma Family.minorEntry_packet (F : Family) (r : ℕ) (hr : r ≤ 1) (q : List Bool)
    (i j : Fin ((max 2 (F.leftOrder (original q)) - 1) + (max 2 (F.rightOrder (original q)) - 1)))
    (u v : ℕ) :
    F.minorEntry r (pair q (pair (BinaryNatCode.encode i.val) (pair (BinaryNatCode.encode j.val)
      (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v))))) =
      residueBits (((((F.minorMatrix r q i j).coeff v).coeff u) : ℤ) : ZMod (Nat.fromBitsLE (modulus q) + 1)) := by
  let m := max 2 (F.leftOrder (original q))
  let n := max 2 (F.rightOrder (original q))
  have hm : 1 ≤ m := by dsimp only [m]; omega
  have hn : 1 ≤ n := by dsimp only [n]; omega
  have hs := F.clipped.entry_correct (original q) (modulus q)
    (CoefficientMinor.row m n 1 r hm hn hr i) (PrincipalMinor.col m n 1 hm hn j) u v
  have he := CoefficientMinor.minor_apply (shiftFamily (F.left (original q)) (F.direction (original q)))
    ((F.right (original q)).map C) m n 1 r hm hn hr i j
  -- The degree payload is opaque to the row/column transformation.
  have hquery' : (F.minorAccess r).query
      (pair q (pair (BinaryNatCode.encode i.val) (pair (BinaryNatCode.encode j.val)
        (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v))))) =
      pair q (pair (BinaryNatCode.encode (Subresultant.rowIndex 1 r i.val))
        (pair (BinaryNatCode.encode (Subresultant.colIndex m 1 j.val))
          (pair (BinaryNatCode.encode u) (BinaryNatCode.encode v)))) := by
    simp only [SubresultantBits.Access.query, SubresultantBits.Access.selectedRow,
      SubresultantBits.Access.selectedCol, SubresultantBits.Access.row, SubresultantBits.Access.col,
      SubresultantBits.Access.degree, Family.minorAccess, SubresultantBits.Access.leftWidth,
      pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits,
      BinaryNat.sub_pair, BinaryNat.add_pair, Subresultant.rowIndex, Subresultant.colIndex, fromBits_one]
    dsimp only [m]
    split_ifs <;> rfl
  simp only [Family.minorEntry, Function.comp_apply, hquery', flattenQuery, pairFst_pair, pairSnd_pair]
  dsimp only [Family.minorMatrix]
  rw [he]
  simpa only [Family.clipped, Family.minorMatrix, CoefficientMinor.row, PrincipalMinor.col,
    original, modulus, m, n] using hs

noncomputable def Family.subresultantValue (F : Family) (r : ℕ) : List Bool → List Bool :=
  SymbolicFixedTableEntryBits.coefficient (fun c => SymbolicPairRecovery.subresultantCoefficient
    (F.left c) (F.right c) (F.direction c) (F.leftOrder c) (F.rightOrder c) r)

lemma Family.subresultantEvaluator (F : Family) (r : ℕ) (hr : r ≤ 1) (B : List Bool → ℕ)
    (hP : ∀ c k, ((F.left c).coeff k).natDegree ≤ B c)
    (hQ : ∀ c k, ((F.right c).coeff k).natDegree ≤ B c)
    (hm : BinaryFn F.leftOrder) (hn : BinaryFn F.rightOrder) (hc : BinaryFn F.direction) (hB : BinaryFn B)
    (P : SpaceFunction (SymbolicFixedTableEntryBits.coefficient F.left))
    (Q : SpaceFunction (SymbolicFixedTableEntryBits.coefficient F.right)) :
    SpaceFunction (F.subresultantValue r) := by
  let N := fun q => (max 2 (F.leftOrder (original q)) - 1) + (max 2 (F.rightOrder (original q)) - 1)
  let bound := fun q => BinaryNatCode.encode (B (original q))
  have hdim : (fun q => BinaryNatCode.encode (N q)) ∈ FP := by
    have h : BinaryFn N := ((binary_sub (binary_max_two hm) (BinaryFn.const 1)).add
      (binary_sub (binary_max_two hn) (BinaryFn.const 1))).comp original_FP
    exact h.bits_mem_FP
  have hpos q : 0 < N q := by dsimp only [N]; omega
  have hmat q (i j : Fin (N q)) k : ((F.minorMatrix r q i j).coeff k).natDegree ≤ Nat.fromBitsLE (bound q) := by
    rw [Family.minorMatrix, CoefficientMinor.minor_apply _ _ _ _ _ _ (by omega) (by omega) hr]
    simpa only [bound, BinaryNatCode.encode, Nat.fromBitsLE_bits] using
      SymbolicFixedTable.sylvester_inner_degree (F.left (original q)) (F.right (original q))
        (F.direction (original q)) _ _ (B (original q)) (hP _) (hQ _) _ _ k
  have E := BivariateDeterminantBits.integerEvaluator N modulus alpha target bound (F.minorMatrix r)
    (F.minorEntry r) hpos hmat (F.minorEntry_packet r hr) (F.minorEntryEvaluator r hm hn hc P Q)
      hdim modulus_FP alpha_FP target_FP
      (mem_FP_comp (f := original) (g := fun c => BinaryNatCode.encode (B c)) original_FP hB.bits_mem_FP)
  have hM := mem_FP_comp (f := original) (g := fun c => BinaryNatCode.encode (F.leftOrder c)) original_FP hm.bits_mem_FP
  have hN := mem_FP_comp (f := original) (g := fun c => BinaryNatCode.encode (F.rightOrder c)) original_FP hn.bits_mem_FP
  have hp := (BinaryNat.lt_fppred (constFn_mem_FP [true]) hM).and
    (BinaryNat.lt_fppred (constFn_mem_FP [true]) hN)
  have H := SpaceFunction.branch (fun q => decide (1 < F.leftOrder (original q) ∧ 1 < F.rightOrder (original q)))
    ((hp.of_iff (fun q => by simp only [Function.comp_apply, BinaryNatCode.encode, Nat.fromBitsLE_bits, fromBits_one])).flag_mem_FP)
      E (SpaceFunction.ofFP _ (constFn_mem_FP []))
  refine H.congr (funext fun q => ?_)
  change (if decide (1 < F.leftOrder (original q) ∧ 1 < F.rightOrder (original q)) = true then
    BivariateDeterminantBits.integerValue N modulus alpha target (F.minorMatrix r) q else []) =
    SymbolicFixedTableEntryBits.integerResidue
      (((SymbolicPairRecovery.subresultantCoefficient (F.left (original q)) (F.right (original q))
        (F.direction (original q)) (F.leftOrder (original q)) (F.rightOrder (original q)) r).coeff
          (Nat.fromBitsLE (target q))).coeff (Nat.fromBitsLE (alpha q))) (Nat.fromBitsLE (modulus q) + 1)
  simp only [decide_eq_true_eq]
  by_cases h : 1 < F.leftOrder (original q) ∧ 1 < F.rightOrder (original q)
  · rw [ite_eq_left h, SymbolicPairRecovery.subresultantCoefficient_eq_minor _ _ _ _ _ _ h.1 h.2 hr]
    have hd := congrArg₂ (fun m n : ℕ =>
      (Subresultant.minor (shiftFamily (F.left (original q)) (F.direction (original q)))
        ((F.right (original q)).map C) m n 1 r).det)
      (max_eq_right (by omega : 2 ≤ F.leftOrder (original q)))
      (max_eq_right (by omega : 2 ≤ F.rightOrder (original q)))
    have hz := congrArg (fun p : Polynomial (Polynomial ℤ) =>
      SymbolicFixedTableEntryBits.integerResidue ((p.coeff (Nat.fromBitsLE (target q))).coeff
        (Nat.fromBitsLE (alpha q))) (Nat.fromBitsLE (modulus q) + 1)) hd
    exact hz
  · rw [ite_eq_right h, SymbolicPairRecovery.subresultantCoefficient_zero _ _ _ _ _ _ (by tauto)]
    simp only [coeff_zero, SymbolicFixedTableEntryBits.integerResidue, residueBits, Int.cast_zero,
      ZMod.val_zero, BinaryNatCode.encode]
    rfl

end LeanCanny.Algebra.SymbolicPairRecoveryBits
