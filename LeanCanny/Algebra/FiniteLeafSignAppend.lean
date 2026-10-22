/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FiniteLeafSignPrepared
public import LeanCanny.Computation.SpaceFunctionBranch

/-! # Concatenating streamed sign constraints -/

@[expose] public section
namespace LeanCanny.Algebra.FiniteLeafSignBits
open LeanCanny.Encoding LeanCanny.Computation
open scoped Classical BigOperators
attribute [local irreducible] BinaryNat.sub

noncomputable def Source.append {arity : List Bool → ℕ} (S T : Source arity) : Source arity where
  count c := S.count c + T.count c
  terms c := S.terms c + T.terms c
  degree c := S.degree c + T.degree c
  height c := S.height c + T.height c
  coefficient c j r := if j < S.count c then
    if r < S.terms c then S.coefficient c j r else 0
    else if r < T.terms c then T.coefficient c (j - S.count c) r else 0
  exponent c j r i := if j < S.count c then
    if r < S.terms c then S.exponent c j r i else 0
    else if r < T.terms c then T.exponent c (j - S.count c) r i else 0
  pattern c j := if j < S.count c then S.pattern c j else T.pattern c (j - S.count c)
  exponent_le c j r _ i hi := by
    split_ifs with hj hr hr
    · have H := S.exponent_le c j r hr i hi
      omega
    · omega
    · have H := T.exponent_le c (j - S.count c) r hr i hi
      omega
    · omega
  coefficient_le c j r _ := by
    split_ifs with hj hr hr
    · exact (S.coefficient_le c j r hr).trans (Nat.pow_le_pow_right (by decide) (by omega))
    · simp
    · exact (T.coefficient_le c (j - S.count c) r hr).trans (Nat.pow_le_pow_right (by decide) (by omega))
    · simp

private theorem indexed_source_pad {A M N : ℕ} (hMN : M ≤ N) (a : ℕ → ℤ) (e : ℕ → ℕ → ℕ) :
    RationalSubstitution.Indexed.source A N (fun r => if r < M then a r else 0)
      (fun r i => if r < M then e r i else 0) = RationalSubstitution.Indexed.source A M a e := by
  classical
  unfold RationalSubstitution.Indexed.source
  calc
    _ = ∑ r ∈ Finset.range M, MvPolynomial.monomial
      (RationalSubstitution.Indexed.exponentVector A (fun i => if r < M then e r i else 0))
      (if r < M then a r else 0) := by
      symm
      apply Finset.sum_subset (Finset.range_mono hMN)
      intro r _ hr
      have h : ¬r < M := by simpa only [Finset.mem_range] using hr
      simp only [h, ite_false, MvPolynomial.monomial_zero]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      simp only [Finset.mem_range.mp hr, ite_true]

 theorem Source.append_polynomial_left {arity : List Bool → ℕ} (S T : Source arity) (c : List Bool) (j : ℕ)
    (hj : j < S.count c) : (S.append T).polynomial c j = S.polynomial c j := by
  simp only [Source.polynomial, Source.append, hj, ite_true]
  exact indexed_source_pad (Nat.le_add_right _ _) _ _

 theorem Source.append_polynomial_right {arity : List Bool → ℕ} (S T : Source arity) (c : List Bool) (j : ℕ)
    (hj : S.count c ≤ j) : (S.append T).polynomial c j = T.polynomial c (j - S.count c) := by
  have hj' : ¬j < S.count c := by omega
  simp only [Source.polynomial, Source.append, hj', ite_false]
  exact indexed_source_pad (Nat.le_add_left _ _) _ _

def leftRow {arity : List Bool → ℕ} (S : Source arity) (q : List Bool) : Prop :=
  Nat.fromBitsLE (pairSnd q) < S.count (pairFst q)

def validTerm {arity : List Bool → ℕ} (S : Source arity) (q : List Bool) : Prop :=
  Nat.fromBitsLE (pairSnd q) < S.terms (pairFst (pairFst q))

theorem leftRow_pred {arity : List Bool → ℕ} {S : Source arity} (A : S.Access) : FPPred (leftRow S) :=
  (BinaryNat.lt_fppred pairSnd_mem_FP (mem_FP_comp pairFst_mem_FP (bits_mem_FP A.count_unary))).of_iff
    (fun _ => by simp only [leftRow, Function.comp_apply, Nat.fromBitsLE_bits])

theorem validTerm_pred {arity : List Bool → ℕ} {S : Source arity} (A : S.Access) : FPPred (validTerm S) :=
  (BinaryNat.lt_fppred pairSnd_mem_FP
    (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) A.terms_binary.bits_mem_FP)).of_iff
    (fun _ => by simp only [validTerm, Function.comp_apply, BinaryNatCode.encode, Nat.fromBitsLE_bits])

def shiftedRow {arity : List Bool → ℕ} (S : Source arity) (q : List Bool) : List Bool :=
  pair (pairFst q) (BinaryNat.sub (pair (pairSnd q) (BinaryNatCode.encode (S.count (pairFst q)))))

theorem shiftedRow_FP {arity : List Bool → ℕ} {S : Source arity} (A : S.Access) : shiftedRow S ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_comp (mem_FP_pair pairSnd_mem_FP
    (mem_FP_comp pairFst_mem_FP (bits_mem_FP A.count_unary))) BinaryNat.sub_mem_FP)

def shiftedCoefficient {arity : List Bool → ℕ} (S : Source arity) (p : List Bool) : List Bool :=
  pair (pair (shiftedRow S (pairFst (pairFst p))) (pairSnd (pairFst p))) (pairSnd p)

theorem shiftedCoefficient_FP {arity : List Bool → ℕ} {S : Source arity} (A : S.Access) : shiftedCoefficient S ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) (shiftedRow_FP A))
    (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)) pairSnd_mem_FP

def shiftedExponent {arity : List Bool → ℕ} (S : Source arity) (p : List Bool) : List Bool :=
  pair (shiftedRow S (pairFst p)) (pairSnd p)

theorem shiftedExponent_FP {arity : List Bool → ℕ} {S : Source arity} (A : S.Access) : shiftedExponent S ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP (shiftedRow_FP A)) pairSnd_mem_FP

def exponentTerm (p : List Bool) : List Bool := pair (pairFst p) (pairFst (pairSnd p))

theorem exponentTerm_FP : exponentTerm ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)

noncomputable def appendCoefficient {arity : List Bool → ℕ} {S T : Source arity} (A : S.Access) (B : T.Access)
    (p : List Bool) : List Bool :=
  if leftRow S (pairFst (pairFst p)) then
    if validTerm S (pairFst p) then A.coefficient p else []
  else if validTerm T (pairFst p) then B.coefficient (shiftedCoefficient S p) else []

noncomputable def appendExponent {arity : List Bool → ℕ} {S T : Source arity} (A : S.Access) (B : T.Access)
    (p : List Bool) : List Bool :=
  if leftRow S (pairFst p) then
    if validTerm S (exponentTerm p) then A.exponent p else []
  else if validTerm T (exponentTerm p) then B.exponent (shiftedExponent S p) else []

noncomputable def appendPattern {arity : List Bool → ℕ} {S T : Source arity} (A : S.Access) (B : T.Access)
    (p : List Bool) : List Bool :=
  if leftRow S p then A.pattern p else B.pattern (shiftedRow S p)

 theorem appendCoefficient_evaluator {arity : List Bool → ℕ} {S T : Source arity} (A : S.Access) (B : T.Access) :
    SpaceFunction (appendCoefficient A B) := by
  have hp := (leftRow_pred A).comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  have hs := (validTerm_pred A).comp pairFst_mem_FP
  have ht := (validTerm_pred B).comp pairFst_mem_FP
  have Z := SpaceFunction.ofFP (fun _ => []) (constFn_mem_FP [])
  have L := SpaceFunction.branch (fun p => decide (validTerm S (pairFst p))) hs.flag_mem_FP A.coefficientEvaluator Z
  have R := SpaceFunction.branch (fun p => decide (validTerm T (pairFst p))) ht.flag_mem_FP
    (B.coefficientEvaluator.precompose _ (shiftedCoefficient_FP A)) Z
  have E := SpaceFunction.branch (fun p => decide (leftRow S (pairFst (pairFst p)))) hp.flag_mem_FP L R
  refine E.congr (funext fun p => ?_)
  simp only [appendCoefficient, Function.comp_apply, decide_eq_true_eq]

 theorem appendExponent_FP {arity : List Bool → ℕ} {S T : Source arity} (A : S.Access) (B : T.Access) :
    appendExponent A B ∈ FP := by
  have hp := (leftRow_pred A).comp pairFst_mem_FP
  have hs := (validTerm_pred A).comp exponentTerm_FP
  have ht := (validTerm_pred B).comp exponentTerm_FP
  exact hp.ite_mem_FP (hs.ite_mem_FP A.exponent_FP (constFn_mem_FP []))
    (ht.ite_mem_FP (mem_FP_comp (shiftedExponent_FP A) B.exponent_FP) (constFn_mem_FP []))

 theorem appendPattern_FP {arity : List Bool → ℕ} {S T : Source arity} (A : S.Access) (B : T.Access) :
    appendPattern A B ∈ FP :=
  (leftRow_pred A).ite_mem_FP A.pattern_FP (mem_FP_comp (shiftedRow_FP A) B.pattern_FP)

theorem shiftedRow_fst {arity : List Bool → ℕ} (S : Source arity) (q : List Bool) :
    pairFst (shiftedRow S q) = pairFst q := by
  simp only [shiftedRow, pairFst_pair]

theorem shiftedRow_value {arity : List Bool → ℕ} (S : Source arity) (q : List Bool) :
    Nat.fromBitsLE (pairSnd (shiftedRow S q)) = Nat.fromBitsLE (pairSnd q) - S.count (pairFst q) := by
  simp only [shiftedRow, pairSnd_pair, BinaryNat.sub_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]

noncomputable def Source.Access.append {arity : List Bool → ℕ} {S T : Source arity}
    (A : S.Access) (B : T.Access) : (S.append T).Access where
  coefficient := appendCoefficient A B
  exponent := appendExponent A B
  pattern := appendPattern A B
  count_unary := A.count_unary.add B.count_unary
  terms_binary := A.terms_binary.add B.terms_binary
  degree_binary := A.degree_binary.add B.degree_binary
  height_binary := A.height_binary.add B.height_binary
  coefficientEvaluator := appendCoefficient_evaluator A B
  exponent_FP := appendExponent_FP A B
  pattern_FP := appendPattern_FP A B
  coefficient_eq q r _ m hm := by
    simp only [appendCoefficient, leftRow, validTerm, pairFst_pair, pairSnd_pair,
      show Nat.fromBitsLE (BinaryNatCode.encode r) = r from Nat.fromBitsLE_bits r, Source.append]
    split_ifs with hj hr hr
    · exact A.coefficient_eq q r hr m hm
    · simp only [Int.cast_zero, MatrixPower.residueBits, ZMod.val_zero]
      rfl
    · have H := B.coefficient_eq (shiftedRow S q) r (by simpa only [shiftedRow_fst] using hr) m hm
      simpa only [shiftedCoefficient, pairFst_pair, pairSnd_pair, shiftedRow_fst, shiftedRow_value] using H
    · simp only [Int.cast_zero, MatrixPower.residueBits, ZMod.val_zero]
      rfl
  exponent_eq q r _ i hi := by
    simp only [appendExponent, leftRow, validTerm, exponentTerm, pairFst_pair, pairSnd_pair,
      show Nat.fromBitsLE (BinaryNatCode.encode r) = r from Nat.fromBitsLE_bits r, Source.append]
    split_ifs with hj hr hr
    · exact A.exponent_eq q r hr i hi
    · rfl
    · have H := B.exponent_eq (shiftedRow S q) r (by simpa only [shiftedRow_fst] using hr) i
        (by simpa only [shiftedRow_fst] using hi)
      simpa only [shiftedExponent, pairFst_pair, pairSnd_pair, shiftedRow_fst, shiftedRow_value] using H
    · rfl
  pattern_eq c j := by
    simp only [appendPattern, leftRow, Source.append, pairFst_pair, pairSnd_pair,
      show Nat.fromBitsLE (BinaryNatCode.encode j) = j from Nat.fromBitsLE_bits j]
    split_ifs with hj
    · exact A.pattern_eq c j
    · simpa only [shiftedRow, pairFst_pair, pairSnd_pair, BinaryNat.sub_pair,
        BinaryNatCode.encode, Nat.fromBitsLE_bits] using B.pattern_eq c (j - S.count c)

/-- Concatenated rows express the conjunction of their two row conditions. -/
theorem Source.append_all_iff {arity : List Bool → ℕ} (S T : Source arity) (c : List Bool)
    (R : MvPolynomial (Fin (arity c)) ℤ → SignType → Prop) :
    (∀ j : Fin ((S.append T).count c), R ((S.append T).polynomial c j.val) ((S.append T).pattern c j.val)) ↔
      (∀ j : Fin (S.count c), R (S.polynomial c j.val) (S.pattern c j.val)) ∧
      (∀ j : Fin (T.count c), R (T.polynomial c j.val) (T.pattern c j.val)) := by
  constructor
  · intro h
    constructor
    · intro j
      have hj : j.val < (S.append T).count c := by change j.val < S.count c + T.count c; omega
      have H := h ⟨j.val, hj⟩
      rw [Source.append_polynomial_left S T c j.val j.isLt] at H
      simpa only [Source.append, j.isLt, ite_true] using H
    · intro j
      have hj : S.count c + j.val < (S.append T).count c := by change S.count c + j.val < S.count c + T.count c; omega
      have H : R ((S.append T).polynomial c (S.count c + j.val)) ((S.append T).pattern c (S.count c + j.val)) := h ⟨S.count c + j.val, hj⟩
      have hn : ¬S.count c + j.val < S.count c := by omega
      rw [Source.append_polynomial_right S T c (S.count c + j.val) (by omega), Nat.add_sub_cancel_left] at H
      simpa only [Source.append, hn, ite_false, Nat.add_sub_cancel_left] using H
  · rintro ⟨hs, ht⟩ j
    by_cases hj : j.val < S.count c
    · rw [Source.append_polynomial_left S T c j.val hj]
      simpa only [Source.append, hj, ite_true] using hs ⟨j.val, hj⟩
    · have hi : j.val - S.count c < T.count c := by
        have H := j.isLt
        change j.val < S.count c + T.count c at H
        omega
      rw [Source.append_polynomial_right S T c j.val (by omega)]
      simpa only [Source.append, hj, ite_false] using ht ⟨j.val - S.count c, hi⟩

end LeanCanny.Algebra.FiniteLeafSignBits
