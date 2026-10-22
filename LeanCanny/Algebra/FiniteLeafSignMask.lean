/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FiniteLeafSignAppend

/-! # Omitting selected streamed sign constraints

An omitted row becomes the constant one with positive sign. One extra
monomial allows this even when the original source has no monomials.
-/

@[expose] public section
namespace LeanCanny.Algebra.FiniteLeafSignBits
open LeanCanny.Encoding LeanCanny.Computation RationalSubstitution MatrixPower
open scoped Classical BigOperators

noncomputable def Source.ignore {arity : List Bool → ℕ} (S : Source arity)
    (skip : List Bool → ℕ → Prop) : Source arity where
  count := S.count
  terms c := S.terms c + 1
  degree := S.degree
  height := S.height
  coefficient c j r := if skip c j then if r = 0 then 1 else 0
    else if r < S.terms c then S.coefficient c j r else 0
  exponent c j r i := if skip c j then 0 else if r < S.terms c then S.exponent c j r i else 0
  pattern c j := if skip c j then .pos else S.pattern c j
  exponent_le c j r _ i hi := by
    split_ifs with hs hr
    · exact Nat.zero_le _
    · exact S.exponent_le c j r hr i hi
    · exact Nat.zero_le _
  coefficient_le c j r _ := by
    split_ifs with hs hz hr
    · exact Nat.one_le_two_pow
    · simp
    · exact S.coefficient_le c j r hr
    · simp

theorem Source.ignore_polynomial {arity : List Bool → ℕ} (S : Source arity)
    (skip : List Bool → ℕ → Prop) (c : List Bool) (j : ℕ) :
    (S.ignore skip).polynomial c j = if skip c j then 1 else S.polynomial c j := by
  by_cases hs : skip c j
  · have h0 : Indexed.exponentVector (arity c) (fun _ => 0) = 0 := by ext i; rfl
    simp only [Source.polynomial, Source.ignore, hs, ite_true, Indexed.source, h0]
    simp
  · simp only [Source.polynomial, Source.ignore, hs, ite_false, Indexed.source]
    calc
      _ = ∑ r ∈ Finset.range (S.terms c), MvPolynomial.monomial
          (Indexed.exponentVector (arity c) (fun i => if r < S.terms c then S.exponent c j r i else 0))
          (if r < S.terms c then S.coefficient c j r else 0) := by
        symm
        apply Finset.sum_subset (Finset.range_mono (Nat.le_succ _))
        intro r _ hr
        have h : ¬r < S.terms c := by simpa only [Finset.mem_range] using hr
        simp only [h, ite_false, MvPolynomial.monomial_zero]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro r hr
        simp only [Finset.mem_range.mp hr, ite_true]

theorem Source.ignore_signs_iff {arity : List Bool → ℕ} (S : Source arity)
    (skip : List Bool → ℕ → Prop) (c : List Bool) (z : Fin (arity c) → ℝ) :
    (∀ j : Fin ((S.ignore skip).count c),
      SignType.sign (((S.ignore skip).polynomial c j.val).eval₂ (Int.castRingHom ℝ) z) =
        (S.ignore skip).pattern c j.val) ↔
      ∀ j : Fin (S.count c), ¬skip c j.val →
        SignType.sign ((S.polynomial c j.val).eval₂ (Int.castRingHom ℝ) z) = S.pattern c j.val := by
  constructor
  · intro h j hj
    have H := h j
    rw [Source.ignore_polynomial] at H
    change SignType.sign ((if skip c j.val then 1 else S.polynomial c j.val).eval₂
      (Int.castRingHom ℝ) z) = (if skip c j.val then .pos else S.pattern c j.val) at H
    simpa only [hj, ite_false] using H
  · intro h j
    rw [Source.ignore_polynomial]
    change SignType.sign ((if skip c j.val then 1 else S.polynomial c j.val).eval₂
      (Int.castRingHom ℝ) z) = (if skip c j.val then .pos else S.pattern c j.val)
    by_cases hj : skip c j.val
    · simp only [hj, ite_true, MvPolynomial.eval₂_one, sign_one]
      rfl
    · simpa only [hj, ite_false] using h j hj

def rowPredicate (skip : List Bool → ℕ → Prop) (q : List Bool) : Prop :=
  skip (pairFst q) (Nat.fromBitsLE (pairSnd q))

def constantOne (q : List Bool) : List Bool := ArithmeticBits.one (BinaryNat.succ (pairSnd q))

theorem constantOne_FP : constantOne ∈ FP := by
  have hm := mem_FP_comp pairSnd_mem_FP BinaryNat.succ_mem_FP
  have H := mem_FP_comp hm ArithmeticBits.one_mem_FP
  exact mem_FP_of_eq H (fun _ => rfl)

theorem constantOne_packet (q : List Bool) (r m : ℕ) (hm : 0 < m) :
    constantOne (pair (pair q (BinaryNatCode.encode r)) (BinaryNatCode.encode (m - 1))) =
      MatrixPower.residueBits (1 : ZMod m) := by
  simp only [constantOne, pairSnd_pair, BinaryNat.succ_eq_bits, BinaryNatCode.encode, Nat.fromBitsLE_bits,
    Nat.sub_add_cancel hm]
  exact ArithmeticBits.one_residueBits m

noncomputable def ignoredCoefficient {arity : List Bool → ℕ} {S : Source arity} (A : S.Access)
    (skip : List Bool → ℕ → Prop) (q : List Bool) : List Bool :=
  if rowPredicate skip (pairFst (pairFst q)) then
    if Nat.fromBitsLE (pairSnd (pairFst q)) = 0 then constantOne q else []
  else if validTerm S (pairFst q) then A.coefficient q else []

noncomputable def ignoredExponent {arity : List Bool → ℕ} {S : Source arity} (A : S.Access)
    (skip : List Bool → ℕ → Prop) (q : List Bool) : List Bool :=
  if rowPredicate skip (pairFst q) then []
  else if validTerm S (exponentTerm q) then A.exponent q else []

noncomputable def ignoredPattern {arity : List Bool → ℕ} {S : Source arity} (A : S.Access)
    (skip : List Bool → ℕ → Prop) (q : List Bool) : List Bool :=
  if rowPredicate skip q then InfinitesimalSign.encode .pos else A.pattern q

theorem ignoredCoefficient_evaluator {arity : List Bool → ℕ} {S : Source arity} (A : S.Access)
    (skip : List Bool → ℕ → Prop) (hs : FPPred (rowPredicate skip)) :
    SpaceFunction (ignoredCoefficient A skip) := by
  have hp := hs.comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP)
  have hz : FPPred (fun q : List Bool => Nat.fromBitsLE (pairSnd (pairFst q)) = 0) :=
    (BinaryNat.le_fppred (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP) (constFn_mem_FP [])).of_iff
      (fun q => by change Nat.fromBitsLE (pairSnd (pairFst q)) ≤ 0 ↔ _ = 0; omega)
  have ht := (validTerm_pred A).comp pairFst_mem_FP
  have Z := SpaceFunction.ofFP (fun _ => []) (constFn_mem_FP [])
  have L := SpaceFunction.branch (fun q => decide (Nat.fromBitsLE (pairSnd (pairFst q)) = 0))
    hz.flag_mem_FP (SpaceFunction.ofFP _ constantOne_FP) Z
  have R := SpaceFunction.branch (fun q => decide (validTerm S (pairFst q))) ht.flag_mem_FP A.coefficientEvaluator Z
  have E := SpaceFunction.branch (fun q => decide (rowPredicate skip (pairFst (pairFst q)))) hp.flag_mem_FP L R
  exact E.congr (funext fun q => by simp only [ignoredCoefficient, decide_eq_true_eq])

theorem ignoredExponent_FP {arity : List Bool → ℕ} {S : Source arity} (A : S.Access)
    (skip : List Bool → ℕ → Prop) (hs : FPPred (rowPredicate skip)) : ignoredExponent A skip ∈ FP :=
  (hs.comp pairFst_mem_FP).ite_mem_FP (constFn_mem_FP [])
    (((validTerm_pred A).comp exponentTerm_FP).ite_mem_FP A.exponent_FP (constFn_mem_FP []))

theorem ignoredPattern_FP {arity : List Bool → ℕ} {S : Source arity} (A : S.Access)
    (skip : List Bool → ℕ → Prop) (hs : FPPred (rowPredicate skip)) : ignoredPattern A skip ∈ FP :=
  hs.ite_mem_FP (constFn_mem_FP _) A.pattern_FP

noncomputable def Source.Access.ignore {arity : List Bool → ℕ} {S : Source arity} (A : S.Access)
    (skip : List Bool → ℕ → Prop) (hs : FPPred (rowPredicate skip)) : (S.ignore skip).Access where
  coefficient := ignoredCoefficient A skip
  exponent := ignoredExponent A skip
  pattern := ignoredPattern A skip
  count_unary := A.count_unary
  terms_binary := A.terms_binary.add (BinaryFn.const 1)
  degree_binary := A.degree_binary
  height_binary := A.height_binary
  coefficientEvaluator := ignoredCoefficient_evaluator A skip hs
  exponent_FP := ignoredExponent_FP A skip hs
  pattern_FP := ignoredPattern_FP A skip hs
  coefficient_eq q r _ m hm := by
    simp only [ignoredCoefficient, rowPredicate, validTerm, Source.ignore, pairFst_pair, pairSnd_pair,
      show Nat.fromBitsLE (BinaryNatCode.encode r) = r from Nat.fromBitsLE_bits r]
    split_ifs with hskip hz ht
    · simpa only [Int.cast_one] using constantOne_packet q r m hm
    · simp only [Int.cast_zero, MatrixPower.residueBits, ZMod.val_zero]; rfl
    · exact A.coefficient_eq q r ht m hm
    · simp only [Int.cast_zero, MatrixPower.residueBits, ZMod.val_zero]; rfl
  exponent_eq q r _ i hi := by
    simp only [ignoredExponent, rowPredicate, validTerm, exponentTerm, Source.ignore, pairFst_pair, pairSnd_pair,
      show Nat.fromBitsLE (BinaryNatCode.encode r) = r from Nat.fromBitsLE_bits r]
    split_ifs with hskip ht
    · rfl
    · exact A.exponent_eq q r ht i hi
    · rfl
  pattern_eq c j := by
    simp only [ignoredPattern, rowPredicate, Source.ignore, pairFst_pair, pairSnd_pair,
      show Nat.fromBitsLE (BinaryNatCode.encode j) = j from Nat.fromBitsLE_bits j]
    split_ifs
    · rfl
    · exact A.pattern_eq c j

end LeanCanny.Algebra.FiniteLeafSignBits
