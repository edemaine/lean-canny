/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Encoding.BoundedAlgebraicFiberBasisMoments
public import LeanCanny.Encoding.BoundedAlgebraicFiberBasisPencil
public import LeanCanny.Algebra.IntegerSumSpace
public import LeanCanny.Encoding.BinaryPowModFP

/-! # Native weighted moments for fiber-root hashing

A context carries the original source, a binary summand count, a modulus
predecessor, and a parameter. Each summand recomputes three selected records
and one modular power. The signed sum uses polynomial space even when its
binary count is exponential. The matrix identity applies when that count
is the actual fiber-root count; no correctness of arbitrary counts is
assumed by the total evaluator.
-/

@[expose] public section
namespace LeanCanny.Encoding.BoundedAlgebraicFiberWeightedMoments
open LeanCanny.Algebra LeanCanny.Computation LeanCanny.ETR BoundedFullWriter
open BoundedAlgebraicSlice BoundedAlgebraicFiberRankBasis
open scoped Classical BigOperators

def original (b : List Bool) : List Bool := pairFst b
def count (b : List Bool) : List Bool := pairFst (pairSnd b)
def modulus (b : List Bool) : List Bool := pairFst (pairSnd (pairSnd b))
def parameter (b : List Bool) : List Bool := pairSnd (pairSnd (pairSnd b))
theorem original_FP : original ∈ FP := pairFst_mem_FP
theorem count_FP : count ∈ FP := mem_FP_comp pairSnd_mem_FP pairFst_mem_FP
theorem modulus_FP : modulus ∈ FP := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairFst_mem_FP
theorem parameter_FP : parameter ∈ FP := mem_FP_comp (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) pairSnd_mem_FP

def context (c : List Bool) (n : ℕ) (m : List Bool) (t : ℕ) : List Bool :=
  pair c (pair (BinaryNatCode.encode n) (pair m (BinaryNatCode.encode t)))

def base (s : List Bool) : List Bool := pairFst (pairFst s)
theorem base_FP : base ∈ FP := mem_FP_comp pairFst_mem_FP pairFst_mem_FP

def tripleQuery (s : List Bool) : List Bool := pair (original (base s))
  (pair (pairFst (pairSnd (pairFst s))) (pair (pairSnd (pairSnd (pairFst s))) (pairSnd s)))
theorem tripleQuery_FP : tripleQuery ∈ FP := by
  have hs := mem_FP_comp pairFst_mem_FP pairSnd_mem_FP
  exact mem_FP_pair (mem_FP_comp base_FP original_FP)
    (mem_FP_pair (mem_FP_comp hs pairFst_mem_FP) (mem_FP_pair (mem_FP_comp hs pairSnd_mem_FP) pairSnd_mem_FP))

def weight (s : List Bool) : List Bool := BinaryNat.powMod
  (pair (parameter (base s)) (pair (pairSnd s) (modulus (base s))))
theorem weight_FP : weight ∈ FP := by
  have H := mem_FP_comp (mem_FP_pair (mem_FP_comp base_FP parameter_FP)
    (mem_FP_pair pairSnd_mem_FP (mem_FP_comp base_FP modulus_FP))) BinaryNat.powMod_mem_FP
  exact mem_FP_of_eq H (fun _ => by simp only [weight, Function.comp_apply])

noncomputable def term (P : Readers) (F : Family) (s : List Bool) : ℤ :=
  BoundedAlgebraicFiberBasisMoments.moment P F (tripleQuery s) *
    ((Nat.fromBitsLE (parameter (base s)) ^ Nat.fromBitsLE (pairSnd s) %
      (Nat.fromBitsLE (modulus (base s)) + 1) : ℕ) : ℤ)

theorem term_evaluator {P : Readers} (h : P.PolyTime) {F : Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun s => SignStatisticBits.integerCode (term P F s)) := by
  have E := (BoundedAlgebraicFiberBasisMoments.evaluator h A ha).precompose tripleQuery tripleQuery_FP
  have W := SpaceFunction.ofFP (fun s => pair (weight s) []) (mem_FP_pair weight_FP (constFn_mem_FP []))
  have H := (E.pairOutputs W).postcompose IntegerSumBits.multiply IntegerSumBits.multiply_mem_FP
  apply H.congr
  funext s
  have hw : pair (weight s) [] = SignStatisticBits.integerCode
      ((Nat.fromBitsLE (parameter (base s)) ^ Nat.fromBitsLE (pairSnd s) %
        (Nat.fromBitsLE (modulus (base s)) + 1) : ℕ) : ℤ) := by
    simp only [weight, BinaryNat.powMod_eq_bits, pairFst_pair, pairSnd_pair, SignStatisticBits.integerCode,
      Int.toNat_natCast, Int.toNat_neg_natCast, BinaryNatCode.encode]
    rfl
  simp only [Function.comp_apply, hw, IntegerSumBits.multiply_codes, term]

noncomputable def entry (P : Readers) (F : Family) (q : List Bool) : ℤ :=
  ∑ r ∈ Finset.range (Nat.fromBitsLE (count (pairFst q))), term P F (pair q (BinaryNatCode.encode r))

theorem evaluator {P : Readers} (h : P.PolyTime) {F : Family} (A : F.Access)
    (ha : ∀ c, (TermView.term (P.source c)).arity ≤ P.dim c) :
    SpaceFunction (fun q => SignStatisticBits.integerCode (entry P F q)) := by
  exact IntegerSumBits.evaluator (term_evaluator h A ha) (count ∘ pairFst)
    (mem_FP_comp pairFst_mem_FP count_FP) (fun q r => term P F (pair q (BinaryNatCode.encode r))) (fun _ _ => rfl)

theorem entry_bound (P : Readers) (F : Family) (q : List Bool) :
    (entry P F q).natAbs ≤ Nat.fromBitsLE (count (pairFst q)) *
      2 ^ (F.degree (pairFst (original (pairFst q)))).size *
        (Nat.fromBitsLE (modulus (pairFst q)) + 1) := by
  apply (Int.natAbs_sum_le _ _).trans
  calc
    ∑ r ∈ Finset.range (Nat.fromBitsLE (count (pairFst q))), (term P F (pair q (BinaryNatCode.encode r))).natAbs ≤
        ∑ _r ∈ Finset.range (Nat.fromBitsLE (count (pairFst q))),
          2 ^ (F.degree (pairFst (original (pairFst q)))).size *
            (Nat.fromBitsLE (modulus (pairFst q)) + 1) := by
      apply Finset.sum_le_sum
      intro r _
      have H0 := BoundedAlgebraicFiberBasisMoments.moment_bound P F (tripleQuery (pair q (BinaryNatCode.encode r)))
      have hctx : pairFst (tripleQuery (pair q (BinaryNatCode.encode r))) = original (pairFst q) := by
        simp only [tripleQuery, base, pairFst_pair]
      rw [hctx] at H0
      have H := H0.trans (Nat.lt_size_self (F.degree (pairFst (original (pairFst q))))).le
      unfold term
      rw [Int.natAbs_mul, Int.natAbs_natCast]
      simp only [base, pairFst_pair, pairSnd_pair]
      exact Nat.mul_le_mul H (Nat.mod_lt _ (Nat.succ_pos _)).le
    _ = _ := by simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]; ring

noncomputable def entryBits (F : Family) (q : List Bool) : ℕ :=
  (count (pairFst q)).length + (F.degree (pairFst (original (pairFst q)))).size +
    (modulus (pairFst q)).length

theorem entryBits_unary {F : Family} (A : F.Access) : UnaryFn (entryBits F) := by
  have hc := mem_FP_comp pairFst_mem_FP count_FP
  have ho := mem_FP_comp pairFst_mem_FP original_FP
  have hs : (fun q => pairFst (original (pairFst q))) ∈ FP :=
    mem_FP_comp (f := fun q => original (pairFst q)) (g := pairFst) ho pairFst_mem_FP
  have hm := mem_FP_comp pairFst_mem_FP modulus_FP
  exact ((UnaryFn.length hc).add ((BoundedAlgebraicFiberRecords.size_unary A).comp hs)).add (UnaryFn.length hm)

theorem entry_bits (P : Readers) (F : Family) (q : List Bool) : (entry P F q).natAbs.size ≤ entryBits F q := by
  have hn := Nat.fromBitsLE_lt_pow_length (count (pairFst q))
  have hm : Nat.fromBitsLE (modulus (pairFst q)) + 1 ≤ 2 ^ (modulus (pairFst q)).length := by
    have H := Nat.fromBitsLE_lt_pow_length (modulus (pairFst q))
    omega
  have hb := (entry_bound P F q).trans (Nat.mul_le_mul_left
    (Nat.fromBitsLE (count (pairFst q)) * 2 ^ (F.degree (pairFst (original (pairFst q)))).size) hm)
  have hl := Nat.mul_lt_mul_of_pos_right hn (Nat.mul_pos
    (Nat.two_pow_pos ((F.degree (pairFst (original (pairFst q)))).size))
    (Nat.two_pow_pos (modulus (pairFst q)).length))
  apply Nat.size_le.mpr
  calc
    (entry P F q).natAbs ≤ Nat.fromBitsLE (count (pairFst q)) *
        (2 ^ (F.degree (pairFst (original (pairFst q)))).size * 2 ^ (modulus (pairFst q)).length) := by
      simpa only [Nat.mul_assoc] using hb
    _ < 2 ^ (count (pairFst q)).length *
        (2 ^ (F.degree (pairFst (original (pairFst q)))).size * 2 ^ (modulus (pairFst q)).length) := hl
    _ = 2 ^ entryBits F q := by rw [entryBits, pow_add, pow_add, Nat.mul_assoc]

theorem entry_packet (P : Readers) (F : Family) (c : List Bool) (m : List Bool) (t : ℕ)
    (i j : Fin (RootCount.count P F c)) :
    (entry P F (pair (context c (RootCount.count P F c) m t)
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) : ℚ) =
    BoundedAlgebraicFiberBasisPencil.weighted P F c
      (fun x => (BoundedAlgebraicFiberRootHash.integerValue P F c (Nat.fromBitsLE m + 1) t x : ℚ)) i j := by
  let q := pair (context c (RootCount.count P F c) m t)
    (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))
  have hn : Nat.fromBitsLE (count (pairFst q)) = RootCount.count P F c := by
    simp only [q, context, count, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have ht (r : ℕ) : term P F (pair q (BinaryNatCode.encode r)) =
      BoundedAlgebraicFiberBasisMoments.moment P F (pair c (pair (BinaryNatCode.encode i.val)
        (pair (BinaryNatCode.encode j.val) (BinaryNatCode.encode r)))) * ((t ^ r % (Nat.fromBitsLE m + 1) : ℕ) : ℤ) := by
    simp only [term, tripleQuery, base, q, context, original, parameter, modulus, pairFst_pair, pairSnd_pair,
      BinaryNatCode.encode, Nat.fromBitsLE_bits]
  change (entry P F q : ℚ) = _
  rw [entry, hn, ← Fin.sum_univ_eq_sum_range]
  simp only [Int.cast_sum, ht, Int.cast_mul, Int.cast_natCast, BoundedAlgebraicFiberBasisMoments.moment_packet]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  unfold BoundedAlgebraicFiberBasisPencil.weighted
  apply Finset.sum_congr rfl
  intro x _
  simp only [BoundedAlgebraicFiberRootHash.integerValue, Int.cast_sum, Int.cast_mul, Int.cast_natCast,
    BoundedAlgebraicFiberRootHash.integerVector, SignType.intCast_cast, BoundedAlgebraicFiberRootHash.sign_cast,
    Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  ring

end LeanCanny.Encoding.BoundedAlgebraicFiberWeightedMoments
