/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.FiniteAnnihilatorDegreeSpace
public import LeanCanny.Algebra.BalancedParameterContext

/-! # Native degrees of canonical balanced subtrees

Degrees depend only on square-free leaf degrees, not on the separating
directions. A binary-counted product scans the leaf interval of a node. Its
height is capped by the binary size of the unary source count, keeping the
accumulator polynomial in input length even on malformed node queries.
-/

@[expose] public section

namespace LeanCanny.Algebra.BalancedCanonicalDegrees
open Polynomial
open LeanCanny.Encoding LeanCanny.Computation Turing.MultiTapeTM
open SeparableBits (Family Readers)
open BalancedParameterContext (original height index packet)
open scoped BigOperators Classical

noncomputable def leafDegree (B : Family) (count : List Bool → ℕ) (c : List Bool) (i : ℕ) : ℕ :=
  if i < count c then (ScaledSquarefree.polynomial (B.polynomial (pair c (BinaryNatCode.encode i)))).natDegree else 1

noncomputable def leaves (B : Family) (count : List Bool → ℕ) (hne : ∀ c, B.polynomial c ≠ 0) (c : List Bool) :
    ℕ → SeparableIntegerPolynomial :=
  FiniteAnnihilatorTree.leaf (fun i => B.polynomial (pair c (BinaryNatCode.encode i))) (count c) (fun _ _ => hne _)

theorem leafDegree_eq (B : Family) (count : List Bool → ℕ) (hne : ∀ c, B.polynomial c ≠ 0) (c : List Bool) (i : ℕ) :
    leafDegree B count c i = (leaves B count hne c i).polynomial.natDegree := by
  by_cases hi : i < count c
  · simp only [leafDegree, hi, ite_true, leaves, FiniteAnnihilatorTree.leaf_degree _ _ _ i hi]
  · simp only [leafDegree, hi, ite_false]
    exact (FiniteAnnihilatorTree.padding_degree
      (fun j => B.polynomial (pair c (BinaryNatCode.encode j))) (count c) (fun _ _ => hne _) i (by omega)).symm

noncomputable def leafCode (B : Family) (count : List Bool → ℕ) (p : List Bool) : List Bool :=
  if Nat.fromBitsLE (pairSnd p) < count (pairFst p) then
    BinaryNatCode.encode (ScaledSquarefree.polynomial (B.polynomial p)).natDegree else BinaryNatCode.encode 1

theorem leafCode_packet (B : Family) (count : List Bool → ℕ) (c : List Bool) (i : ℕ) :
    leafCode B count (pair c (BinaryNatCode.encode i)) = BinaryNatCode.encode (leafDegree B count c i) := by
  simp only [leafCode, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits, leafDegree]
  split_ifs <;> rfl

theorem leafEvaluator (B : Family) (A : Readers B) (hne : ∀ c, B.polynomial c ≠ 0)
    (count : List Bool → ℕ) (hn : UnaryFn count) : SpaceFunction (leafCode B count) := by
  have hp := BinaryNat.lt_fppred pairSnd_mem_FP (mem_FP_comp pairFst_mem_FP (bits_mem_FP hn))
  have E := SpaceFunction.branch
    (fun p => decide (Nat.fromBitsLE (pairSnd p) < Nat.fromBitsLE (Nat.bits (count (pairFst p)))))
    hp.flag_mem_FP (SeparableBits.scaledSquarefreeDegreeEvaluator B A hne)
    (SpaceFunction.ofFP _ (constFn_mem_FP (BinaryNatCode.encode 1)))
  exact E.congr (funext fun p => by simp only [leafCode, Nat.fromBitsLE_bits, decide_eq_true_eq])

def boundedHeight (count : List Bool → ℕ) (p : List Bool) : ℕ := min (height p) (count (original p)).size
def width (count : List Bool → ℕ) (p : List Bool) : ℕ := 2 ^ boundedHeight count p
def maxLeaves (count : List Bool → ℕ) (c : List Bool) : ℕ := 2 * (count c + 1)

theorem width_le (count : List Bool → ℕ) (p : List Bool) : width count p ≤ maxLeaves count (original p) :=
  (Nat.pow_le_pow_right (by decide) (Nat.min_le_right _ _)).trans (FiniteAnnihilatorTree.width_bound _)

theorem boundedHeight_unary {count : List Bool → ℕ} (hn : UnaryFn count) : UnaryFn (boundedHeight count) :=
  BalancedParameterContext.height_unary.min ((hn.comp BalancedParameterContext.original_FP).size)

theorem width_binary {count : List Bool → ℕ} (hn : UnaryFn count) : BinaryFn (width count) :=
  (BinaryFn.const 2).powUnary (boundedHeight_unary hn)

theorem maxLeaves_unary {count : List Bool → ℕ} (hn : UnaryFn count) : UnaryFn (maxLeaves count) :=
  (UnaryFn.const 2).mul (hn.add (UnaryFn.const 1))

noncomputable def product (B : Family) (count : List Bool → ℕ) (c : List Bool) (start k : ℕ) : ℕ :=
  ∏ j ∈ Finset.range k, leafDegree B count c (start + j)

noncomputable def degree (B : Family) (count : List Bool → ℕ) (p : List Bool) : ℕ :=
  product B count (original p) (width count p * index p) (width count p)

theorem product_bound (B : Family) (count D : List Bool → ℕ) (hne : ∀ c, B.polynomial c ≠ 0)
    (hD : ∀ c i, i < count c → (B.polynomial (pair c (BinaryNatCode.encode i))).natDegree ≤ D c)
    (c : List Bool) (start k : ℕ) : product B count c start k ≤ (D c + 1) ^ k := by
  induction k with
  | zero => simp only [product, Finset.range_zero, Finset.prod_empty, pow_zero, le_refl]
  | succ k ih =>
    have hl : leafDegree B count c (start + k) ≤ D c + 1 := by
      by_cases hi : start + k < count c
      · rw [leafDegree, ite_eq_left hi]
        exact ((ScaledSquarefree.polynomial_natDegree_le _ (hne _)).trans (hD c _ hi)).trans (Nat.le_succ _)
      · simp only [leafDegree, hi, ite_false]
        omega
    rw [product, Finset.prod_range_succ]
    exact (Nat.mul_le_mul ih hl).trans_eq (pow_succ _ _).symm

theorem degree_packet (B : Family) (count : List Bool → ℕ) (hne : ∀ c, B.polynomial c ≠ 0)
    (c : List Bool) (h i : ℕ) (hh : h ≤ (count c).size) :
    degree B count (packet c h i) = (BalancedPrimitiveTree.node (leaves B count hne c) h i).polynomial.natDegree := by
  simp only [degree, width, boundedHeight, BalancedParameterContext.height_packet,
    BalancedParameterContext.original_packet, BalancedParameterContext.index_packet, Nat.min_eq_left hh]
  rw [BalancedPrimitiveTree.degree_eq_prod]
  unfold product
  apply Finset.prod_congr rfl
  intro j _
  exact leafDegree_eq B count hne c _

theorem evaluator (B : Family) (A : Readers B) (hne : ∀ c, B.polynomial c ≠ 0)
    (count D : List Bool → ℕ) (hn : UnaryFn count) (hD : BinaryFn D)
    (hdegree : ∀ c i, i < count c → (B.polynomial (pair c (BinaryNatCode.encode i))).natDegree ≤ D c) :
    SpaceFunction (fun p => BinaryNatCode.encode (degree B count p)) := by
  have hc := ComputableTidilyInPolyTime.fst encBits encNat
  have hi := ComputableTidilyInPolyTime.snd encBits encNat
  have hs : BinaryFn (fun p => width count p * index p) :=
    (width_binary hn).mul (BinaryFn.fromBits BalancedParameterContext.indexWord_FP)
  have hquery := pair_computable (BalancedParameterContext.original_FP.comp hc)
    (natBits_computable.comp (ComputableTidilyInPolyTime.binary_add' (hs.comp hc) hi))
  have hleaf := (leafEvaluator B A hne count hn).computable.comp (ComputableTidilyInPolySpace.of_polyTime hquery)
  have hvalue := (ComputableTidilyInPolySpace.of_polyTime fromBitsLE_computable).comp hleaf
  have hd : ComputableTidilyInPolySpace
      (fun p : List Bool × ℕ => leafDegree B count (original p.1) (width count p.1 * index p.1 + p.2))
      (encPair encBits encNat) encNat :=
    hvalue.congr fun p => by
      change Nat.fromBitsLE (leafCode B count
        (pair (original p.1) (BinaryNatCode.encode (width count p.1 * index p.1 + p.2)))) = _
      rw [leafCode_packet, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  have hDo : BinaryFn (fun p => D (original p)) := hD.comp BalancedParameterContext.original_FP
  have hbound : BinaryFn (fun p => (D (original p) + 1) ^ maxLeaves count (original p)) :=
    (hDo.add (BinaryFn.const 1)).powUnary
      ((maxLeaves_unary hn).comp BalancedParameterContext.original_FP)
  have E := TidyBoundedFold.product_evaluator
    (factor := fun p i => leafDegree B count (original p) (width count p * index p + i))
    hd (width_binary hn) hbound.polyBounded_length (fun p k hk => by
      apply ComputableTidilyInO.length_encNat_mono
      exact (product_bound B count D hne hdegree _ _ _).trans
        (Nat.pow_le_pow_right (by omega) (hk.trans (width_le count p))))
  exact ⟨((ComputableTidilyInPolySpace.of_polyTime natBits_computable).comp E).congr
    (fun _ => rfl)⟩

end LeanCanny.Algebra.BalancedCanonicalDegrees
