/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BalancedCandidateResultant
public import LeanCanny.Algebra.CannyResultantBudget
public import LeanCanny.Algebra.PrimitivePairConstruction

/-! # A native bounded scan for the canonical node direction

Stored child orders and a binary child-height control determine all loop and
test budgets. The native scan works on every table context. Exact child orders,
separability, and coefficient bounds at one node suffice to identify its answer
with the canonical primitive-pair direction; no global table promise is used.
-/

@[expose] public section

namespace LeanCanny.Algebra.BalancedTablePolynomials.Candidate
open Polynomial
open LeanCanny.Encoding LeanCanny.Computation
open SeparableBits (Family Readers)
open BalancedParameterContext (child)

def leftDegree (p : List Bool) : ℕ := BalancedMetadataTable.order (child false p)
def rightDegree (p : List Bool) : ℕ := BalancedMetadataTable.order (child true p)
def degree (p : List Bool) : ℕ := leftDegree p * rightDegree p
def count (p : List Bool) : ℕ := degree p ^ 2 + 1

def heightBudget (childHeight : List Bool → ℕ) (p : List Bool) : ℕ :=
  CannyResultantBits.coefficientBudget (leftDegree p) (rightDegree p) (degree p ^ 2) (childHeight p) (childHeight p)

attribute [local irreducible] tree node BinaryNat.normalize BalancedMetadataTable.read

theorem leftDegree_binary : BinaryFn leftDegree := by
  have h := mem_FP_comp (BalancedParameterContext.child_FP false) (BalancedMetadataTable.read_FP false)
  exact BinaryFn.fromBits h

theorem rightDegree_binary : BinaryFn rightDegree := by
  have h := mem_FP_comp (BalancedParameterContext.child_FP true) (BalancedMetadataTable.read_FP false)
  exact BinaryFn.fromBits h

theorem degree_binary : BinaryFn degree := leftDegree_binary.mul rightDegree_binary

theorem count_binary : BinaryFn count := by
  have h := (degree_binary.mul degree_binary).add (BinaryFn.const 1)
  have he : count = (fun p => degree p * degree p + 1) := funext fun p => by simp only [count, pow_two]
  rw [he]
  exact h

theorem heightBudget_binary {H : List Bool → ℕ} (hH : BinaryFn H) : BinaryFn (heightBudget H) := by
  have hsq : BinaryFn (fun p => degree p ^ 2) := by simpa only [pow_two] using degree_binary.mul degree_binary
  exact CannyResultantBits.coefficientBudget_binary leftDegree_binary rightDegree_binary hsq hH hH

noncomputable def language (B : Family) (H : List Bool → ℕ) : Language :=
  SeparableBoundedTest.language (polynomial B) (degree ∘ pairFst) (heightBudget H ∘ pairFst)

theorem decider (B : Family) (A : Readers B) (H : List Bool → ℕ) (hH : BinaryFn H) : SpaceDecider (language B H) := by
  have hd : BinaryFn (degree ∘ pairFst) := degree_binary.comp pairFst_mem_FP
  have hb : BinaryFn (heightBudget H ∘ pairFst) := (heightBudget_binary hH).comp pairFst_mem_FP
  exact SeparableBoundedTest.decider (polynomial B) (coefficient B) (coefficient_packet B)
    (coefficientEvaluator B A) _ _ hd hb

noncomputable def direction (B : Family) (H : List Bool → ℕ) (p : List Bool) : ℕ :=
  BoundedChoice.search (language B H) p (count p) - 1

theorem evaluator (B : Family) (A : Readers B) (H : List Bool → ℕ) (hH : BinaryFn H) :
    SpaceFunction (fun p => BinaryNatCode.encode (direction B H p)) := by
  have E := BoundedChoice.evaluator (decider B A H hH) (fun p => BinaryNatCode.encode (count p)) count_binary.bits_mem_FP
  exact E.congr (funext fun p => by simp only [direction, BinaryNatCode.encode, Nat.fromBitsLE_bits])

theorem polynomial_packet (B : Family) (p : List Bool) (r : ℕ)
    (hl : leftDegree p = (node B (child false p)).natDegree)
    (hr : rightDegree p = (node B (child true p)).natDegree) :
    polynomial B (pair p (BinaryNatCode.encode r)) = cannyResultant (node B (child false p)) (node B (child true p)) r := by
  simp only [polynomial, BalancedTablePolynomials.leftOrder, BalancedTablePolynomials.rightOrder,
    pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  change cannyResultantWithDegrees (node B (child false p)) (node B (child true p)) r (leftDegree p) (rightDegree p) = _
  rw [hl, hr, cannyResultantWithDegrees_exact]

theorem height_at (B : Family) (H : List Bool → ℕ) (p : List Bool) (r : ℕ) (hcount : r < count p)
    (hl : leftDegree p = (node B (child false p)).natDegree)
    (hr : rightDegree p = (node B (child true p)).natDegree)
    (hbl : ∀ k, ((node B (child false p)).coeff k).natAbs ≤ 2 ^ H p)
    (hbr : ∀ k, ((node B (child true p)).coeff k).natAbs ≤ 2 ^ H p) (k : ℕ) :
    ((cannyResultant (node B (child false p)) (node B (child true p)) r).coeff k).natAbs ≤ 2 ^ heightBudget H p := by
  have hc : r ≤ degree p ^ 2 := by dsimp only [count] at hcount; omega
  have h := CannyResultantBits.coefficient_size_le (node B (child false p)) (node B (child true p)) r
    (leftDegree p) (rightDegree p) (degree p ^ 2) (H p) (H p) k hl.ge hr.ge hc hbl hbr
  exact (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by decide) h)

theorem member_iff (B : Family) (H : List Bool → ℕ) (p : List Bool) (r : ℕ) (hcount : r < count p)
    (hl : leftDegree p = (node B (child false p)).natDegree)
    (hr : rightDegree p = (node B (child true p)).natDegree)
    (hsl : ((node B (child false p)).map (Int.castRingHom (AlgebraicClosure ℚ))).Separable)
    (hsr : ((node B (child true p)).map (Int.castRingHom (AlgebraicClosure ℚ))).Separable)
    (hbl : ∀ k, ((node B (child false p)).coeff k).natAbs ≤ 2 ^ H p)
    (hbr : ∀ k, ((node B (child true p)).coeff k).natAbs ≤ 2 ^ H p) :
    pair p (BinaryNatCode.encode r) ∈ language B H ↔
      ((cannyResultant (node B (child false p)) (node B (child true p)) r).map (Int.castRingHom ℚ)).Separable := by
  have he := polynomial_packet B p r hl hr
  have hn : polynomial B (pair p (BinaryNatCode.encode r)) ≠ 0 := by
    rw [he]
    exact PrimitivePair.integer_resultant_ne_zero _ _ r hsl hsr (IsAlgClosed.splits _) (IsAlgClosed.splits _)
  have hd : (polynomial B (pair p (BinaryNatCode.encode r))).natDegree = (degree ∘ pairFst) (pair p (BinaryNatCode.encode r)) := by
    rw [he, PrimitivePair.resultant_natDegree _ _ r hsl hsr (IsAlgClosed.splits _) (IsAlgClosed.splits _)]
    simp only [Function.comp_apply, pairFst_pair, degree, hl, hr]
  have hb (k : ℕ) : ((polynomial B (pair p (BinaryNatCode.encode r))).coeff k).natAbs ≤
      2 ^ (heightBudget H ∘ pairFst) (pair p (BinaryNatCode.encode r)) := by
    rw [he]
    simpa only [Function.comp_apply, pairFst_pair] using height_at B H p r hcount hl hr hbl hbr k
  have h := SeparableBoundedTest.correct_at (polynomial B) (degree ∘ pairFst) (heightBudget H ∘ pairFst)
    (pair p (BinaryNatCode.encode r)) hn hd hb
  simpa only [language, he] using h

theorem direction_eq_select (B : Family) (H : List Bool → ℕ) (p : List Bool)
    (hl : leftDegree p = (node B (child false p)).natDegree)
    (hr : rightDegree p = (node B (child true p)).natDegree)
    (hsl : ((node B (child false p)).map (Int.castRingHom (AlgebraicClosure ℚ))).Separable)
    (hsr : ((node B (child true p)).map (Int.castRingHom (AlgebraicClosure ℚ))).Separable)
    (hbl : ∀ k, ((node B (child false p)).coeff k).natAbs ≤ 2 ^ H p)
    (hbr : ∀ k, ((node B (child true p)).coeff k).natAbs ≤ 2 ^ H p) :
    direction B H p = PrimitivePair.select (node B (child false p)) (node B (child true p)) := by
  have hc : count p = ((node B (child false p)).natDegree * (node B (child true p)).natDegree) ^ 2 + 1 := by
    simp only [count, degree, hl, hr]
  unfold direction PrimitivePair.select
  rw [hc]
  congr 1
  apply BoundedChoice.search_congr
  intro r hrange
  have hm := member_iff B H p r (by rw [hc]; exact hrange) hl hr hsl hsr hbl hbr
  simpa only [PrimitivePair.candidateLanguage, Set.mem_ofPred_eq, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits] using hm

end LeanCanny.Algebra.BalancedTablePolynomials.Candidate
