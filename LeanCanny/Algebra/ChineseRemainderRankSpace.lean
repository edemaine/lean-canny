/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.ChineseRemainderDigits
public import LeanCanny.Algebra.DyadicSumSpace

/-!
# Certified bit access to the CRT correction rank

The rank is the high part of the truncated quotient sum. Reading its bit `k`
therefore reads sum bit `precision+k`; the existing space-bounded sum-bit machine
composes all local preparation calls through the native space interface.
-/

@[expose] public section

namespace LeanCanny.Algebra.ChineseRemainder

open LeanCanny.Encoding
open LeanCanny.Computation
open scoped BigOperators

def rankIndex (precision index : List Bool → List Bool) (c : List Bool) : List Bool :=
  BinaryNat.add (pair (precision c) (index c))

theorem rankIndex_mem_FP {precision index : List Bool → List Bool} (hp : precision ∈ FP) (hi : index ∈ FP) :
    rankIndex precision index ∈ FP := by
  have he := mem_FP_comp (mem_FP_pair hp hi) BinaryNat.add_mem_FP
  refine mem_FP_of_eq (g := rankIndex precision index) he ?_
  intro c
  simp only [Function.comp_apply, rankIndex]

theorem rankIndex_value (precision index : List Bool → List Bool) (c : List Bool) :
    Nat.fromBitsLE (rankIndex precision index c) = Nat.fromBitsLE (precision c) + Nat.fromBitsLE (index c) := by
  simp only [rankIndex, BinaryNat.add_pair, Nat.fromBitsLE_bits]

theorem rankBitEvaluator {f : List Bool → List Bool} (E : SpaceFunction f)
    (count precision index : List Bool → List Bool) (hc : count ∈ FP) (hp : precision ∈ FP) (hi : index ∈ FP)
    (F : (c : List Bool) → System (Fin (Nat.fromBitsLE (count c))))
    (r : (c : List Bool) → Fin (Nat.fromBitsLE (count c)) → ℕ)
    (hprecision : ∀ c, Nat.fromBitsLE (count c) * (F c).product < 2 ^ Nat.fromBitsLE (precision c))
    (hprep : ∀ c (i : Fin (Nat.fromBitsLE (count c))),
      f (pair c (BinaryNatCode.encode i.val)) =
        pair (BinaryNatCode.encode ((F c).numerator (r c) i)) (BinaryNatCode.encode ((F c).modulus i - 1))) :
    SpaceFunction (fun c => if ((F c).integerSum (r c) / (F c).product).testBit (Nat.fromBitsLE (index c))
      then [true] else []) := by
  let A := fun c i => if h : i < Nat.fromBitsLE (count c) then (F c).numerator (r c) ⟨i, h⟩ else 0
  let M := fun c i => if h : i < Nat.fromBitsLE (count c) then (F c).modulus ⟨i, h⟩ else 1
  have hprep' : ∀ c i, i < Nat.fromBitsLE (count c) →
      f (pair c (BinaryNatCode.encode i)) = pair (BinaryNatCode.encode (A c i)) (BinaryNatCode.encode (M c i - 1)) := by
    intro c i hiN
    simpa only [A, M, dite_eq_left hiN] using hprep c ⟨i, hiN⟩
  have hm : ∀ c i, i < Nat.fromBitsLE (count c) → 0 < M c i := by
    intro c i hiN
    simpa only [M, dite_eq_left hiN] using (F c).positive ⟨i, hiN⟩
  have ha : ∀ c i, i < Nat.fromBitsLE (count c) → A c i < M c i := by
    intro c i hiN
    simpa only [A, M, dite_eq_left hiN] using (F c).numerator_lt (r c) ⟨i, hiN⟩
  have E' := DyadicSumBits.evaluator E count precision (rankIndex precision index) hc hp
    (rankIndex_mem_FP hp hi) A M hprep' hm ha
  refine E'.congr (funext fun c => ?_)
  have hsum : (∑ i ∈ Finset.range (Nat.fromBitsLE (count c)),
      2 ^ Nat.fromBitsLE (precision c) * A c i / M c i) =
      (F c).truncatedSum (r c) (2 ^ Nat.fromBitsLE (precision c)) := by
    rw [Finset.sum_range]
    unfold System.truncatedSum
    apply Finset.sum_congr rfl
    intro i _
    simp only [A, M, dite_eq_left i.is_lt]
  have hrank := (F c).truncatedRank_eq (r c) (2 ^ Nat.fromBitsLE (precision c))
    (by positivity) (by simpa only [Fintype.card_fin] using hprecision c)
  rw [hsum, rankIndex_value, Nat.add_comm (Nat.fromBitsLE (precision c)), ← Nat.testBit_div_two_pow, hrank]

theorem rankBitEvaluatorOfCount {f : List Bool → List Bool} (E : SpaceFunction f)
    (count precision index : List Bool → List Bool) (hc : count ∈ FP) (hp : precision ∈ FP) (hi : index ∈ FP)
    (N : List Bool → ℕ) (hcount : ∀ c, Nat.fromBitsLE (count c) = N c)
    (F : (c : List Bool) → System (Fin (N c))) (r : (c : List Bool) → Fin (N c) → ℕ)
    (hprecision : ∀ c, N c * (F c).product < 2 ^ Nat.fromBitsLE (precision c))
    (hprep : ∀ c (i : Fin (N c)), f (pair c (BinaryNatCode.encode i.val)) =
      pair (BinaryNatCode.encode ((F c).numerator (r c) i)) (BinaryNatCode.encode ((F c).modulus i - 1))) :
    SpaceFunction (fun c => if ((F c).integerSum (r c) / (F c).product).testBit (Nat.fromBitsLE (index c))
      then [true] else []) := by
  have he : (fun c => Nat.fromBitsLE (count c)) = N := funext hcount
  subst N
  exact rankBitEvaluator E count precision index hc hp hi F r hprecision hprep

end LeanCanny.Algebra.ChineseRemainder
