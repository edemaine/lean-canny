/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BalancedProductSpace
public import LeanCanny.Computation.SpaceFunctionBranch

/-!
# Finite product and cofactor bits in polynomial space

FP tests replace padding and omitted leaves by one. Factor-bit correctness is
required only at retained indices. The count stays binary, so the family may
have exponentially many factors. Empty products and out-of-range omissions are
included in the same evaluator.
-/

@[expose] public section

namespace LeanCanny.Algebra.BalancedProduct

open LeanCanny.Encoding
open LeanCanny.Encoding.Brackets
open LeanCanny.Computation
open scoped BigOperators

def factorQuery (p : List Bool) : List Bool := pair (pairFst p) (pairFst (pairSnd p))
def oneBit (p : List Bool) : List Bool := if pairSnd (pairSnd p) = [] then [true] else []
def maskedLeaf (keep : List Bool → Bool) (f : List Bool → List Bool) (p : List Bool) : List Bool :=
  if keep (factorQuery p) then f p else oneBit p

theorem factorQuery_mem_FP : factorQuery ∈ FP :=
  mem_FP_pair pairFst_mem_FP (mem_FP_comp pairSnd_mem_FP pairFst_mem_FP)
theorem oneBit_mem_FP : oneBit ∈ FP :=
  (stringEq_fppred (mem_FP_comp pairSnd_mem_FP pairSnd_mem_FP) (constFn_mem_FP [])).ite_mem_FP
    (constFn_mem_FP [true]) (constFn_mem_FP [])

theorem oneBit_packet (c : List Bool) (i k : ℕ) :
    (oneBit (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))))[0]?.getD false =
      (1 : ℕ).testBit k := by
  apply Bool.eq_iff_iff.mpr
  simp only [oneBit, pairSnd_pair, Controller.code_eq_nil, Nat.testBit_one_eq_true_iff_self_eq_zero]
  by_cases hk : k = 0 <;> simp [hk]

theorem maskedLeafEvaluator {f : List Bool → List Bool} (E : SpaceFunction f)
    (keep : List Bool → Bool) (hk : (fun z => [keep z]) ∈ FP) : SpaceFunction (maskedLeaf keep f) :=
  SpaceFunction.branch (keep ∘ factorQuery) (mem_FP_comp factorQuery_mem_FP hk) E
    (SpaceFunction.ofFP oneBit oneBit_mem_FP)

theorem maskedTreeEvaluator {f : List Bool → List Bool} (E : SpaceFunction f)
    (count index : List Bool → List Bool) (hc : count ∈ FP) (hi : index ∈ FP)
    (keep : List Bool → Bool) (hk : (fun z => [keep z]) ∈ FP)
    (g : List Bool → ℕ → Bool) (a : List Bool → ℕ → ℕ)
    (hkeep : ∀ c i, keep (pair c (BinaryNatCode.encode i)) = g c i)
    (hbits : ∀ c i k, g c i = true →
      (f (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))))[0]?.getD false = (a c i).testBit k) :
    SpaceFunction (treeValue count index (fun c i => if g c i then a c i else 1)) := by
  refine treeEvaluator (maskedLeafEvaluator E keep hk) count index hc hi _ ?_
  intro c i k
  simp only [maskedLeaf, factorQuery, pairFst_pair, pairSnd_pair, hkeep]
  cases hg : g c i with
  | false => simpa only [Bool.false_eq_true, ↓reduceIte] using oneBit_packet c i k
  | true => simpa only [↓reduceIte] using hbits c i k hg

def inside (count : List Bool → List Bool) (z : List Bool) : Bool :=
  decide (Nat.fromBitsLE (pairSnd z) < Nat.fromBitsLE (count (pairFst z)))
def retained (count skip : List Bool → List Bool) (z : List Bool) : Bool :=
  decide (Nat.fromBitsLE (pairSnd z) < Nat.fromBitsLE (count (pairFst z)) ∧
    Nat.fromBitsLE (pairSnd z) ≠ Nat.fromBitsLE (skip (pairFst z)))

theorem inside_mem_FP {count : List Bool → List Bool} (hc : count ∈ FP) :
    (fun z => [inside count z]) ∈ FP :=
  (BinaryNat.lt_fppred pairSnd_mem_FP (mem_FP_comp pairFst_mem_FP hc)).flag_mem_FP

theorem retained_mem_FP {count skip : List Bool → List Bool} (hc : count ∈ FP) (hs : skip ∈ FP) :
    (fun z => [retained count skip z]) ∈ FP := by
  have hn := mem_FP_comp pairFst_mem_FP hc
  have ht := mem_FP_comp pairFst_mem_FP hs
  have hne := (BinaryNat.eq_fppred pairSnd_mem_FP ht).not
  have hp := (BinaryNat.lt_fppred pairSnd_mem_FP hn).and hne
  have he : FPPred (fun z => Nat.fromBitsLE (pairSnd z) < Nat.fromBitsLE (count (pairFst z)) ∧
      Nat.fromBitsLE (pairSnd z) ≠ Nat.fromBitsLE (skip (pairFst z))) := by
    refine hp.of_iff (fun z => ?_)
    dsimp only [Function.comp_apply]
    omega
  exact he.flag_mem_FP

def value (count index : List Bool → List Bool) (a : List Bool → ℕ → ℕ) (c : List Bool) : List Bool :=
  if (∏ i ∈ Finset.range (Nat.fromBitsLE (count c)), a c i).testBit (Nat.fromBitsLE (index c)) then [true] else []

def cofactorValue (count skip index : List Bool → List Bool) (a : List Bool → ℕ → ℕ) (c : List Bool) : List Bool :=
  if (∏ i ∈ (Finset.range (Nat.fromBitsLE (count c))).erase (Nat.fromBitsLE (skip c)), a c i).testBit
    (Nat.fromBitsLE (index c)) then [true] else []

theorem evaluator {f : List Bool → List Bool} (E : SpaceFunction f)
    (count index : List Bool → List Bool) (hc : count ∈ FP) (hi : index ∈ FP)
    (a : List Bool → ℕ → ℕ)
    (hbits : ∀ c i k, i < Nat.fromBitsLE (count c) →
      (f (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))))[0]?.getD false = (a c i).testBit k) :
    SpaceFunction (value count index a) := by
  have E' := maskedTreeEvaluator E count index hc hi (inside count) (inside_mem_FP hc)
    (fun c i => decide (i < Nat.fromBitsLE (count c))) a
    (by intro c i; simp [inside]) (fun c i k h => hbits c i k (of_decide_eq_true h))
  refine E'.congr (funext fun c => ?_)
  simp only [treeValue, decide_eq_true_eq]
  change (if (tree (padded (a c) (Nat.fromBitsLE (count c))) (count c).length 0).testBit
    (Nat.fromBitsLE (index c)) then [true] else []) = _
  rw [tree_padded_of_bits]
  rfl

theorem cofactorEvaluator {f : List Bool → List Bool} (E : SpaceFunction f)
    (count skip index : List Bool → List Bool) (hc : count ∈ FP) (hs : skip ∈ FP) (hi : index ∈ FP)
    (a : List Bool → ℕ → ℕ)
    (hbits : ∀ c i k, i < Nat.fromBitsLE (count c) → i ≠ Nat.fromBitsLE (skip c) →
      (f (pair c (pair (BinaryNatCode.encode i) (BinaryNatCode.encode k))))[0]?.getD false = (a c i).testBit k) :
    SpaceFunction (cofactorValue count skip index a) := by
  have E' := maskedTreeEvaluator E count index hc hi (retained count skip) (retained_mem_FP hc hs)
    (fun c i => decide (i < Nat.fromBitsLE (count c) ∧ i ≠ Nat.fromBitsLE (skip c))) a
    (by intro c i; simp [retained]) (by
      intro c i k h
      have hp := of_decide_eq_true h
      exact hbits c i k hp.1 hp.2)
  refine E'.congr (funext fun c => ?_)
  simp only [treeValue, decide_eq_true_eq]
  change (if (tree (omitted (a c) (Nat.fromBitsLE (count c)) (Nat.fromBitsLE (skip c)))
    (count c).length 0).testBit (Nat.fromBitsLE (index c)) then [true] else []) = _
  rw [tree_omitted_of_bits]
  rfl

end LeanCanny.Algebra.BalancedProduct
