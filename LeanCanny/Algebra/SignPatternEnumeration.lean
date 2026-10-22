/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.SignPatternSource

/-! # Ternary enumeration agrees with the scaled sign-pattern count -/

@[expose] public section

namespace LeanCanny.Algebra.SignPatternBits
open Polynomial

open LeanCanny.Encoding
open scoped BigOperators

theorem enumerated_exponent (k : ℕ) (j : Fin (3 ^ k)) (i : Fin k) :
    Ternary.exponent k j.val i.val = (finFunctionFinEquiv (m := 3) (n := k)).symm j i := by
  rw [Ternary.exponent_fin]
  exact congrFun (Ternary.vector_eq_symm k j) i

theorem enumerated_product (F : Family) (c : List Bool) (j : Fin (3 ^ Nat.fromBitsLE (F.count c))) :
    (queryFamily F).product (pair c (BinaryNatCode.encode j.val)) =
      RootSignQueries.queryPolynomial (fun i : Fin (Nat.fromBitsLE (F.count c)) => F.polynomial c i.val)
        ((finFunctionFinEquiv (m := 3) (n := Nat.fromBitsLE (F.count c))).symm j) := by
  simp only [SignQueryBits.Family.product, queryFamily, Function.comp_apply, pairFst_pair, pairSnd_pair,
    BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [← Fin.prod_univ_eq_prod_range
    (fun i => F.polynomial c i ^ (Ternary.exponent (Nat.fromBitsLE (F.count c)) j.val i).val)]
  unfold RootSignQueries.queryPolynomial
  apply Finset.prod_congr rfl
  intro i _
  rw [enumerated_exponent]

theorem enumerated_weight (F : Family) (c : List Bool) (j : Fin (3 ^ Nat.fromBitsLE (F.count c))) :
    weight F (pair c (BinaryNatCode.encode j.val)) =
      RootSignQueries.patternWeight (fun i : Fin (Nat.fromBitsLE (F.count c)) => F.pattern c i.val)
        ((finFunctionFinEquiv (m := 3) (n := Nat.fromBitsLE (F.count c))).symm j) := by
  simp only [weight, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  rw [← Fin.prod_univ_eq_prod_range
    (fun i => RootSignQueries.weight (F.pattern c i) (Ternary.exponent (Nat.fromBitsLE (F.count c)) j.val i))]
  unfold RootSignQueries.patternWeight
  apply Finset.prod_congr rfl
  intro i _
  rw [enumerated_exponent]

theorem enumerated_query (F : Family) (c : List Bool) (j : Fin (3 ^ Nat.fromBitsLE (F.count c))) :
    (queryFamily F).value (pair c (BinaryNatCode.encode j.val)) = RootSignQueries.tarskiQuery
      ((F.root c).map (algebraMap ℤ ℝ))
      (RootSignQueries.queryPolynomial
        (fun i : Fin (Nat.fromBitsLE (F.count c)) => (F.polynomial c i.val).map (algebraMap ℤ ℝ))
        ((finFunctionFinEquiv (m := 3) (n := Nat.fromBitsLE (F.count c))).symm j)) := by
  rw [SignQueryBits.Family.value]
  have hr : (queryFamily F).root (pair c (BinaryNatCode.encode j.val)) = F.root c := by
    simp only [queryFamily, Function.comp_apply, pairFst_pair]
  rw [hr, enumerated_product, RootSignQueries.map_queryPolynomial]

noncomputable def summand (F : Family) (q : List Bool) : ℤ := weight F q * (queryFamily F).value q

theorem sum_eq_scaledCount (F : Family) (c : List Bool) :
    (∑ j ∈ Finset.range (3 ^ Nat.fromBitsLE (F.count c)), summand F (pair c (BinaryNatCode.encode j))) = scaledCount F c := by
  classical
  rw [← Fin.sum_univ_eq_sum_range (fun j => summand F (pair c (BinaryNatCode.encode j)))]
  simp only [summand, enumerated_weight, enumerated_query]
  have h := Equiv.sum_comp (finFunctionFinEquiv (m := 3) (n := Nat.fromBitsLE (F.count c))).symm
    (fun e : Fin (Nat.fromBitsLE (F.count c)) → Fin 3 =>
      RootSignQueries.patternWeight (fun i => F.pattern c i.val) e *
        RootSignQueries.tarskiQuery ((F.root c).map (algebraMap ℤ ℝ))
          (RootSignQueries.queryPolynomial (fun i => (F.polynomial c i.val).map (algebraMap ℤ ℝ)) e))
  refine h.trans ?_
  unfold scaledCount RootSignQueries.scaledRootCount
  apply Finset.sum_congr
  · ext e
    simp only [Finset.mem_univ]
  · intro e _
    rfl

end LeanCanny.Algebra.SignPatternBits
