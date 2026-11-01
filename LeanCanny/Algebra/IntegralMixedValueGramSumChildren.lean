/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedValueGramSumSource

/-! # Each emitted Gram term uses the exact parent factors -/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueGramSumChildren
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits IntegralMixedVirtualCaps IntegralMixedValueGramSumTasks
open scoped Classical

theorem programCount_le (P : Parameters) (F : Family) (q : List Bool) :
    IntegralMixedValueGramSumSource.programCount P F q ≤ count P F q := by
  unfold IntegralMixedValueGramSumSource.programCount
  split
  · exact le_rfl
  · exact Nat.zero_le _

theorem product_value (P : Parameters) (F : Family) (q : List Bool) (k : ℕ)
    (hk : k ≤ numericCap P (RankedHistoryTask.root q)) :
    IntegralMixedValueGramProductNative.value P F (query P (pair q (BinaryNatCode.encode k))) =
      residueBits (IntegralMixedValueGramSumSource.summand P F q k : ZMod (modulus P q)) := by
  have HI :
      -(IntegralMixedValueGramProductNative.factor P F true (query P (pair q (BinaryNatCode.encode k))) *
        IntegralMixedValueGramProductNative.factor P F false (query P (pair q (BinaryNatCode.encode k)))) =
          IntegralMixedValueGramSumSource.summand P F q k := by
    simp only [IntegralMixedValueGramProductNative.factor, query_saved,
      IntegralMixedValueGramProductTasks.column, IntegralMixedValueGramProductTasks.row,
      IntegralMixedValueGramProductTasks.col, IntegralMixedValueGramProductTasks.sourceRow,
      IntegralMixedValueGramProductTasks.middle, query_get P q k hk, reduceCtorEq, ite_false, ite_true,
      Bool.false_eq_true, rank_query, IntegralMixedValueGramSumSource.summand]
  unfold IntegralMixedValueGramProductNative.value
  rw [HI]
  exact congrArg (fun m : ℕ => residueBits (IntegralMixedValueGramSumSource.summand P F q k : ZMod m))
    (query_modulus P q k)

abbrev RepliesAt (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q : List Bool) : Prop :=
  ∀ k < IntegralMixedValueGramSumSource.programCount P F q,
    reply (query P (pair q (BinaryNatCode.encode k))) =
      IntegralMixedValueGramProductNative.value P F (query P (pair q (BinaryNatCode.encode k)))

theorem reply_value (P : Parameters) (F : Family) (g : RootGeometry P F)
    (reply : List Bool → List Bool) (q : List Bool) (hv : valid P q) (he : RepliesAt P F reply q)
    (k : ℕ) (hk : k < IntegralMixedValueGramSumSource.programCount P F q) :
    reply (query P (pair q (BinaryNatCode.encode k))) =
      residueBits (IntegralMixedValueGramSumSource.summand P F q k : ZMod (modulus P q)) :=
  (he k hk).trans (product_value P F q k
    (hk.le.trans ((programCount_le P F q).trans (count_cap P F g q hv))))

end LeanCanny.Algebra.IntegralMixedValueGramSumChildren
