/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegerCharacteristicSpace
public import LeanCanny.Algebra.LowestCoefficientSpace
public import LeanCanny.Computation.SpaceDeciderFunction

/-! # Native trailing-degree scans for integer matrix characteristic polynomials

A binary dimension, a uniform coefficient-bit allowance, and original modular
entry access suffice. Every coefficient and residue scan is included in the
space bound; no rank or zero-coefficient oracle is supplied.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegerMatrixTrailingBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Berkowitz
open scoped Classical

noncomputable def indexed (F : IntegerFamily) : IntegerFamily where
  dimension q := F.dimension (pairFst q)
  matrix q := F.matrix (pairFst q)
  budget q := F.budget (pairFst q)
  determinant_bits q := F.determinant_bits (pairFst q)

theorem canonical_entry {F : IntegerFamily} (a : IntegerAccess F) (c m : List Bool)
    (i j : Fin (F.dimension c)) :
    a.entry (pair (pair c m) (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
      residueBits ((F.matrix c i j : ℤ) : ZMod (Nat.fromBitsLE m + 1)) := by
  generalize hq : pair c m = q
  have hc : pairFst q = c := by rw [← hq, pairFst_pair]
  have hm : pairSnd q = m := by rw [← hq, pairSnd_pair]
  subst c
  subst m
  exact a.entry_eq q i j

def sourceQuery (p : List Bool) : List Bool :=
  pair (pair (pairFst (pairFst (pairFst p))) (pairSnd (pairFst p))) (pairSnd p)
theorem sourceQuery_FP : sourceQuery ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp (mem_FP_comp pairFst_mem_FP pairFst_mem_FP) pairFst_mem_FP)
    (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)) pairSnd_mem_FP

noncomputable def access {F : IntegerFamily} (a : IntegerAccess F) : IntegerAccess (indexed F) where
  dimension := a.dimension ∘ pairFst
  budget := a.budget ∘ pairFst
  entry := a.entry ∘ sourceQuery
  dimension_eq q := a.dimension_eq (pairFst q)
  budget_eq q := a.budget_eq (pairFst q)
  entry_eq q i j := by
    simp only [Function.comp_apply, sourceQuery, pairFst_pair, pairSnd_pair]
    exact canonical_entry a (pairFst (pairFst q)) (pairSnd q) i j

theorem controls {F : IntegerFamily} (a : IntegerAccess F) (ha : a.ControlsPolyTime) :
    (access a).ControlsPolyTime := by
  have hD := mem_FP_comp pairFst_mem_FP ha.dimension
  have hB := mem_FP_comp pairFst_mem_FP ha.budget
  exact ⟨hD, hB⟩

noncomputable def polynomial (F : IntegerFamily) (c : List Bool) : Polynomial ℤ := (F.matrix c).charpoly

theorem coefficientZero {F : IntegerFamily} (a : IntegerAccess F) (ha : a.ControlsPolyTime)
    (E : SpaceFunction a.entry) {budget : List Bool → ℕ} (hb : BinaryFn budget)
    (hbudget : ∀ c k, ((F.matrix c).charpoly.coeff k).natAbs.size ≤ budget c) :
    SpaceDecider {q | (polynomial F (pairFst q)).coeff (Nat.fromBitsLE (pairSnd q)) = 0} := by
  have Q := E.precompose sourceQuery sourceQuery_FP
  have hB := BinaryFn.bits_mem_FP (hb.comp pairFst_mem_FP)
  exact IntegerCharacteristicBits.zeroDecider (access a) (controls a ha) Q pairSnd_mem_FP hB
    (by
      intro q
      change ((F.matrix (pairFst q)).charpoly.coeff (Nat.fromBitsLE (pairSnd q))).natAbs.size ≤
        Nat.fromBitsLE (BinaryNatCode.encode (budget (pairFst q)))
      rw [show Nat.fromBitsLE (BinaryNatCode.encode (budget (pairFst q))) = budget (pairFst q) from Nat.fromBitsLE_bits _]
      exact hbudget (pairFst q) (Nat.fromBitsLE (pairSnd q)))

attribute [local irreducible] polynomial

theorem evaluator {F : IntegerFamily} (a : IntegerAccess F) (ha : a.ControlsPolyTime)
    (E : SpaceFunction a.entry) {budget : List Bool → ℕ} (hb : BinaryFn budget)
    (hbudget : ∀ c k, ((F.matrix c).charpoly.coeff k).natAbs.size ≤ budget c) :
    SpaceFunction (fun c => BinaryNatCode.encode (polynomial F c).natTrailingDegree) := by
  have D := coefficientZero a ha E hb hbudget
  apply LowestCoefficientBits.evaluator D.flagEvaluator a.dimension ha.dimension (polynomial F)
  · intro c
    rw [a.dimension_eq, BinaryNatCode.encode, Nat.fromBitsLE_bits, polynomial, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin]
  · intro c k
    simp only [Set.mem_ofPred_eq, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
    by_cases hz : (polynomial F c).coeff k = 0 <;> simp [hz]

end LeanCanny.Algebra.IntegerMatrixTrailingBits
