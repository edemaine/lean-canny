/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedValueGramSumTasks

/-! # The guarded finite sum is the actual negative Gram entry -/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedValueGramSumSource
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits
open scoped Classical BigOperators
attribute [local irreducible] IntegralMixedValueDoubleNilpotent.basis

noncomputable abbrev columns (P : Parameters) (F : Family) (q : List Bool) :=
  IntegralMixedValueMacaulayMatrix.columns (IntegralMixedVirtualTaskBits.family P F) q
noncomputable abbrev rank (P : Parameters) (F : Family) (q : List Bool) := IntegralMixedValueGramProductTasks.rank P F q
def Labels (P : Parameters) (F : Family) (q : List Bool) : Prop :=
  get P .slot8 q < columns P F q ∧ get P .slot9 q < columns P F q ∧
    get P .row q < rank P F q ∧ get P .col q < rank P F q
noncomputable instance (P : Parameters) (F : Family) (q : List Bool) : Decidable (Labels P F q) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem columns_binary (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : BinaryFn (columns P F) :=
  IntegralMixedValueDeterminantMetadata.columns_binary _ _ (IntegralMixedVirtualTaskBits.metadata P a F h)
theorem labels_FP (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : FPPred (Labels P F) :=
  ((get_binary P a .slot8).lt (columns_binary P a F h)).and
    (((get_binary P a .slot9).lt (columns_binary P a F h)).and
      (((get_binary P a .row).lt (IntegralMixedValueGramProductTasks.rank_binary P a F h)).and
        ((get_binary P a .col).lt (IntegralMixedValueGramProductTasks.rank_binary P a F h))))

noncomputable def entry (P : Parameters) (F : Family) (q : List Bool)
    (i j : Fin (columns P F q)) (r t : Fin (rank P F q)) : ℤ :=
  Algebra.leftMulMatrix (IntegralMixedValueDoubleNilpotent.basis ((IntegralMixedVirtualTaskBits.family P F).state q))
    (-ProjectiveGramEliminant.gram (IntegralMixedValueGramEntry.rectangular (IntegralMixedVirtualTaskBits.family P F)
      (IntegralMixedVirtualTaskBits.indices P F) q) i j) r t
noncomputable def totalEntry (P : Parameters) (F : Family) (q : List Bool) : ℤ :=
  if H : Labels P F q then entry P F q ⟨get P .slot8 q, H.1⟩ ⟨get P .slot9 q, H.2.1⟩
    ⟨get P .row q, H.2.2.1⟩ ⟨get P .col q, H.2.2.2⟩ else 0
noncomputable def value (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  residueBits (totalEntry P F q : ZMod (modulus P q))

noncomputable def programCount (P : Parameters) (F : Family) (q : List Bool) : ℕ :=
  if Labels P F q then IntegralMixedValueGramSumTasks.count P F q else 0
theorem programCount_binary (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : BinaryFn (programCount P F) :=
  BinaryFn.ite (labels_FP P a F h) (IntegralMixedValueGramSumTasks.count_binary P a F h) (BinaryFn.const 0)

noncomputable def summand (P : Parameters) (F : Family) (q : List Bool) (k : ℕ) : ℤ :=
  -(IntegralMixedValueMacaulaySnapshot.pointAt F (IntegralMixedVirtualTaskBits.saved P q) (get P .slot13 q)
      (k / rank P F q) (get P .slot8 q) (get P .row q) (k % rank P F q) *
    IntegralMixedValueMacaulaySnapshot.pointAt F (IntegralMixedVirtualTaskBits.saved P q) (get P .slot13 q)
      (k / rank P F q) (get P .slot9 q) (k % rank P F q) (get P .col q))

theorem summand_finite (P : Parameters) (F : Family) (q : List Bool)
    (i j : Fin (columns P F q)) (r t : Fin (rank P F q))
    (hi : get P .slot8 q = i.val) (hj : get P .slot9 q = j.val)
    (hr : get P .row q = r.val) (ht : get P .col q = t.val)
    (k : Fin (IntegralMixedValueGramSumTasks.count P F q)) :
    summand P F q k.val =
      -(IntegralMixedValueMacaulayMatrix.entry (IntegralMixedVirtualTaskBits.family P F) (IntegralMixedVirtualTaskBits.indices P F)
          q k.divNat i r k.modNat *
        IntegralMixedValueMacaulayMatrix.entry (IntegralMixedVirtualTaskBits.family P F) (IntegralMixedVirtualTaskBits.indices P F)
          q k.divNat j k.modNat t) := by
  unfold summand
  rw [hi, hj, hr, ht]
  have HL := IntegralMixedValueMacaulaySnapshot.parent_entry P F q k.divNat i r k.modNat
  have HR := IntegralMixedValueMacaulaySnapshot.parent_entry P F q k.divNat j k.modNat t
  exact congrArg₂ (fun x y : ℤ => -(x * y)) HL HR

theorem sum_eq (P : Parameters) (F : Family) (q : List Bool) :
    ∑ k ∈ Finset.range (programCount P F q), summand P F q k = totalEntry P F q := by
  by_cases H : Labels P F q
  · rw [programCount, ite_eq_left H, totalEntry, dite_eq_left H]
    let i : Fin (columns P F q) := ⟨get P .slot8 q, H.1⟩
    let j : Fin (columns P F q) := ⟨get P .slot9 q, H.2.1⟩
    let r : Fin (rank P F q) := ⟨get P .row q, H.2.2.1⟩
    let t : Fin (rank P F q) := ⟨get P .col q, H.2.2.2⟩
    rw [← Fin.sum_univ_eq_sum_range]
    have HM := NegativeGramEntryRequest.matrix_entry
      (IntegralMixedValueDoubleNilpotent.basis ((IntegralMixedVirtualTaskBits.family P F).state q))
      (IntegralMixedValueGramEntry.rectangular (IntegralMixedVirtualTaskBits.family P F)
        (IntegralMixedVirtualTaskBits.indices P F) q) i j r t
    refine Eq.trans ?_ HM.symm
    apply Finset.sum_congr rfl
    intro k _
    exact summand_finite P F q i j r t rfl rfl rfl rfl k
  · rw [programCount, ite_eq_right H, totalEntry, dite_eq_right H]
    simp only [Finset.range_zero, Finset.sum_empty]

theorem entry_source (P : Parameters) (F : Family)
    (index : ∀ q, Fin (IntegralMixedValueTrailing.ChoiceBound ((IntegralMixedVirtualTaskBits.family P F).spatial q)
      ((IntegralMixedVirtualTaskBits.family P F).rule q))) (q : List Bool)
    (i j : Fin (columns P F q)) (r t : Fin (rank P F q)) :
    entry P F q i j r t =
      (IntegralMixedValueDeterminantSource.source (IntegralMixedVirtualTaskBits.family P F)
        (IntegralMixedVirtualTaskBits.indices P F) index).entryMatrix q i j r t :=
  (IntegralMixedValueGramEntry.source_entry _ _ index q i j r t).symm

end LeanCanny.Algebra.IntegralMixedValueGramSumSource
