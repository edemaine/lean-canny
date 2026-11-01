/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedHeightCellIdentities
public import LeanCanny.Algebra.IntegralMixedHeightIndices
/-! # The explicit integer height formula equals the actual natural matrix entries -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedHeightIntegerNaturalBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedOldHeightBits (bankFamily state)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem guard_of_index (P : Parameters) (q : List Bool)
    (i : Fin (P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q)) + 1)) (hi : i.val = get P .slot8 q)
    (hx : 1 ≤ get P .slot15 q ∧ get P .slot15 q ≤ 4) : IntegralMixedHeightPostBits.guard P (pair q []) := by
  unfold IntegralMixedHeightPostBits.guard
  rw [pairFst_pair]
  refine ⟨?_, hx⟩
  have H : get P .slot8 q < P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q)) + 1 := hi ▸ i.isLt
  rwa [IntegralMixedFullHistoryFamilyBits.saved_root] at H

theorem physical (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (i : Fin (P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q)) + 1)) (hi : i.val = get P .slot8 q)
    (hx : get P .slot15 q = 1) :
    IntegralMixedHeightIntegerBits.value P D q = IntegralMixedHeightNaturalEntries.physical (state P D q)
      ((bankFamily P D).birth_bound (IntegralMixedVirtualTaskBits.saved P q))
      ((IntegralMixedHeightCellsBits.physicalFamily P D).rule (IntegralMixedVirtualTaskBits.saved P q)) i (get P .row q) (get P .col q) := by
  have HG := guard_of_index P q i hi (by rw [hx]; decide)
  have HC : IntegralMixedHeightPostBits.constantBranch P (pair q []) := by
    unfold IntegralMixedHeightPostBits.constantBranch
    rw [pairFst_pair]
    exact Or.inl hx
  rw [IntegralMixedHeightIntegerBits.value, ite_eq_left HG, ite_eq_left HC,
    IntegralMixedHeightCellIdentities.factor_cofactor P D q i hi,
    IntegralMixedHeightCellIdentities.affine_entry P D q i hi, IntegralMixedHeightCellsBits.rule_physical P D q hx,
    IntegralMixedHeightIndexBits.row_physical P D q hx, IntegralMixedHeightIndexBits.col_physical P D q hx,
    IntegralMixedHeightNaturalEntries.physical_eq]

theorem virtual (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (i : Fin (P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q)) + 1)) (hi : i.val = get P .slot8 q)
    (hx : get P .slot15 q ≠ 1) (hs : 1 ≤ get P .slot15 q ∧ get P .slot15 q ≤ 4) :
    IntegralMixedHeightIntegerBits.value P D q = IntegralMixedHeightNaturalEntries.virtual (state P D q)
      ((bankFamily P D).birth_bound (IntegralMixedVirtualTaskBits.saved P q))
      ((bankFamily P D).rule (IntegralMixedVirtualTaskBits.saved P q)) i (get P .row q) (get P .col q) := by
  have HG := guard_of_index P q i hi hs
  have HB : IntegralMixedHeightTableQueryBits.radix P q = 2 ^ (bankFamily P D).width (IntegralMixedVirtualTaskBits.saved P q) := by
    rw [(IntegralMixedFullHistoryFamilyBits.geometry P D).width q]
    rfl
  have HD : (IntegralMixedHeightTableQueryBits.oldRow P q = IntegralMixedHeightTableQueryBits.oldCol P q) ↔
      IntegralMixedHeightNaturalEntries.oldIndex ((bankFamily P D).birth (IntegralMixedVirtualTaskBits.saved P q))
        ((bankFamily P D).width (IntegralMixedVirtualTaskBits.saved P q)) (get P .row q) =
      IntegralMixedHeightNaturalEntries.oldIndex ((bankFamily P D).birth (IntegralMixedVirtualTaskBits.saved P q))
        ((bankFamily P D).width (IntegralMixedVirtualTaskBits.saved P q)) (get P .col q) := by
    rw [← IntegralMixedHeightIndexBits.row_virtual P D q hx, ← IntegralMixedHeightIndexBits.col_virtual P D q hx]
    constructor
    · intro H; exact Fin.ext H
    · intro H; exact congrArg Fin.val H
  rw [IntegralMixedHeightIntegerBits.value, ite_eq_left HG, IntegralMixedHeightCellIdentities.factor_cofactor P D q i hi,
    IntegralMixedHeightCellIdentities.affine_entry P D q i hi, IntegralMixedHeightCellsBits.rule_virtual P D q hx,
    IntegralMixedHeightIndexBits.row_virtual P D q hx, IntegralMixedHeightIndexBits.col_virtual P D q hx,
    IntegralMixedHeightCellIdentities.slope_cell P D q i hi, IntegralMixedHeightNaturalEntries.virtual_eq]
  dsimp only [state, bankFamily, IntegralMixedFullHistoryFamilyBits.family] at *
  simp only [IntegralMixedHeightPostBits.constantBranch, IntegralMixedHeightPostBits.slopeBranch,
    IntegralMixedHeightAffineSumBits.diagonal, pairFst_pair, hx, false_or]
  simp only [HB, HD]
  split_ifs <;> first | omega | ring

theorem invalid (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool)
    (hi : ¬ get P .slot8 q < P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q)) + 1) :
    IntegralMixedHeightIntegerBits.word P D q = [] := by
  have HG : ¬ IntegralMixedHeightPostBits.guard P (pair q []) := by
    intro H
    apply hi
    have HR := H.1
    simpa only [pairFst_pair, IntegralMixedFullHistoryFamilyBits.saved_root] using HR
  rw [IntegralMixedHeightIntegerBits.word, IntegralMixedHeightIntegerBits.value, ite_eq_right HG, Int.cast_zero]
  exact (MatrixPower.ArithmeticBits.zero_residueBits _).symm

end LeanCanny.Algebra.IntegralMixedHeightIntegerNaturalBits
