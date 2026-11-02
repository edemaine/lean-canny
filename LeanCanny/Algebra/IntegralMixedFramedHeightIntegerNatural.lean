/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedHeightCellIdentities
public import LeanCanny.Algebra.IntegralMixedFramedHeightIndices
/-! # The explicit integer height formula equals the actual natural matrix entries -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedHeightIntegerNaturalBits
open LeanCanny.Encoding LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedOldHeightBits (bankFamily state)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem guard_of_index (P : Parameters) (q : List Bool)
    (i : Fin (P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q)) + 1)) (hi : i.val = get P .slot8 q)
    (hx : 1 ≤ get P .slot15 q ∧ get P .slot15 q ≤ 4) : IntegralMixedFramedHeightPostBits.guard P (pair q []) := by
  unfold IntegralMixedFramedHeightPostBits.guard
  rw [pairFst_pair]
  refine ⟨?_, hx⟩
  have H : get P .slot8 q < P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q)) + 1 := hi ▸ i.isLt
  rwa [IntegralMixedFullHistoryFamilyBits.saved_root] at H

theorem physical (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool)
    (i : Fin (P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q)) + 1)) (hi : i.val = get P .slot8 q)
    (hx : get P .slot15 q = 1) :
    IntegralMixedFramedHeightIntegerBits.value P D J q = IntegralMixedHeightNaturalEntries.physical (state P D J q)
      ((bankFamily P D J).birth_bound (IntegralMixedVirtualTaskBits.saved P q))
      ((IntegralMixedFramedScalarCellsBits.physicalFamily P D J).rule (IntegralMixedVirtualTaskBits.saved P q)) i (get P .row q) (get P .col q) := by
  have HG := guard_of_index P q i hi (by rw [hx]; decide)
  have HC : IntegralMixedFramedHeightPostBits.constantBranch P (pair q []) := by
    unfold IntegralMixedFramedHeightPostBits.constantBranch
    rw [pairFst_pair]
    exact Or.inl hx
  rw [IntegralMixedFramedHeightIntegerBits.value, ite_eq_left HG, ite_eq_left HC,
    IntegralMixedFramedHeightCellIdentities.factor_cofactor P D J q i hi,
    IntegralMixedFramedHeightCellIdentities.affine_entry P D J q i hi, IntegralMixedFramedScalarCellsBits.rule_physical P D J q hx,
    IntegralMixedFramedHeightIndexBits.row_physical P D J q hx, IntegralMixedFramedHeightIndexBits.col_physical P D J q hx,
    IntegralMixedHeightNaturalEntries.physical_eq]

theorem virtual (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool)
    (i : Fin (P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q)) + 1)) (hi : i.val = get P .slot8 q)
    (hx : get P .slot15 q ≠ 1) (hs : 1 ≤ get P .slot15 q ∧ get P .slot15 q ≤ 4) :
    IntegralMixedFramedHeightIntegerBits.value P D J q = IntegralMixedHeightNaturalEntries.virtual (state P D J q)
      ((bankFamily P D J).birth_bound (IntegralMixedVirtualTaskBits.saved P q))
      ((bankFamily P D J).rule (IntegralMixedVirtualTaskBits.saved P q)) i (get P .row q) (get P .col q) := by
  have HG := guard_of_index P q i hi hs
  have HB : IntegralMixedHeightTableQueryBits.radix P q = 2 ^ (bankFamily P D J).width (IntegralMixedVirtualTaskBits.saved P q) := by
    rw [(IntegralMixedFramedHistoryFamilyBits.geometry P D J).width q]
    rfl
  have HD : (IntegralMixedHeightTableQueryBits.oldRow P q = IntegralMixedHeightTableQueryBits.oldCol P q) ↔
      IntegralMixedHeightNaturalEntries.oldIndex ((bankFamily P D J).birth (IntegralMixedVirtualTaskBits.saved P q))
        ((bankFamily P D J).width (IntegralMixedVirtualTaskBits.saved P q)) (get P .row q) =
      IntegralMixedHeightNaturalEntries.oldIndex ((bankFamily P D J).birth (IntegralMixedVirtualTaskBits.saved P q))
        ((bankFamily P D J).width (IntegralMixedVirtualTaskBits.saved P q)) (get P .col q) := by
    rw [← IntegralMixedFramedHeightIndexBits.row_virtual P D J q hx, ← IntegralMixedFramedHeightIndexBits.col_virtual P D J q hx]
    constructor
    · intro H; exact Fin.ext H
    · intro H; exact congrArg Fin.val H
  rw [IntegralMixedFramedHeightIntegerBits.value, ite_eq_left HG, IntegralMixedFramedHeightCellIdentities.factor_cofactor P D J q i hi,
    IntegralMixedFramedHeightCellIdentities.affine_entry P D J q i hi, IntegralMixedFramedScalarCellsBits.rule_virtual P D J q hx,
    IntegralMixedFramedHeightIndexBits.row_virtual P D J q hx, IntegralMixedFramedHeightIndexBits.col_virtual P D J q hx,
    IntegralMixedFramedHeightCellIdentities.slope_cell P D J q i hi, IntegralMixedHeightNaturalEntries.virtual_eq]
  dsimp only [state, bankFamily, IntegralMixedFramedScalarCellsBits.virtualFamily, IntegralMixedFramedHistoryFamilyBits.family] at *
  simp only [IntegralMixedFramedHeightPostBits.constantBranch, IntegralMixedFramedHeightPostBits.slopeBranch,
    IntegralMixedFramedHeightAffineSumBits.diagonal, pairFst_pair, hx, false_or]
  simp only [HB, HD]
  split_ifs <;> first | omega | ring

theorem invalid (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool)
    (hi : ¬ get P .slot8 q < P.ambient (pairFst (IntegralMixedVirtualTaskBits.saved P q)) + 1) :
    IntegralMixedFramedHeightIntegerBits.word P D J q = [] := by
  have HG : ¬ IntegralMixedFramedHeightPostBits.guard P (pair q []) := by
    intro H
    apply hi
    have HR := H.1
    simpa only [pairFst_pair, IntegralMixedFullHistoryFamilyBits.saved_root] using HR
  rw [IntegralMixedFramedHeightIntegerBits.word, IntegralMixedFramedHeightIntegerBits.value, ite_eq_right HG, Int.cast_zero]
  exact (MatrixPower.ArithmeticBits.zero_residueBits _).symm

end LeanCanny.Algebra.IntegralMixedFramedHeightIntegerNaturalBits
