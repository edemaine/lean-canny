/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedGramBlockEntryClosure
public import LeanCanny.Algebra.IntegralBerkowitzMatrixCore

/-! # Actual Gram block and characteristic-factor matrices retain their source -/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedGramMatrixModel
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedGramCharacteristicSource IntegralBerkowitzBlockBits
open scoped Classical
attribute [local irreducible] IntegralMixedValueDoubleNilpotent.basis IntegralMixedValueDoubleNilpotent.matrix
  Berkowitz.powerMatrix

noncomputable def core (F : Family) (key : List Bool) (j : ℕ) : Source :=
  IntegralBerkowitzMatrixCore.freeze (IntegralMixedGramCharacteristicSnapshot.physical F j) key

theorem core_snapshot (P : Parameters) (F : Family) (q : List Bool) :
    IntegralBerkowitzMatrixCore.freeze (source P F) q =
      core F (IntegralMixedVirtualTaskBits.saved P q) (get P .slot13 q) := rfl

noncomputable def integerAction (F : Family) (key : List Bool) (j r t : ℕ) : ℤ :=
  IntegralCriticalTotalSnapshotBits.integerEntry (IntegralCriticalTotalSnapshotBits.blockMatrix (core F key j) []) r t
noncomputable def integerPower (F : Family) (key : List Bool) (j r t : ℕ) : ℤ :=
  IntegralCriticalTotalSnapshotBits.integerEntry ((core F key j).powerMatrix []) r t

theorem dimension_snapshot (P : Parameters) (F : Family) (q : List Bool) :
    (source P F).dimension q = (core F (IntegralMixedVirtualTaskBits.saved P q) (get P .slot13 q)).dimension [] := rfl
theorem rank_snapshot (P : Parameters) (F : Family) (q : List Bool) :
    (source P F).rank q = (core F (IntegralMixedVirtualTaskBits.saved P q) (get P .slot13 q)).rank [] := rfl
theorem basis_snapshot (P : Parameters) (F : Family) (q : List Bool) :
    (source P F).basis q = (core F (IntegralMixedVirtualTaskBits.saved P q) (get P .slot13 q)).basis [] := rfl
theorem matrix_snapshot (P : Parameters) (F : Family) (q : List Bool) :
    (source P F).matrix q = (core F (IntegralMixedVirtualTaskBits.saved P q) (get P .slot13 q)).matrix [] := rfl
theorem action_snapshot (P : Parameters) (F : Family) (q : List Bool) (r t : ℕ) :
    integerAction F (IntegralMixedVirtualTaskBits.saved P q) (get P .slot13 q) r t =
      IntegralCriticalTotalSnapshotBits.integerEntry (IntegralCriticalTotalSnapshotBits.blockMatrix (source P F) q) r t := rfl
theorem power_snapshot (P : Parameters) (F : Family) (q : List Bool) (r t : ℕ) :
    integerPower F (IntegralMixedVirtualTaskBits.saved P q) (get P .slot13 q) r t =
      IntegralCriticalTotalSnapshotBits.integerEntry ((source P F).powerMatrix q) r t := rfl

noncomputable def actionValue (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  residueBits (integerAction F (IntegralMixedVirtualTaskBits.saved P q) (get P .slot13 q)
    (get P .row q) (get P .col q) : ZMod (modulus P q))
noncomputable def factorValue (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  residueBits (integerPower F (IntegralMixedVirtualTaskBits.saved P q) (get P .slot13 q)
    (get P .row q) (get P .col q) : ZMod (modulus P q))

theorem action_native (P : Parameters) (F : Family) (q : List Bool) :
    actionValue P F q = IntegralMixedGramBlockEntryNative.value P F q := by
  unfold actionValue IntegralMixedGramBlockEntryNative.value
  rw [action_snapshot]

attribute [local irreducible] integerAction integerPower

theorem action_transport (P : Parameters) (F : Family) (q c : List Bool) (r t : ℕ)
    (hs : IntegralMixedVirtualTaskBits.saved P c = IntegralMixedVirtualTaskBits.saved P q)
    (hj : get P .slot13 c = get P .slot13 q) (hm : modulus P c = modulus P q)
    (hi : get P .row c = r) (ht : get P .col c = t) :
    actionValue P F c = residueBits (integerAction F (IntegralMixedVirtualTaskBits.saved P q)
      (get P .slot13 q) r t : ZMod (modulus P q)) := by
  unfold actionValue
  rw [hs, hj, hi, ht]
  exact congrArg (fun m : ℕ => residueBits (integerAction F (IntegralMixedVirtualTaskBits.saved P q)
    (get P .slot13 q) r t : ZMod m)) hm

theorem factor_transport (P : Parameters) (F : Family) (q c : List Bool) (r t : ℕ)
    (hs : IntegralMixedVirtualTaskBits.saved P c = IntegralMixedVirtualTaskBits.saved P q)
    (hj : get P .slot13 c = get P .slot13 q) (hm : modulus P c = modulus P q)
    (hi : get P .row c = r) (ht : get P .col c = t) :
    factorValue P F c = residueBits (integerPower F (IntegralMixedVirtualTaskBits.saved P q)
      (get P .slot13 q) r t : ZMod (modulus P q)) := by
  unfold factorValue
  rw [hs, hj, hi, ht]
  exact congrArg (fun m : ℕ => residueBits (integerPower F (IntegralMixedVirtualTaskBits.saved P q)
    (get P .slot13 q) r t : ZMod m)) hm

end LeanCanny.Algebra.IntegralMixedGramMatrixModel
