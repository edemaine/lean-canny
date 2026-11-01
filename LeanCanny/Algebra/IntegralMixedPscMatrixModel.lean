/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedPscActionClosure
public import LeanCanny.Algebra.IntegralBerkowitzMatrixCore

/-! # Actual PSC block and factor matrices retain parent, coordinate and index -/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPscMatrixModel
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedPscCharacteristicBits IntegralBerkowitzBlockBits
open scoped Classical
attribute [local irreducible] IntegralMixedCutNilpotent.basis IntegralMixedSquarefreeMatrixSource.matrix
  Berkowitz.powerMatrix

noncomputable def physical (F : Family) (j c : ℕ) : Source :=
  { IntegralMixedPscEntrySnapshot.source F j c with
    matrix key := by
      let := (IntegralMixedPscEntrySnapshot.source F j c).ring key
      exact -(IntegralMixedPscEntrySnapshot.source F j c).matrix key }
noncomputable def core (F : Family) (key : List Bool) (j c : ℕ) : Source :=
  IntegralBerkowitzMatrixCore.freeze (physical F j c) key

theorem core_snapshot (P : Parameters) (F : Family) (q : List Bool) :
    IntegralBerkowitzMatrixCore.freeze (source P F) q =
      core F (IntegralMixedVirtualTaskBits.saved P q) (get P .slot13 q) (get P .slot8 q) := rfl

noncomputable def integerAction (F : Family) (key : List Bool) (j c r t : ℕ) : ℤ :=
  IntegralCriticalTotalSnapshotBits.integerEntry (IntegralCriticalTotalSnapshotBits.blockMatrix (core F key j c) []) r t
noncomputable def integerPower (F : Family) (key : List Bool) (j c r t : ℕ) : ℤ :=
  IntegralCriticalTotalSnapshotBits.integerEntry ((core F key j c).powerMatrix []) r t

theorem dimension_snapshot (P : Parameters) (F : Family) (q : List Bool) :
    (source P F).dimension q = (core F (IntegralMixedVirtualTaskBits.saved P q) (get P .slot13 q) (get P .slot8 q)).dimension [] := rfl
theorem rank_snapshot (P : Parameters) (F : Family) (q : List Bool) :
    (source P F).rank q = (core F (IntegralMixedVirtualTaskBits.saved P q) (get P .slot13 q) (get P .slot8 q)).rank [] := rfl
theorem basis_snapshot (P : Parameters) (F : Family) (q : List Bool) :
    (source P F).basis q = (core F (IntegralMixedVirtualTaskBits.saved P q) (get P .slot13 q) (get P .slot8 q)).basis [] := rfl
theorem matrix_snapshot (P : Parameters) (F : Family) (q : List Bool) :
    (source P F).matrix q = (core F (IntegralMixedVirtualTaskBits.saved P q) (get P .slot13 q) (get P .slot8 q)).matrix [] := rfl
theorem action_snapshot (P : Parameters) (F : Family) (q : List Bool) (r t : ℕ) :
    integerAction F (IntegralMixedVirtualTaskBits.saved P q) (get P .slot13 q) (get P .slot8 q) r t =
      IntegralCriticalTotalSnapshotBits.integerEntry (IntegralCriticalTotalSnapshotBits.blockMatrix (source P F) q) r t := rfl
theorem power_snapshot (P : Parameters) (F : Family) (q : List Bool) (r t : ℕ) :
    integerPower F (IntegralMixedVirtualTaskBits.saved P q) (get P .slot13 q) (get P .slot8 q) r t =
      IntegralCriticalTotalSnapshotBits.integerEntry ((source P F).powerMatrix q) r t := rfl

noncomputable def actionValue (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  residueBits (integerAction F (IntegralMixedVirtualTaskBits.saved P q) (get P .slot13 q) (get P .slot8 q)
    (get P .row q) (get P .col q) : ZMod (modulus P q))
noncomputable def factorValue (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  residueBits (integerPower F (IntegralMixedVirtualTaskBits.saved P q) (get P .slot13 q) (get P .slot8 q)
    (get P .row q) (get P .col q) : ZMod (modulus P q))

theorem action_native (P : Parameters) (F : Family) (q : List Bool) :
    actionValue P F q = IntegralMixedPscActionBits.value P F q := by
  unfold actionValue IntegralMixedPscActionBits.value
  rw [action_snapshot]

attribute [local irreducible] integerAction integerPower

theorem action_transport (P : Parameters) (F : Family) (q c : List Bool) (r t : ℕ)
    (hs : IntegralMixedVirtualTaskBits.saved P c = IntegralMixedVirtualTaskBits.saved P q)
    (hj : get P .slot13 c = get P .slot13 q) (hk : get P .slot8 c = get P .slot8 q) (hm : modulus P c = modulus P q)
    (hi : get P .row c = r) (ht : get P .col c = t) :
    actionValue P F c = residueBits (integerAction F (IntegralMixedVirtualTaskBits.saved P q)
      (get P .slot13 q) (get P .slot8 q) r t : ZMod (modulus P q)) := by
  unfold actionValue
  rw [hs, hj, hk, hi, ht]
  exact congrArg (fun m : ℕ => residueBits (integerAction F (IntegralMixedVirtualTaskBits.saved P q)
    (get P .slot13 q) (get P .slot8 q) r t : ZMod m)) hm

theorem factor_transport (P : Parameters) (F : Family) (q c : List Bool) (r t : ℕ)
    (hs : IntegralMixedVirtualTaskBits.saved P c = IntegralMixedVirtualTaskBits.saved P q)
    (hj : get P .slot13 c = get P .slot13 q) (hk : get P .slot8 c = get P .slot8 q) (hm : modulus P c = modulus P q)
    (hi : get P .row c = r) (ht : get P .col c = t) :
    factorValue P F c = residueBits (integerPower F (IntegralMixedVirtualTaskBits.saved P q)
      (get P .slot13 q) (get P .slot8 q) r t : ZMod (modulus P q)) := by
  unfold factorValue
  rw [hs, hj, hk, hi, ht]
  exact congrArg (fun m : ℕ => residueBits (integerPower F (IntegralMixedVirtualTaskBits.saved P q)
    (get P .slot13 q) (get P .slot8 q) r t : ZMod m)) hm

end LeanCanny.Algebra.IntegralMixedPscMatrixModel
