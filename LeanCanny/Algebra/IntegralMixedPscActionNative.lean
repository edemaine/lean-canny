/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPscActionTasks
public import LeanCanny.Algebra.IntegralNaturalBlockEntry
/-! # The first PSC determinant phase reads and negates the actual PSC entry -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPscActionBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedCutSource IntegralMixedVirtualQueryBits IntegralMixedPscActionTasks
open IntegralMixedPscCharacteristicBits
open scoped Classical
attribute [local irreducible] ArithmeticBits.negate

theorem block_entry (P : Parameters) (F : Family) (q : List Bool) (a b : ℕ) :
    IntegralCriticalTotalSnapshotBits.integerEntry (IntegralCriticalTotalSnapshotBits.blockMatrix (source P F) q) a b =
      table P F q (a / (source P F).rank q) (b / (source P F).rank q)
        (a % (source P F).rank q) (b % (source P F).rank q) := by
  let := (source P F).ring q
  exact IntegralNaturalBlockEntry.entry_all ((source P F).basis q) ((source P F).matrix q)
    ((source P F).rank_pos q) a b

noncomputable def value (P : Parameters) (F : Family) (q : List Bool) : List Bool := residueBits
  (IntegralCriticalTotalSnapshotBits.integerEntry (IntegralCriticalTotalSnapshotBits.blockMatrix (source P F) q)
    (get P .row q) (get P .col q) : ZMod (modulus P q))

theorem positive_child (P : Parameters) (F : Family) (q : List Bool) :
    IntegralMixedPscEntryBits.value P F (query P F q) = residueBits
      (IntegralMixedPscEntryBits.table P F q (spatialRow P F q) (spatialCol P F q)
        (basisRow P F q) (basisCol P F q) : ZMod (modulus P q)) := by
  rw [IntegralMixedPscEntrySnapshot.value_snapshot, query_saved]
  simp only [query_get, reduceCtorEq, ite_false, ite_true]
  rw [← IntegralMixedPscEntrySnapshot.snapshot]
  exact congrArg (fun m : ℕ => residueBits
    (IntegralMixedPscEntryBits.table P F q (spatialRow P F q) (spatialCol P F q)
      (basisRow P F q) (basisCol P F q) : ZMod m)) (query_modulus P F q)

def finish (P : Parameters) (z : List Bool) : List Bool :=
  ArithmeticBits.negate (pair (BinaryNatCode.encode (modulus P (pairFst z))) (pairSnd z))
theorem finish_FP (P : Parameters) (a : Access P) : finish P ∈ FP := by
  have HM : BinaryFn (fun z => modulus P (pairFst z)) := (modulus_binary P a).comp pairFst_mem_FP
  exact mem_FP_of_eq (mem_FP_comp (mem_FP_pair HM.bits_mem_FP pairSnd_mem_FP) ArithmeticBits.negate_mem_FP) (fun _ => rfl)
theorem finish_integer (P : Parameters) (q : List Bool) (x : ℤ) :
    finish P (pair q (residueBits (x : ZMod (modulus P q)))) = residueBits ((-x : ℤ) : ZMod (modulus P q)) := by
  let : NeZero (modulus P q) := ⟨modulus_ne_zero P q⟩
  simp only [finish, pairFst_pair, pairSnd_pair, ArithmeticBits.negate_residueBits, Int.cast_neg]

noncomputable def program (P : Parameters) (F : Family) : SingleCall.Program where
  request _ := true
  query := query P F
  immediate _ := []
  finish := finish P
theorem controls (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : (program P F).Controls :=
  ⟨constFn_mem_FP [true], query_FP P a F h, constFn_mem_FP [], finish_FP P a⟩

abbrev RepliesAt (P : Parameters) (F : Family) (answer : List Bool → List Bool) (q : List Bool) : Prop :=
  answer (query P F q) = IntegralMixedPscEntryBits.value P F (query P F q)
theorem value_at (P : Parameters) (F : Family) (answer : List Bool → List Bool) (q : List Bool)
    (he : RepliesAt P F answer q) : (program P F).value answer q = value P F q := by
  simp only [SingleCall.Program.value, program, ite_true]
  rw [he, positive_child, finish_integer]
  exact congrArg (fun z : ℤ => residueBits (z : ZMod (modulus P q)))
    ((block_entry P F q (get P .row q) (get P .col q)).trans (table_neg P F q _ _ _ _)).symm

end LeanCanny.Algebra.IntegralMixedPscActionBits
