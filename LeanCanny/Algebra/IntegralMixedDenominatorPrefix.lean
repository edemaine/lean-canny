/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedDenominatorNative
/-! # Charged mixed denominator readers at exact chronological prefixes -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedDenominatorScriptBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralMixedHistory IntegralMixedHistoryScript IntegralMixedDenominatorBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def prefixCount (F : Family) (prefixLength : List Bool → ℕ) (c : List Bool) : ℕ := min (prefixLength c) (count F c)

noncomputable def prefixProgram (F : Family) (prefixLength : List Bool → ℕ) : IntegralDenominatorPass.Family :=
  { program F with count := prefixCount F prefixLength }

theorem prefixCount_unary (F : Family) (a : Access F) (prefixLength : List Bool → ℕ) (hp : UnaryFn prefixLength) : UnaryFn (prefixCount F prefixLength) := by
  have HI := BinaryFn.ofUnary hp
  have HN := BinaryFn.ofUnary a.count
  have HE : BinaryFn (prefixCount F prefixLength) := (BinaryFn.ite (HI.le HN) HI HN).of_eq (fun _ => by rw [← min_def]; rfl)
  exact binary_bounded_unary HE a.count (fun _ => min_le_right _ _)

theorem prefixAccess (F : Family) (a : Access F) (prefixLength : List Bool → ℕ) (hp : UnaryFn prefixLength) :
    IntegralDenominatorPassSpace.Access (prefixProgram F prefixLength) :=
  { access F a with count := prefixCount_unary F a prefixLength hp }

theorem integers_prefixProgram (F : Family) (prefixLength : List Bool → ℕ) (c : List Bool) (i : ℕ) :
    IntegralDenominatorPass.integers (prefixProgram F prefixLength) c i = IntegralDenominatorPass.integers (program F) c i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [IntegralDenominatorPass.integers, IntegralDenominatorPass.integers, ih]; rfl

theorem prefix_denominator_evaluator (F : Family) (a : Access F) (prefixLength : List Bool → ℕ) (hp : UnaryFn prefixLength)
    (index : List Bool → ℕ) (hi : BinaryFn index) :
    SpaceFunction (fun c => residueBits (((IntegralDenominatorPass.integers (program F) c (prefixCount F prefixLength c))[index c]?).getD 0 : ZMod (F.modulus c))) := by
  have E := IntegralDenominatorPassSpace.integer_reader_evaluator (prefixProgram F prefixLength) (prefixAccess F a prefixLength hp) index hi
  refine E.congr (funext fun c => ?_)
  rw [integers_prefixProgram]
  rfl

noncomputable def prefixTable (F : Family) (prefixLength : List Bool → ℕ) (c : List Bool) : List Bool :=
  WordList.encode ((IntegralDenominatorPass.integers (program F) c (prefixCount F prefixLength c)).map
    (fun z : ℤ => residueBits (z : ZMod (F.modulus c))))

theorem prefix_table_evaluator (F : Family) (a : Access F) (prefixLength : List Bool → ℕ) (hp : UnaryFn prefixLength) : SpaceFunction (prefixTable F prefixLength) := by
  have E := IntegralDenominatorPassSpace.table_evaluator (prefixProgram F prefixLength) (prefixAccess F a prefixLength hp)
  refine E.congr (funext fun c => ?_)
  rw [ModularHistoryPassSpace.run_eq, IntegralDenominatorPass.values_cast, List.map_map, integers_prefixProgram]
  rfl

theorem integers_prefix_denominators (F : Family) (c : List Bool) (i : ℕ) (hi : i ≤ count F c) :
    IntegralDenominatorPass.integers (program F) c i = denominators (F.spatial c) [] ((F.rules c).reverse.take i).reverse := by
  rw [integers_prefix F c i hi, denominators_fold, List.reverse_reverse]

theorem actual_prefix_continue {S m : ℕ} (F : Family) (c : List Bool) {ι : Type} [Fintype ι]
    (initial : State (F.spatial c) S (F.width c) m ι) (cs ds : List (Command (F.ambient c) (F.width c)))
    (h : m + cs.length ≤ S + 1) (i : ℕ) (hi : i ≤ count F c)
    (hprefix : ((F.rules c).reverse.take i).reverse = cs ++ ds)
    (hinitial : bankList initial = denominators (F.spatial c) [] ds) :
    bankList (continueRun initial cs h) = IntegralDenominatorPass.integers (program F) c i := by
  rw [bankList_continueRun, integers_prefix_denominators F c i hi, hprefix, denominators_append, hinitial]
end LeanCanny.Algebra.IntegralMixedDenominatorScriptBits
