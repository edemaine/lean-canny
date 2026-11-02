/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPreparedCoordinateCorrect
public import LeanCanny.Algebra.IntegralMixedPreparedSquarefreeCorrect
public import LeanCanny.Algebra.IntegralMixedPreparedValueScopedCorrect
public import LeanCanny.Algebra.IntegralMixedSquarefreeFactorClosure
/-! # Actual raw-cut dispatch restores original kinds and keeps factor phases disjoint -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedRawDispatcherBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedCutSource IntegralMixedVirtualQueryBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def machine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (k : IntegralMixedRawKindBits.Metadata F) (hd : BinaryFn F.degree) :=
  (IntegralMixedPreparedCoordinateNative.machine P a F h k hd).choose
    ((IntegralMixedPreparedSquarefreeNative.machine P a F h k hd).choose
      ((IntegralMixedPreparedValueNative.machine P a F h k hd).choose
        ((IntegralMixedValueFactorScopedBits.machine P a F h).choose
          ((IntegralMixedSquarefreeFactorBits.machine P a F h).choose zero))))

private theorem zero_model (q : List Bool) : zero.model q = [] := rfl

private theorem choice_model (M N : Machine) (q : List Bool) :
    (M.choose N).model q = if M.selected q then M.model q else N.model q := rfl

private theorem coordinate_model (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (k : IntegralMixedRawKindBits.Metadata F) (hd : BinaryFn F.degree) (q : List Bool) :
    (IntegralMixedPreparedCoordinateNative.machine P a F h k hd).model q = IntegralMixedNormalizationTopBits.rawCutValue P F q := rfl
private theorem coordinate_selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (k : IntegralMixedRawKindBits.Metadata F) (hd : BinaryFn F.degree) (q : List Bool) :
    (IntegralMixedPreparedCoordinateNative.machine P a F h k hd).selected q = decide (IntegralMixedPreparedCoordinateNative.Selected P F q) := rfl

private theorem squarefree_model (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (k : IntegralMixedRawKindBits.Metadata F) (hd : BinaryFn F.degree) (q : List Bool) :
    (IntegralMixedPreparedSquarefreeNative.machine P a F h k hd).model q = IntegralMixedNormalizationTopBits.rawCutValue P F q := rfl
private theorem squarefree_selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (k : IntegralMixedRawKindBits.Metadata F) (hd : BinaryFn F.degree) (q : List Bool) :
    (IntegralMixedPreparedSquarefreeNative.machine P a F h k hd).selected q = decide (IntegralMixedPreparedSquarefreeNative.Selected P F q) := rfl

private theorem value_model (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (k : IntegralMixedRawKindBits.Metadata F) (hd : BinaryFn F.degree) (q : List Bool) :
    (IntegralMixedPreparedValueNative.machine P a F h k hd).model q = IntegralMixedNormalizationTopBits.rawCutValue P F q := rfl
private theorem value_selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (k : IntegralMixedRawKindBits.Metadata F) (hd : BinaryFn F.degree) (q : List Bool) :
    (IntegralMixedPreparedValueNative.machine P a F h k hd).selected q = decide (IntegralMixedPreparedValueNative.Selected P F q) := rfl

private theorem valueFactor_model (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (q : List Bool) :
    (IntegralMixedValueFactorScopedBits.machine P a F h).model q = IntegralMixedValueFactorValue.value P F q := rfl
private theorem valueFactor_selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (q : List Bool) :
    (IntegralMixedValueFactorScopedBits.machine P a F h).selected q = decide (IntegralMixedValueFactorScopedBits.Selected P F q) := rfl

private theorem squarefreeFactor_model (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (q : List Bool) :
    (IntegralMixedSquarefreeFactorBits.machine P a F h).model q = IntegralMixedSquarefreeFactorBits.value P F q := rfl
private theorem squarefreeFactor_selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (q : List Bool) :
    (IntegralMixedSquarefreeFactorBits.machine P a F h).selected q = decide (IntegralMixedSquarefreeFactorBits.Selected P F q) := rfl

attribute [local irreducible] IntegralMixedPreparedCoordinateNative.machine IntegralMixedPreparedSquarefreeNative.machine
  IntegralMixedPreparedValueNative.machine IntegralMixedValueFactorScopedBits.machine IntegralMixedSquarefreeFactorBits.machine

theorem machine_model (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (k : IntegralMixedRawKindBits.Metadata F) (hd : BinaryFn F.degree) (q : List Bool) :
    (machine P a F h k hd).model q =
      if IntegralMixedPreparedCoordinateNative.Selected P F q then IntegralMixedNormalizationTopBits.rawCutValue P F q else
      if IntegralMixedPreparedSquarefreeNative.Selected P F q then IntegralMixedNormalizationTopBits.rawCutValue P F q else
      if IntegralMixedPreparedValueNative.Selected P F q then IntegralMixedNormalizationTopBits.rawCutValue P F q else
      if IntegralMixedValueFactorScopedBits.Selected P F q then IntegralMixedValueFactorValue.value P F q else
      if IntegralMixedSquarefreeFactorBits.Selected P F q then IntegralMixedSquarefreeFactorBits.value P F q else [] := by
  simp only [machine, choice_model, coordinate_model, coordinate_selected, squarefree_model, squarefree_selected,
    value_model, value_selected, valueFactor_model, valueFactor_selected, squarefreeFactor_model, squarefreeFactor_selected, zero_model, decide_eq_true_eq]

theorem selected (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (k : IntegralMixedRawKindBits.Metadata F) (hd : BinaryFn F.degree) (q : List Bool) : (machine P a F h k hd).selected q = true := by
  change (_ || (_ || (_ || (_ || (_ || true))))) = true
  simp only [Bool.or_true]

theorem model_valueFactor (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (k : IntegralMixedRawKindBits.Metadata F) (hd : BinaryFn F.degree) (q : List Bool)
    (hq : IntegralMixedValueFactorScopedBits.Selected P F q) :
    (machine P a F h k hd).model q = IntegralMixedValueFactorValue.value P F q := by
  rw [machine_model]
  have HP : phase q = 25 := hq.1.2.2.1
  have HC : ¬IntegralMixedPreparedCoordinateNative.Selected P F q := by intro H; have := H.2.2.1; change phase q = 26 at this; omega
  have HS : ¬IntegralMixedPreparedSquarefreeNative.Selected P F q := by intro H; have := H.2.2.1; change phase q = 26 at this; omega
  have HV : ¬IntegralMixedPreparedValueNative.Selected P F q := by intro H; have := H.2.2.1; change phase q = 26 at this; omega
  change (if IntegralMixedPreparedCoordinateNative.Selected P F q then _ else
    if IntegralMixedPreparedSquarefreeNative.Selected P F q then _ else
    if IntegralMixedPreparedValueNative.Selected P F q then _ else
    if IntegralMixedValueFactorScopedBits.Selected P F q then _ else _) = _
  rw [ite_eq_right HC, ite_eq_right HS,
    ite_eq_right HV, ite_eq_left hq]

theorem model_squarefreeFactor (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (k : IntegralMixedRawKindBits.Metadata F) (hd : BinaryFn F.degree) (q : List Bool)
    (hq : IntegralMixedSquarefreeFactorBits.Selected P F q) :
    (machine P a F h k hd).model q = IntegralMixedSquarefreeFactorBits.value P F q := by
  rw [machine_model]
  have HP : phase q = 24 := hq.2.2.1
  have HC : ¬IntegralMixedPreparedCoordinateNative.Selected P F q := by intro H; have := H.2.2.1; change phase q = 26 at this; omega
  have HS : ¬IntegralMixedPreparedSquarefreeNative.Selected P F q := by intro H; have := H.2.2.1; change phase q = 26 at this; omega
  have HV : ¬IntegralMixedPreparedValueNative.Selected P F q := by intro H; have := H.2.2.1; change phase q = 26 at this; omega
  have HF : ¬IntegralMixedValueFactorScopedBits.Selected P F q := by intro H; have := H.1.2.2.1; change phase q = 25 at this; omega
  change (if IntegralMixedPreparedCoordinateNative.Selected P F q then _ else
    if IntegralMixedPreparedSquarefreeNative.Selected P F q then _ else
    if IntegralMixedPreparedValueNative.Selected P F q then _ else
    if IntegralMixedValueFactorScopedBits.Selected P F q then _ else
    if IntegralMixedSquarefreeFactorBits.Selected P F q then _ else _) = _
  rw [ite_eq_right HC, ite_eq_right HS,
    ite_eq_right HV, ite_eq_right HF,
    ite_eq_left hq]

theorem canonical (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (k : IntegralMixedRawKindBits.Metadata F) (hd : BinaryFn F.degree) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = (machine P a F h k hd).model q := by
  rw [machine_model]
  split_ifs
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩
  · exact ⟨0, (ArithmeticBits.zero_residueBits _).symm⟩

end LeanCanny.Algebra.IntegralMixedRawDispatcherBits
