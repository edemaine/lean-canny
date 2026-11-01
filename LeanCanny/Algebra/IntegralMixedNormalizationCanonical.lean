/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationDispatcher
/-! # Every normalization controller retains canonical modular replies -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationTopBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource NativeControllerBranch
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] modulus top

theorem value_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = value P F q := ⟨_, rfl⟩

theorem momentEntry_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = momentEntry P F q := ⟨_, rfl⟩

theorem momentValue_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = momentValue P F q := by
  rw [moment_snapshot]
  unfold momentAt IntegralBerkowitzMomentFreezeBits.atMoment
  dsimp only [sourceAt]
  exact ⟨_, rfl⟩

theorem factorValue_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = factorValue P F q := ⟨_, rfl⟩

theorem characteristic_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = (source P F).value q := by
  rw [value_coefficient]
  exact ⟨_, rfl⟩

theorem inverseTerm_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = inverseTermValue P F q := ⟨_, rfl⟩

theorem inverseMatrix_canonical (P : Parameters) (F : Family) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = inverseMatrixValue P F q := ⟨_, rfl⟩

end LeanCanny.Algebra.IntegralMixedNormalizationTopBits

namespace LeanCanny.Algebra.IntegralMixedNormalizationDispatcherBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedNormalizationTopBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] modulus top IntegralMixedNormalizationTopBits.value topPowerValue momentEntry momentValue factorValue
  zeroValue indexValue inverseValue inverseTermValue inverseMatrixValue productTermValue productValue IntegralMixedNormalizationTopBits.source
  IntegralBerkowitzBlockBits.Source.value

private theorem choose_canonical (P : Parameters) (M N : Machine) (q : List Bool)
    (hm : ∃ z : ZMod (modulus P q), residueBits z = M.model q)
    (hn : ∃ z : ZMod (modulus P q), residueBits z = N.model q) :
    ∃ z : ZMod (modulus P q), residueBits z = (M.choose N).model q := by
  change ∃ z : ZMod (modulus P q), residueBits z = if M.selected q then M.model q else N.model q
  split_ifs
  · exact hm
  · exact hn

theorem canonical (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (hd : BinaryFn F.degree)
    (height : List Bool → ℕ) (hb : BinaryFn height) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = (machine P a F h hd height hb).model q := by
  unfold machine
  apply choose_canonical P _ _ q
  · change ∃ z : ZMod (modulus P q), residueBits z = value P F q
    exact value_canonical P F q
  apply choose_canonical P _ _ q
  · change ∃ z : ZMod (modulus P q), residueBits z = topPowerValue P F q
    exact topPowerValue_canonical P F q
  apply choose_canonical P _ _ q
  · change ∃ z : ZMod (modulus P q), residueBits z = value P F q
    exact value_canonical P F q
  apply choose_canonical P _ _ q
  · change ∃ z : ZMod (modulus P q), residueBits z = momentEntry P F q
    exact momentEntry_canonical P F q
  apply choose_canonical P _ _ q
  · change ∃ z : ZMod (modulus P q), residueBits z = momentValue P F q
    exact momentValue_canonical P F q
  apply choose_canonical P _ _ q
  · change ∃ z : ZMod (modulus P q), residueBits z = factorValue P F q
    exact factorValue_canonical P F q
  apply choose_canonical P _ _ q
  · change ∃ z : ZMod (modulus P q), residueBits z = (source P F).value q
    exact characteristic_canonical P F q
  apply choose_canonical P _ _ q
  · change ∃ z : ZMod (modulus P q), residueBits z = zeroValue P F q
    exact zeroValue_canonical P F q
  apply choose_canonical P _ _ q
  · change ∃ z : ZMod (modulus P q), residueBits z = indexValue P F q
    exact indexValue_canonical P F q
  apply choose_canonical P _ _ q
  · change ∃ z : ZMod (modulus P q), residueBits z = inverseValue P F q
    exact inverseValue_canonical P F q
  apply choose_canonical P _ _ q
  · change ∃ z : ZMod (modulus P q), residueBits z = inverseTermValue P F q
    exact inverseTerm_canonical P F q
  apply choose_canonical P _ _ q
  · change ∃ z : ZMod (modulus P q), residueBits z = inverseMatrixValue P F q
    exact inverseMatrix_canonical P F q
  apply choose_canonical P _ _ q
  · change ∃ z : ZMod (modulus P q), residueBits z = productTermValue P F q
    exact productTermValue_canonical P F q
  apply choose_canonical P _ _ q
  · change ∃ z : ZMod (modulus P q), residueBits z = productValue P F q
    exact productValue_canonical P F q
  exact stage14_canonical P a F h hd q

end LeanCanny.Algebra.IntegralMixedNormalizationDispatcherBits
