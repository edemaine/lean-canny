/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalTotalCreatingSource
public import LeanCanny.Algebra.IntegralCriticalHeightValue
public import LeanCanny.Algebra.IntegralCriticalScriptEuler
/-! # Actual retained height entries for every flat task -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralHistoryCriticalBits
open LeanCanny.Encoding MatrixPower FixedWidthPolynomial UniformIntegralPrefix
set_option backward.isDefEq.respectTransparency false

theorem heightValue_mod (F : Family) (i r t modulus : ℕ) :
    heightValue F i (r % count (F.birth []) (F.width []))
      (t % count (F.birth []) (F.width [])) modulus = heightValue F i r t modulus := by
  unfold heightValue
  simp only [Nat.mod_mod]

end LeanCanny.Algebra.IntegralHistoryCriticalBits

namespace LeanCanny.Algebra.IntegralCriticalScriptQueryBits
open LeanCanny.Encoding MatrixPower
set_option backward.isDefEq.respectTransparency false

theorem height_snapshot (F : Families) (q : Queries F) (c : List Bool) (i r t : ℕ) :
    IntegralCriticalScriptEulerBits.heightAt (source F q).toEuler.toGradient.toFrozen.toSource c i r t =
      IntegralHistoryCriticalBits.heightValue (F c) i r t (q.modulus c) := rfl

end LeanCanny.Algebra.IntegralCriticalScriptQueryBits

namespace LeanCanny.Algebra.IntegralCriticalTotalHeightBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open IntegralCriticalTotalCompanionBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def entry (F : Scripts) (q : List Bool) (i r t : ℕ) : List Bool :=
  IntegralHistoryCriticalBits.heightValue (IntegralCriticalTotalCreatingBits.atFamily F q) i r t
    (IntegralCriticalHistoryTask.modulus F.toParameters q)

noncomputable def value (F : Scripts) (q : List Bool) : List Bool :=
  entry F q (IntegralCriticalHistoryTask.get F.toParameters .slot8 q)
    (IntegralCriticalHistoryTask.get F.toParameters .row q)
    (IntegralCriticalHistoryTask.get F.toParameters .col q)

theorem entry_eq_heightAt (F : Scripts) (q : List Bool) (i r t : ℕ) :
    entry F q i r t = IntegralCriticalScriptEulerBits.heightAt
      (IntegralCriticalTotalCreatingBits.euler F).toGradient.toFrozen.toSource q i r t :=
  (IntegralCriticalScriptQueryBits.height_snapshot (IntegralCriticalTotalCreatingBits.atFamily F)
    (IntegralCriticalTotalCreatingBits.queries F) q i r t).symm

theorem value_eq_heightAt (F : Scripts) (q : List Bool) :
    value F q = IntegralCriticalScriptEulerBits.heightAt
      (IntegralCriticalTotalCreatingBits.euler F).toGradient.toFrozen.toSource q
      (IntegralCriticalHistoryTask.get F.toParameters .slot8 q)
      (IntegralCriticalHistoryTask.get F.toParameters .row q)
      (IntegralCriticalHistoryTask.get F.toParameters .col q) := entry_eq_heightAt F q _ _ _

theorem entry_invariance (F : Scripts) (q c : List Bool)
    (hr : root q = root c)
    (hb : IntegralCriticalHistoryTask.birth F.toParameters q = IntegralCriticalHistoryTask.birth F.toParameters c)
    (hm : IntegralCriticalHistoryTask.modulus F.toParameters q = IntegralCriticalHistoryTask.modulus F.toParameters c)
    (i r t : ℕ) : entry F q i r t = entry F c i r t := by
  unfold entry
  rw [IntegralCriticalTotalCreatingBits.atFamily_invariance F q c hr hb, hm]

theorem dummy_heightValue (i r t modulus : ℕ) :
    IntegralHistoryCriticalBits.heightValue IntegralCriticalTotalCreatingBits.dummy i r t modulus = [] := by
  let := (IntegralHistoryCriticalBits.original IntegralCriticalTotalCreatingBits.dummy).ring []
  unfold IntegralHistoryCriticalBits.heightValue UniformIntegralPrefix.Prefix.elementEntry
  have H : (IntegralHistoryCriticalBits.original IntegralCriticalTotalCreatingBits.dummy).height [] i = 0 := by
    change CoordinateFrozenCriticalElimination.numerators (fun _ : Fin 1 => 1) (fun _ => (0 : ℤ)) i = 0
    unfold CoordinateFrozenCriticalElimination.numerators CommonIntegerDenominator.numerator
    split_ifs <;> simp only [zero_mul]
  rw [H]
  simp only [map_zero, Matrix.zero_apply, Int.cast_zero]
  simp [residueBits, BinaryNatCode.encode]

theorem value_invalid (F : Scripts) (q : List Bool) (h : ¬ valid F q) : value F q = [] := by
  unfold value entry
  rw [IntegralCriticalTotalCreatingBits.atFamily_invalid F q h]
  exact dummy_heightValue _ _ _ _

end LeanCanny.Algebra.IntegralCriticalTotalHeightBits
