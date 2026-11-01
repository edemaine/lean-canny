/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalFlatActionCorrect
public import LeanCanny.Algebra.IntegralCriticalTotalMatrixSnapshot
public import LeanCanny.Algebra.IntegralCriticalTotalActionSnapshot
/-! # Finite actual action tasks agree with the integer action blocks -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatActualActionBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralCriticalFlatActualSources
set_option backward.isDefEq.respectTransparency false

noncomputable def value (F : Scripts) (q : List Bool) : List Bool :=
  IntegralCriticalTotalSnapshotBits.modularActionEntry F q (get F.toParameters .row q) (get F.toParameters .col q)

theorem finite_value (F : Scripts) (c : List Bool)
    (i j : Fin ((characteristic F).dimension c * (characteristic F).rank c)) :
    IntegralCriticalTotalSnapshotBits.modularActionEntry F c i.val j.val =
      residueBits ((IntegralCriticalTotalSnapshotBits.blockMatrix (characteristic F) c i j : ℤ) :
        ZMod (IntegralCriticalHistoryTask.modulus F.toParameters c)) :=
  congrArg (fun z : ℤ => residueBits (z : ZMod (IntegralCriticalHistoryTask.modulus F.toParameters c)))
    (IntegralCriticalTotalSnapshotBits.integerEntry_fin _ i j)

private theorem reduction_modulus (F : Scripts) (c : List Bool) :
    (reduction F).modulus c = IntegralCriticalHistoryTask.modulus F.toParameters c := rfl

attribute [local irreducible] relative reduction characteristic
  IntegralCriticalTotalSnapshotBits.modularActionEntry IntegralCriticalTotalSnapshotBits.actionEntry

theorem program_value_finite (F : Scripts) (answer : List Bool → List Bool) (c : List Bool)
    (he : IntegralReductionActionBits.normalGuard (reduction F)
      (IntegralCriticalFlatActionBits.packet F.toParameters (reduction F) c) →
      answer (IntegralCriticalFlatEulerBits.next F.toParameters .reductionPower c) =
        (IntegralReductionActionBits.powerFamily (reduction F)).value
          (IntegralCriticalFlatActionBits.packet F.toParameters (reduction F) c))
    (i j : Fin ((reduction F).dimension c * (reduction F).rank c))
    (hi : get F.toParameters .row c = i.val) (hj : get F.toParameters .col c = j.val) :
    (IntegralCriticalFlatActionBits.program F.toParameters (reduction F)).value answer c = value F c := by
  let := (reduction F).ring c
  have HD : (reduction F).dimension c * (reduction F).rank c =
      (characteristic F).dimension c * (characteristic F).rank c := by
    unfold characteristic
    rfl
  let r := Fin.cast HD i
  let t := Fin.cast HD j
  have HE := IntegralCriticalFlatActionBits.value_block F.toParameters (reduction F) answer c he i j hi hj
  have HM := congrArg (fun m : ℕ => residueBits ((IntegralCoefficientBlocks.blockHom ((reduction F).basis c)
    ((reduction F).dimension c) ((reduction F).actionMatrix c) i j : ℤ) : ZMod m)) (reduction_modulus F c)
  have HB : IntegralCoefficientBlocks.blockHom ((reduction F).basis c) ((reduction F).dimension c)
      ((reduction F).actionMatrix c) i j = IntegralCriticalTotalSnapshotBits.blockMatrix (characteristic F) c r t := by
    unfold characteristic
    rfl
  have HEM := HE.trans HM
  rw [HB] at HEM
  rw [value, hi, hj]
  exact HEM.trans (finite_value F c r t).symm

theorem program_power_value_finite (F : Scripts) (c : List Bool)
    (i j : Fin ((reduction F).dimension c * (reduction F).rank c))
    (hi : get F.toParameters .row c = i.val) (hj : get F.toParameters .col c = j.val) :
    (IntegralCriticalFlatActionBits.program F.toParameters (reduction F)).value
      (IntegralCriticalTotalActionSnapshotBits.powerValue F) c = value F c :=
  program_value_finite F _ c
    (fun _ => IntegralCriticalTotalActionSnapshotBits.power_next F .reductionPower c) i j hi hj

end LeanCanny.Algebra.IntegralCriticalFlatActualActionBits
