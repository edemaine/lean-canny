/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralMixedPscRelativeModel

/-! # The actual constant characteristic coefficient preserves invalid labels -/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPscUpperBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource
open scoped Classical
attribute [local irreducible] residueBits

noncomputable def characteristicValue (P : Parameters) (F : Family) (q : List Bool) : List Bool :=
  residueBits (IntegralCriticalTotalSnapshotBits.integerEntry ((characteristic P F).coefficientMatrix q 0)
    (get P .row q) (get P .col q) : ZMod (modulus P q))

theorem characteristic_value_finite (P : Parameters) (F : Family) (q : List Bool)
    (hr : get P .row q < (characteristic P F).rank q) (ht : get P .col q < (characteristic P F).rank q) :
    (characteristic P F).value q = characteristicValue P F q := by
  have HI : ((characteristic P F).basisRow q).val = get P .row q := Nat.mod_eq_of_lt hr
  have HJ : ((characteristic P F).basisCol q).val = get P .col q := Nat.mod_eq_of_lt ht
  have HE := IntegralCriticalTotalSnapshotBits.integerEntry_fin ((characteristic P F).coefficientMatrix q 0)
    ((characteristic P F).basisRow q) ((characteristic P F).basisCol q)
  rw [HI, HJ] at HE
  have HV := congrArg (fun z : ℤ => residueBits (z : ZMod ((characteristic P F).modulus q))) HE.symm
  exact HV.trans (congrArg (fun m : ℕ => residueBits
    (IntegralCriticalTotalSnapshotBits.integerEntry ((characteristic P F).coefficientMatrix q 0)
      (get P .row q) (get P .col q) : ZMod m)) (characteristic_modulus P F q))

end LeanCanny.Algebra.IntegralMixedPscUpperBits
