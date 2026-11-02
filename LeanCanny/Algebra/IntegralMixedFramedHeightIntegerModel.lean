/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedHeightPost
public import LeanCanny.Algebra.IntegralMixedFramedHeightTableMatrix
/-! # Explicit integer formula for the actual physical and swept height entries -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedHeightIntegerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedScalarCellsBits (cell)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

noncomputable def bank (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) : ℤ :=
  IntegralMixedHistory.commonDenominator (IntegralMixedFramedOldHeightBits.state P D J q)
noncomputable def scales (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) : ℤ :=
  ∏ i ∈ Finset.range (P.ambient (RankedHistoryTask.root q) + 1), if i = get P .slot8 q then 1 else cell P D J q 2 i
noncomputable def factor (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) : ℤ :=
  bank P D J q ^ P.ambient (RankedHistoryTask.root q) * scales P D J q
noncomputable def references (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) : ℤ :=
  ∑ i ∈ Finset.range (birth P q), cell P D J q 1 i * IntegralMixedFramedHeightTableMatrixBits.matrix P D J q i
noncomputable def constant (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) : ℤ :=
  if IntegralMixedHeightTableQueryBits.oldRow P q = IntegralMixedHeightTableQueryBits.oldCol P q then cell P D J q 0 0 else 0
noncomputable def affine (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) : ℤ :=
  references P D J q + bank P D J q * constant P D J q
noncomputable def value (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) : ℤ :=
  if IntegralMixedFramedHeightPostBits.guard P (pair q []) then
    if IntegralMixedFramedHeightPostBits.constantBranch P (pair q []) then factor P D J q * affine P D J q
    else if IntegralMixedFramedHeightPostBits.slopeBranch P (pair q []) then factor P D J q * cell P D J q 3 0 else 0
  else 0
noncomputable def word (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :=
  residueBits (value P D J q : ZMod (modulus P q))

theorem word_canonical (P : Parameters) (D : IntegralMixedFramedHistoryFamilyBits.Plan P) (J : IntegralMixedFramedHistoryFamilyBits.Data P D) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = word P D J q := ⟨_, rfl⟩

end LeanCanny.Algebra.IntegralMixedFramedHeightIntegerBits
