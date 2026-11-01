/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedHeightPost
public import LeanCanny.Algebra.IntegralMixedHeightTableMatrix
/-! # Explicit integer formula for the actual physical and swept height entries -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedHeightIntegerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedHeightCellsBits (cell)
open scoped Classical BigOperators
set_option backward.isDefEq.respectTransparency false

noncomputable def bank (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) : ℤ :=
  IntegralMixedHistory.commonDenominator (IntegralMixedOldHeightBits.state P D q)
noncomputable def scales (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) : ℤ :=
  ∏ i ∈ Finset.range (P.ambient (RankedHistoryTask.root q) + 1), if i = get P .slot8 q then 1 else cell P D q 2 i
noncomputable def factor (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) : ℤ :=
  bank P D q ^ P.ambient (RankedHistoryTask.root q) * scales P D q
noncomputable def references (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) : ℤ :=
  ∑ i ∈ Finset.range (birth P q), cell P D q 1 i * IntegralMixedHeightTableMatrixBits.matrix P D q i
noncomputable def constant (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) : ℤ :=
  if IntegralMixedHeightTableQueryBits.oldRow P q = IntegralMixedHeightTableQueryBits.oldCol P q then cell P D q 0 0 else 0
noncomputable def affine (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) : ℤ :=
  references P D q + bank P D q * constant P D q
noncomputable def value (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) : ℤ :=
  if IntegralMixedHeightPostBits.guard P (pair q []) then
    if IntegralMixedHeightPostBits.constantBranch P (pair q []) then factor P D q * affine P D q
    else if IntegralMixedHeightPostBits.slopeBranch P (pair q []) then factor P D q * cell P D q 3 0 else 0
  else 0
noncomputable def word (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) :=
  residueBits (value P D q : ZMod (modulus P q))

theorem word_canonical (P : Parameters) (D : IntegralMixedFullHistoryFamilyBits.Data P) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = word P D q := ⟨_, rfl⟩

end LeanCanny.Algebra.IntegralMixedHeightIntegerBits
