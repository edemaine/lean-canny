/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalFlatCreatingFP
public import LeanCanny.Algebra.IntegralScalarGeneratorController

/-! # Coefficient entries packaged by their whole actual critical source -/

@[expose] public section
namespace LeanCanny.Algebra.IntegralHistoryCriticalBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial UniformIntegralPrefix
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def coefficientEntry (F : Family) (k r t modulus : ℕ) : ZMod modulus := by
  let S := source F
  let := S.ring []
  have HP : 0 < S.rank [] := (Nat.zero_le (S.row []).val).trans_lt (S.row []).isLt
  exact ((Algebra.leftMulMatrix (S.basis []) ((S.annihilator []).coeff k)
    ⟨r % S.rank [], Nat.mod_lt _ HP⟩
    ⟨t % S.rank [], Nat.mod_lt _ HP⟩ : ℤ) : ZMod modulus)

noncomputable def leadingInteger (F : Family) : ℤ := IntegralClearedCriticalLeadingBits.integer (source F) []

theorem coefficientEntry_leading (F : Family) (r t modulus : ℕ) :
    coefficientEntry F (IntegralScalarRootHistoryBounds.degree F []) r t modulus =
      if r % (source F).rank [] = t % (source F).rank [] then
        (leadingInteger F : ZMod modulus) else 0 := by
  let := (source F).ring []
  have H := IntegralClearedCriticalLeadingBits.coefficient (source F) []
  change ((source F).annihilator []).coeff (IntegralScalarRootHistoryBounds.degree F []) =
    (leadingInteger F : (source F).carrier []) at H
  unfold coefficientEntry
  dsimp only
  rw [H]
  simp only [map_intCast, Matrix.intCast_apply, Fin.ext_iff]
  split_ifs <;> simp only [Int.cast_zero, Int.cast_id]

end LeanCanny.Algebra.IntegralHistoryCriticalBits

namespace LeanCanny.Algebra.IntegralCriticalScriptGeneratorBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
set_option backward.isDefEq.respectTransparency false

theorem coefficientEntry_eq (F : Queries) (c : List Bool) (k : ℕ)
    (r t : Fin (count (IntegralCriticalScript.older (F.rules c) (F.selected c)).length (F.width c))) :
    IntegralHistoryCriticalBits.coefficientEntry (birthSource F c) k r.val t.val (F.modulus c) =
      (scalarFamily F).coefficient c k r t := by
  have HR : r.val < (IntegralHistoryCriticalBits.source (birthSource F c)).rank [] := r.isLt
  have HT : t.val < (IntegralHistoryCriticalBits.source (birthSource F c)).rank [] := t.isLt
  unfold IntegralHistoryCriticalBits.coefficientEntry
  dsimp only
  simp only [Nat.mod_eq_of_lt HR, Nat.mod_eq_of_lt HT]
  rfl

end LeanCanny.Algebra.IntegralCriticalScriptGeneratorBits
