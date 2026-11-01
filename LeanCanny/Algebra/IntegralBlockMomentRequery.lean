/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralBlockMomentSpace
public import LeanCanny.Algebra.IntegralBlockPowerRequery
/-! # Native context replacement for algebra-valued block moments -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralBlockMomentBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
set_option backward.isDefEq.respectTransparency false

noncomputable def Family.requery (F : Family) (f : List Bool → List Bool) : Family where
  dimension c := F.dimension (f c)
  rank c := F.rank (f c)
  carrier c := F.carrier (f c)
  ring c := F.ring (f c)
  basis c := F.basis (f c)
  row c := F.row (f c)
  column c := F.column (f c)
  matrix c := F.matrix (f c)
  modulus c := F.modulus (f c)
  modulus_ne_zero c := F.modulus_ne_zero (f c)
  exponent c := F.exponent (f c)
  basisRow c := F.basisRow (f c)
  basisCol c := F.basisCol (f c)

theorem requery_context (f : List Bool → List Bool) (c : List Bool) (r t : ℕ) (v : List Bool) :
    IntegralBlockPowerBits.requeryEntry f (pair (context c r t) v) = pair (context (f c) r t) v := by
  simp only [IntegralBlockPowerBits.requeryEntry, IntegralBerkowitzBlockBits.original, context, pairFst_pair, pairSnd_pair]

noncomputable def Access.requery (F : Family) (a : Access F) (f : List Bool → List Bool) (hf : f ∈ FP) : Access (F.requery f) where
  dimension := a.dimension.comp hf
  rank := a.rank.comp hf
  modulus := a.modulus.comp hf
  exponent := a.exponent.comp hf
  basisRow := a.basisRow.comp hf
  basisCol := a.basisCol.comp hf
  row := a.row ∘ IntegralBlockPowerBits.requeryEntry f
  column := a.column ∘ IntegralBlockPowerBits.requeryEntry f
  entry := a.entry ∘ IntegralBlockPowerBits.requeryEntry f
  row_eq c i r t := by
    rw [Function.comp_apply, requery_context]
    exact a.row_eq (f c) i r t
  column_eq c i r t := by
    rw [Function.comp_apply, requery_context]
    exact a.column_eq (f c) i r t
  entry_eq c i j r t := by
    rw [Function.comp_apply, requery_context]
    exact a.entry_eq (f c) i j r t

theorem Family.requery_value (F : Family) (f : List Bool → List Bool) (c : List Bool) :
    (F.requery f).value c = F.value (f c) := rfl

theorem Family.requery_powerMatrix (F : Family) (f : List Bool → List Bool) (c : List Bool) :
    (F.requery f).powerMatrix c = F.powerMatrix (f c) := rfl

end LeanCanny.Algebra.IntegralBlockMomentBits
