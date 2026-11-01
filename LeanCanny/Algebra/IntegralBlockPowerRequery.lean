/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralBlockPowerSource

/-! # Native input retargeting of algebra-valued matrix powers -/

@[expose] public section
namespace LeanCanny.Algebra.IntegralBlockPowerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
set_option backward.isDefEq.respectTransparency false

noncomputable def Family.requery (F : Family) (f : List Bool → List Bool) : Family where
  dimension c := F.dimension (f c)
  rank c := F.rank (f c)
  carrier c := F.carrier (f c)
  ring c := F.ring (f c)
  basis c := F.basis (f c)
  matrix c := F.matrix (f c)
  exponent c := F.exponent (f c)
  row c := F.row (f c)
  col c := F.col (f c)
  basisRow c := F.basisRow (f c)
  basisCol c := F.basisCol (f c)
  modulus c := F.modulus (f c)
  modulus_ne_zero c := F.modulus_ne_zero (f c)

def requeryEntry (f : List Bool → List Bool) (p : List Bool) : List Bool :=
  pair (pair (f (IntegralBerkowitzBlockBits.original p)) (pairSnd (pairFst p))) (pairSnd p)

theorem requeryEntry_FP (f : List Bool → List Bool) (hf : f ∈ FP) : requeryEntry f ∈ FP :=
  mem_FP_pair (mem_FP_pair (mem_FP_comp IntegralBerkowitzBlockBits.original_FP hf)
    (mem_FP_comp pairFst_mem_FP pairSnd_mem_FP)) pairSnd_mem_FP

theorem requeryEntry_packet (f : List Bool → List Bool) (c : List Bool) (i j r t : ℕ) :
    requeryEntry f (pair (IntegralBlockMomentBits.context c r t)
      (pair (BinaryNatCode.encode i) (BinaryNatCode.encode j))) =
      pair (IntegralBlockMomentBits.context (f c) r t) (pair (BinaryNatCode.encode i) (BinaryNatCode.encode j)) := by
  simp only [requeryEntry, IntegralBerkowitzBlockBits.original, IntegralBlockMomentBits.context, pairFst_pair, pairSnd_pair]

noncomputable def Access.requery (F : Family) (a : Access F) (f : List Bool → List Bool) (hf : f ∈ FP) : Access (F.requery f) where
  dimension := a.dimension.comp hf
  rank := a.rank.comp hf
  exponent := a.exponent.comp hf
  row := a.row.comp hf
  col := a.col.comp hf
  basisRow := a.basisRow.comp hf
  basisCol := a.basisCol.comp hf
  modulus := a.modulus.comp hf
  entry := a.entry ∘ requeryEntry f
  entry_eq c i j r t := by
    rw [Function.comp_apply, requeryEntry_packet]
    exact a.entry_eq (f c) i j r t

theorem Family.requery_value (F : Family) (f : List Bool → List Bool) (c : List Bool) :
    (F.requery f).value c = F.value (f c) := rfl

theorem Family.requery_powerMatrix (F : Family) (f : List Bool → List Bool) (c : List Bool) :
    (F.requery f).powerMatrix c = F.powerMatrix (f c) := rfl

end LeanCanny.Algebra.IntegralBlockPowerBits
