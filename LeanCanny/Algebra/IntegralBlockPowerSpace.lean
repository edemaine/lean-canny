/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralBlockPowerSource

/-! # Native entries of algebra-valued matrix powers

Integer block powering returns an actual multiplication-matrix entry of
the power over the original algebra. All controls are binary, including
the outer dimension, exponent, and old basis rank. The sole supplied
entry reader's complete space cost is charged.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralBlockPowerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable def powerFamily (F : Family) : MatrixPower.ModularFamily where
  dimension c := F.dimension c * F.rank c
  modulus := F.modulus
  exponent := F.exponent
  row c := finProdFinEquiv (F.row c, F.basisRow c)
  col c := finProdFinEquiv (F.col c, F.basisCol c)
  matrix c := (F.powerMatrix c).map (Int.castRingHom (ZMod (F.modulus c)))
  modulus_ne_zero := F.modulus_ne_zero

noncomputable def powerAccess (F : Family) (a : Access F) : MatrixPower.ModularAccess (powerFamily F) where
  dimension c := BinaryNatCode.encode (F.dimension c * F.rank c)
  modulus c := BinaryNatCode.encode (F.modulus c)
  exponent c := BinaryNatCode.encode (F.exponent c)
  row c := BinaryNatCode.encode ((powerFamily F).row c).val
  col c := BinaryNatCode.encode ((powerFamily F).col c).val
  entry := entryProgram F a
  dimension_eq _ := rfl
  modulus_eq _ := rfl
  exponent_eq _ := rfl
  row_eq _ := rfl
  col_eq _ := rfl
  entry_eq := entry_correct F a

theorem power_controls (F : Family) (a : Access F) : (powerAccess F a).ControlsPolyTime :=
  ⟨(a.dimension.mul a.rank).bits_mem_FP, a.modulus.bits_mem_FP, a.exponent.bits_mem_FP,
    (a.basisRow.add (a.rank.mul a.row)).bits_mem_FP, (a.basisCol.add (a.rank.mul a.col)).bits_mem_FP⟩

theorem power_value (F : Family) : (powerFamily F).value = F.value := by
  funext c
  let := F.ring c
  rw [MatrixPower.ModularFamily.value]
  change residueBits ((((F.powerMatrix c).map (Int.castRingHom (ZMod (F.modulus c)))) ^ F.exponent c)
    (finProdFinEquiv (F.row c, F.basisRow c)) (finProdFinEquiv (F.col c, F.basisCol c))) = _
  rw [← Matrix.map_pow, Matrix.map_apply]
  exact congrArg (fun z : ℤ => residueBits (z : ZMod (F.modulus c)))
    (IntegralCoefficientBlocks.block_power_entry (F.basis c) (F.matrix c) (F.exponent c)
      (F.row c) (F.col c) (F.basisRow c) (F.basisCol c))

attribute [local irreducible] Family.powerMatrix Family.value entryProgram

theorem evaluator (F : Family) (a : Access F) (E : SpaceFunction a.entry) : SpaceFunction F.value := by
  have HE : SpaceFunction (powerAccess F a).entry := by
    change SpaceFunction (entryProgram F a)
    exact entry_evaluator F a E
  exact (MatrixPower.ModularAccess.evaluatorWithEntry (powerAccess F a) (power_controls F a) HE).congr (power_value F)

end LeanCanny.Algebra.IntegralBlockPowerBits
