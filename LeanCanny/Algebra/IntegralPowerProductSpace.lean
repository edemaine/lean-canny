/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralPowerProductCorrect

/-! # Native coefficient entries of algebra-valued products of powers

Each factor power is computed from the original factor entry reader.
A layered product computes the requested old basis entry of their actual
algebra product. The sole original reader's full space cost is charged.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralPowerProductBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
set_option backward.isDefEq.respectTransparency false

noncomputable def productAccess (F : Family) (a : Access F) : MatrixProductBits.Access (productFamily F) where
  width := a.rank
  count := a.count
  modulus := a.modulus
  row := a.row
  col := a.col
  entry := (powerFamily F).value
  entry_eq := power_packet F

attribute [local irreducible] Family.value MatrixPower.ModularFamily.value

theorem evaluator (F : Family) (a : Access F) (E : SpaceFunction a.entry) : SpaceFunction F.value := by
  have HE : SpaceFunction (productAccess F a).entry := power_evaluator F a E
  exact (MatrixProductBits.evaluator (productFamily F) (productAccess F a) HE).congr (product_value F)

end LeanCanny.Algebra.IntegralPowerProductBits
