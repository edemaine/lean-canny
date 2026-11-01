/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalLeadingSpace
public import LeanCanny.Algebra.ModularScalarFP

/-! # FP residues for the actual common leading scalar

Native denominator and original integer-leading residues suffice to compute
`a * Q^D * D`. The exponent and all arithmetic stay binary and modular,
including when the denominator residue is a nonunit.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalLeadingBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralFrozenPowerBits
set_option backward.isDefEq.respectTransparency false

theorem value_FP (S : Source) (a : Access S) (hQ : a.denominator ∈ FP) (hA : a.leading ∈ FP) : value S ∈ FP := by
  have HQ : (fun c => residueBits (S.denominator c : ZMod (S.modulus c))) ∈ FP :=
    mem_FP_of_eq hQ a.denominator_eq
  have HA : (fun c => residueBits (S.leading c : ZMod (S.modulus c))) ∈ FP :=
    mem_FP_of_eq hA a.leading_eq
  have HP := ModularScalarFP.pow a.modulus S.modulus_ne_zero S.allowance a.allowance
    (fun c => (S.denominator c : ZMod (S.modulus c))) HQ
  have HM := ModularScalarFP.mul a.modulus _ _ HA HP
  have HD := ModularScalarFP.natCast a.modulus S.allowance a.allowance
  have H := ModularScalarFP.mul a.modulus _ _ HM HD
  exact mem_FP_of_eq H (fun c => by simp only [value, Int.cast_mul, Int.cast_pow, Int.cast_natCast])

end LeanCanny.Algebra.IntegralCriticalLeadingBits
