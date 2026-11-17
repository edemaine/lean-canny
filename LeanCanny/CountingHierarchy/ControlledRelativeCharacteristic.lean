/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.RelativeCharacteristicCorrectness
public import LeanCanny.CountingHierarchy.NativeRelativeBounds

/-! # Controlled relative critical-value polynomials with source-only bounds -/

@[expose] public section

namespace LeanCanny.CountingHierarchy.Controlled

open Cslib Cslib.Complexity Turing.MultiTapeTM

variable {α : Type} {n m : α → ℕ} {enc : α ↪ List Bool} {a : ℕ}
  {P : (w : α) → MvPolynomial (Fin (n w + m w)) ℤ}

noncomputable def relativeCharacteristicOfDegree (C : Controlled P enc a) (E : Decoder enc)
    (hn : ComputableInPolyTime n enc encUnary) (hm : ComputableInPolyTime m enc encUnary)
    (d : α → ℕ) (hd : ComputableInPolyTime d enc encNat) (hpos : ∀ w, 1 ≤ d w)
    (hdeg : ∀ w, (P w).totalDegree ≤ d w + 1) :
    Controlled (fun w => finiteRelativeCharacteristic (d w) (P w) (hdeg w)) enc (a + 10) where
  arity_computable := ComputableInPolyTime.unary_add' hm (.const 2)
  degreeBound w := (d w + 1) ^ n w + relativeCharacteristicParameterDegreeBound (n w) (d w)
  degree_computable := ComputableInPolyTime.binary_add'
    (ComputableInPolyTime.binary_pow' (ComputableInPolyTime.binary_add' hd (.const 1)) hn)
    (relativeCharacteristicParameterDegreeBound_polyTime hn hd)
  degree_le w := finiteRelativeCharacteristic_degree_le _ (hpos w) _ _
  massExponent w := relativeCharacteristicMassExponent (n w) (d w) (C.massExponent w)
  mass_computable := relativeCharacteristicMassExponent_polyTime hn hd C.mass_computable
  mass_le w := finiteRelativeCharacteristic_mass_le _ _ (hpos w) _ _ (C.mass_le w)
  cutoff w := max (C.cutoff w) (criticalCoefficientPrimeCutoff (n w) (d w))
  cutoff_computable := ComputableInPolyTime.binary_max' C.cutoff_computable
    (criticalCoefficientPrimeCutoff_polyTime hn hd)
  evaluate := C.relativeValue d
  evaluate_mem := C.relativeValue_mem E hn hm hd
  evaluate_eq w p z hp hcut := C.relativeValue_eq _ w p z hp
    ((le_max_left _ _).trans_lt hcut) (hpos w) _ ((le_max_right _ _).trans_lt hcut)

/-- An even degree majorant makes the zero-center potential coercive over the reals. -/
noncomputable def relativeCharacteristic (C : Controlled P enc a) (E : Decoder enc)
    (hn : ComputableInPolyTime n enc encUnary) (hm : ComputableInPolyTime m enc encUnary) :
    Controlled (fun w => finiteRelativeCharacteristic (2 * (C.degreeBound w + 1)) (P w)
      ((C.degree_le w).trans (by omega))) enc (a + 10) :=
  C.relativeCharacteristicOfDegree E hn hm (fun w => 2 * (C.degreeBound w + 1))
    (ComputableInPolyTime.binary_mul' (.const 2)
      (ComputableInPolyTime.binary_add' C.degree_computable (.const 1)))
    (fun _ => by omega) (fun w => (C.degree_le w).trans (by omega))

end LeanCanny.CountingHierarchy.Controlled
