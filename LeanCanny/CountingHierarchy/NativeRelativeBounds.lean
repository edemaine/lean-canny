/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.RelativeCharacteristicBounds
public import LeanCanny.CountingHierarchy.NativeNormBounds

/-! # Native binary budgets for relative critical-value families -/

public section

namespace LeanCanny.CountingHierarchy

open Cslib Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime

variable {α : Type} {enc : α ↪ List Bool}

@[fun_prop] theorem relativeRelationMassExponent_polyTime {d b : α → ℕ}
    (hd : ComputableInPolyTime d enc encNat) (hb : ComputableInPolyTime b enc encNat) :
    ComputableInPolyTime (fun w => relativeRelationMassExponent (d w) (b w)) enc encNat :=
  binary_add' (binary_add' (binarySize_polyTime (binary_add' hd (.const 1))) hb) (.const 1)

@[fun_prop] theorem relativeObjectiveMassExponent_polyTime {n d b : α → ℕ}
    (hn : ComputableInPolyTime n enc encNat) (hd : ComputableInPolyTime d enc encNat)
    (hb : ComputableInPolyTime b enc encNat) :
    ComputableInPolyTime (fun w => relativeObjectiveMassExponent (n w) (d w) (b w)) enc encNat :=
  binary_add' (binary_add'
    (binary_add' (binarySize_polyTime hn) (binarySize_polyTime (binary_add' hd (.const 2)))) hb) (.const 2)

@[fun_prop] theorem relativeNumeratorDegreeBound_polyTime {n d : α → ℕ}
    (hn : ComputableInPolyTime n enc encUnary) (hd : ComputableInPolyTime d enc encNat) :
    ComputableInPolyTime (fun w => relativeNumeratorDegreeBound (n w) (d w)) enc encNat :=
  binary_add' (binary_mul' (binary_pow' (binary_add' hd (.const 1)) hn) (binary_add' hd (.const 2)))
    (binary_mul' (unary_to_binary.comp hn) hd)

@[fun_prop] theorem relativeCharacteristicParameterDegreeBound_polyTime {n d : α → ℕ}
    (hn : ComputableInPolyTime n enc encUnary) (hd : ComputableInPolyTime d enc encNat) :
    ComputableInPolyTime (fun w => relativeCharacteristicParameterDegreeBound (n w) (d w)) enc encNat := by
  have hnb := unary_to_binary.comp hn
  have hdim := binary_pow' (binary_add' hd (.const 1)) hn
  have hH := binary_add' hd (ComputableInPolyTime.const 2)
  exact binary_mul' hdim (binary_add'
    (binary_add' (binary_mul' hdim hH) (binary_mul' hnb hH))
    (binary_mul' hnb (binary_mul' (relativeNumeratorDegreeBound_polyTime hn hd) hH)))

@[fun_prop] theorem relativeCharacteristicMassExponent_polyTime {n d b : α → ℕ}
    (hn : ComputableInPolyTime n enc encUnary) (hd : ComputableInPolyTime d enc encNat)
    (hb : ComputableInPolyTime b enc encNat) :
    ComputableInPolyTime (fun w => relativeCharacteristicMassExponent (n w) (d w) (b w)) enc encNat := by
  have h := quotientCharMassExponent_polyTime hn hd (binary_add' hd (.const 2))
    (relativeObjectiveMassExponent_polyTime (unary_to_binary.comp hn) hd hb)
    (relativeRelationMassExponent_polyTime hd hb)
  simpa only [relativeCharacteristicMassExponent, relativeNumeratorDegreeBound,
    quotientCharMassExponent, Function.comp_apply] using h

end LeanCanny.CountingHierarchy
