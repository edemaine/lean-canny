/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.FiniteCriticalNormBounds
public import LeanCanny.CountingHierarchy.NativeCriticalBounds
public import LeanCanny.CountingHierarchy.NativeRootLabelBounds

/-! # Native resource certificates for the second quotient norm -/

public section

namespace LeanCanny.CountingHierarchy

open Cslib Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime PurePowerResidue

variable {α : Type} {enc : α ↪ List Bool}

@[fun_prop] theorem criticalRootLabelLength_polyTime {n d : α → ℕ}
    (hn : ComputableInPolyTime n enc encUnary) (hd : ComputableInPolyTime d enc encNat) :
    ComputableInPolyTime (fun w => criticalRootLabelLength (n w) (d w)) enc encUnary :=
  ComputableInPolyTime.unary_mul.comp
    (hn.prod (ComputableInPolyTime.binary_size.comp (binary_add' hd (.const 1))))

@[fun_prop] theorem quotientCharMassExponent_polyTime {n d Ω bv br : α → ℕ}
    (hn : ComputableInPolyTime n enc encUnary) (hd : ComputableInPolyTime d enc encNat)
    (hΩ : ComputableInPolyTime Ω enc encNat) (hv : ComputableInPolyTime bv enc encNat)
    (hr : ComputableInPolyTime br enc encNat) :
    ComputableInPolyTime (fun w => quotientCharMassExponent (n w) (d w) (Ω w) (bv w) (br w))
      enc encNat := by
  have hnb := ComputableInPolyTime.unary_to_binary.comp hn
  have hdim := binary_pow' (binary_add' hd (.const 1)) hn
  have hJ := binary_add' (binary_mul' (binarySize_polyTime hnb) hnb)
    (binary_mul' hnb (binary_add' (binary_add'
      (binarySize_polyTime (binary_add' hd (.const 1))) hr) (.const 1)))
  have hB := binary_add' (binary_mul' hdim hΩ) (binary_mul' hnb hd)
  have ht := traceMassExponent_polyTime hnb hB hdim hv hr hJ
  exact binary_add' (binary_mul' ht hdim) (binarySize_polyTime (binary_add' hdim (.const 1)))

@[fun_prop] theorem criticalSpecializedRelationMassExponent_polyTime {n d b : α → ℕ}
    (hn : ComputableInPolyTime n enc encUnary) (hd : ComputableInPolyTime d enc encNat)
    (hb : ComputableInPolyTime b enc encNat) :
    ComputableInPolyTime (fun w => criticalSpecializedRelationMassExponent (n w) (d w) (b w))
      enc encNat :=
  binary_add' (criticalLowerMassExponent_polyTime (unary_to_binary.comp hn) hd hb)
    (criticalSpecializationExponent_polyTime hn hd hb)

@[fun_prop] theorem criticalSpecializedObjectiveMassExponent_polyTime {n d b : α → ℕ}
    (hn : ComputableInPolyTime n enc encUnary) (hd : ComputableInPolyTime d enc encNat)
    (hb : ComputableInPolyTime b enc encNat) :
    ComputableInPolyTime (fun w => criticalSpecializedObjectiveMassExponent (n w) (d w) (b w))
      enc encNat :=
  binary_add' (criticalObjectiveMassExponent_polyTime (unary_to_binary.comp hn) hd hb)
    (criticalSpecializationExponent_polyTime hn hd hb)

@[fun_prop] theorem criticalShiftedLabelDegreeBound_polyTime {n d b : α → ℕ}
    (hn : ComputableInPolyTime n enc encUnary) (hd : ComputableInPolyTime d enc encNat)
    (hb : ComputableInPolyTime b enc encNat) :
    ComputableInPolyTime (fun w => criticalShiftedLabelDegreeBound (n w) (d w) (b w))
      enc encNat :=
  sparseRootLabelDegreeBound_polyTime (binary_pow' (binary_add' hd (.const 1)) hn)
    (unary_to_binary.comp (criticalRootLabelLength_polyTime hn hd))
    (criticalLabelInputMassExponent_polyTime hn hd hb)

@[fun_prop] theorem criticalShiftedLabelMassExponent_polyTime {n d b : α → ℕ}
    (hn : ComputableInPolyTime n enc encUnary) (hd : ComputableInPolyTime d enc encNat)
    (hb : ComputableInPolyTime b enc encNat) :
    ComputableInPolyTime (fun w => criticalShiftedLabelMassExponent (n w) (d w) (b w))
      enc encNat := by
  have hD := binary_pow' (binary_add' hd (.const 1)) hn
  have hL := sparseRootLabelMassExponent_polyTime hD
    (unary_to_binary.comp (criticalRootLabelLength_polyTime hn hd))
    (criticalLabelInputMassExponent_polyTime hn hd hb)
  exact binary_add' (binary_add' hL (binarySize_polyTime hD)) (.const 3)

@[fun_prop] theorem criticalNormObjectiveDegreeBound_polyTime {n d b : α → ℕ}
    (hn : ComputableInPolyTime n enc encUnary) (hd : ComputableInPolyTime d enc encNat)
    (hb : ComputableInPolyTime b enc encNat) :
    ComputableInPolyTime (fun w => criticalNormObjectiveDegreeBound (n w) (d w) (b w))
      enc encNat :=
  binary_mul' (criticalShiftedLabelDegreeBound_polyTime hn hd hb) (binary_add' hd (.const 2))

@[fun_prop] theorem criticalNormObjectiveMassExponent_polyTime {n d b : α → ℕ}
    (hn : ComputableInPolyTime n enc encUnary) (hd : ComputableInPolyTime d enc encNat)
    (hb : ComputableInPolyTime b enc encNat) :
    ComputableInPolyTime (fun w => criticalNormObjectiveMassExponent (n w) (d w) (b w))
      enc encNat :=
  binary_add' (criticalShiftedLabelMassExponent_polyTime hn hd hb)
    (binary_mul' (criticalShiftedLabelDegreeBound_polyTime hn hd hb)
      (criticalSpecializedObjectiveMassExponent_polyTime hn hd hb))

@[fun_prop] theorem criticalNormMassExponent_polyTime {n d b : α → ℕ}
    (hn : ComputableInPolyTime n enc encUnary) (hd : ComputableInPolyTime d enc encNat)
    (hb : ComputableInPolyTime b enc encNat) :
    ComputableInPolyTime (fun w => criticalNormMassExponent (n w) (d w) (b w)) enc encNat :=
  quotientCharMassExponent_polyTime hn hd (criticalNormObjectiveDegreeBound_polyTime hn hd hb)
    (criticalNormObjectiveMassExponent_polyTime hn hd hb)
    (criticalSpecializedRelationMassExponent_polyTime hn hd hb)

end LeanCanny.CountingHierarchy
