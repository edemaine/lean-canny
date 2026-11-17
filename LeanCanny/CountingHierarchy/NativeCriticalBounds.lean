/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.FiniteCriticalData
public import LeanCanny.CountingHierarchy.NativeBinaryBounds

/-! # Native binary certificates for source-derived critical-value bounds -/

public section

namespace LeanCanny.CountingHierarchy

open Cslib Turing.MultiTapeTM Turing.MultiTapeTM.ComputableInPolyTime PurePowerResidue

variable {α : Type} {enc : α ↪ List Bool}

@[fun_prop] theorem potentialMassExponent_polyTime {n ell a : α → ℕ}
    (hn : ComputableInPolyTime n enc encNat) (hell : ComputableInPolyTime ell enc encNat)
    (ha : ComputableInPolyTime a enc encNat) :
    ComputableInPolyTime (fun w => potentialMassExponent (n w) (ell w) (a w)) enc encNat := by
  have he := binary_add' hell (.const 1)
  have hse := binarySize_polyTime he
  exact binary_add' (binarySize_polyTime hn)
    (binary_add' (binary_add' (binary_add' (binary_add' hse (binary_mul' hell ha)) (.const 1))
      (binary_add' hse (binary_mul' he ha))) (.const 1))

@[fun_prop] theorem criticalLowerMassExponent_polyTime {n d b : α → ℕ}
    (hn : ComputableInPolyTime n enc encNat) (hd : ComputableInPolyTime d enc encNat)
    (hb : ComputableInPolyTime b enc encNat) :
    ComputableInPolyTime (fun w => criticalLowerMassExponent (n w) (d w) (b w)) enc encNat := by
  have he := binary_add' hd (.const 1)
  have hc := binary_mul' hn (binarySize_polyTime (binary_mul' (.const 4) he))
  exact binary_add' (binary_add' (binary_mul' he hc)
    (binary_add' (binarySize_polyTime he) hb)) (.const 1)

@[fun_prop] theorem criticalObjectiveMassExponent_polyTime {n d b : α → ℕ}
    (hn : ComputableInPolyTime n enc encNat) (hd : ComputableInPolyTime d enc encNat)
    (hb : ComputableInPolyTime b enc encNat) :
    ComputableInPolyTime (fun w => criticalObjectiveMassExponent (n w) (d w) (b w)) enc encNat := by
  have he := binary_add' hd (.const 1)
  have hc := binary_mul' hn (binarySize_polyTime (binary_mul' (.const 4) he))
  exact binary_add' (binary_add' (potentialMassExponent_polyTime hn he hc)
    (binary_add' (binarySize_polyTime (binary_add' hd (.const 2))) hb)) (.const 1)

@[fun_prop] theorem traceMassExponent_polyTime {n B D bv br bJ : α → ℕ}
    (hn : ComputableInPolyTime n enc encNat) (hB : ComputableInPolyTime B enc encNat)
    (hD : ComputableInPolyTime D enc encNat) (hv : ComputableInPolyTime bv enc encNat)
    (hr : ComputableInPolyTime br enc encNat) (hJ : ComputableInPolyTime bJ enc encNat) :
    ComputableInPolyTime (fun w => traceMassExponent (n w) (B w) (D w) (bv w) (br w) (bJ w))
      enc encNat := by
  exact binary_add' (binary_add' (binary_add'
    (binary_mul' hn (binarySize_polyTime (binary_add' hB (.const 1))))
    (binary_mul' hD hv)) hJ) (binary_mul' (binary_mul' hB hn) hr)

@[fun_prop] theorem criticalValueMassExponent_polyTime {n d b : α → ℕ}
    (hn : ComputableInPolyTime n enc encUnary) (hd : ComputableInPolyTime d enc encNat)
    (hb : ComputableInPolyTime b enc encNat) :
    ComputableInPolyTime (fun w => criticalValueMassExponent (n w) (d w) (b w)) enc encNat := by
  have hnb := ComputableInPolyTime.unary_to_binary.comp hn
  have hdim : ComputableInPolyTime (fun w => (d w + 1) ^ n w) enc encNat :=
    ComputableInPolyTime.binary_pow' (ComputableInPolyTime.binary_add' hd (.const 1)) hn
  have hr := criticalLowerMassExponent_polyTime hnb hd hb
  have hv := criticalObjectiveMassExponent_polyTime hnb hd hb
  have hJ := binary_add' (binary_mul' (binarySize_polyTime hnb) hnb)
    (binary_mul' hnb (binary_add' (binary_add'
      (binarySize_polyTime (binary_add' hd (.const 1))) hr) (.const 1)))
  have hB := binary_add' (binary_mul' hdim (binary_add' hd (.const 2))) (binary_mul' hnb hd)
  have ht := traceMassExponent_polyTime hnb hB hdim hv hr hJ
  exact binary_add' (binary_mul' ht hdim) (binarySize_polyTime (binary_add' hdim (.const 1)))

@[fun_prop] theorem criticalValueParameterDegreeBound_polyTime {n d : α → ℕ}
    (hn : ComputableInPolyTime n enc encUnary) (hd : ComputableInPolyTime d enc encNat) :
    ComputableInPolyTime (fun w => criticalValueParameterDegreeBound (n w) (d w)) enc encNat := by
  have hnb := ComputableInPolyTime.unary_to_binary.comp hn
  have hdim : ComputableInPolyTime (fun w => (d w + 1) ^ n w) enc encNat :=
    ComputableInPolyTime.binary_pow' (ComputableInPolyTime.binary_add' hd (.const 1)) hn
  exact binary_mul' hdim (binary_add' (binary_add' hdim hnb)
    (binary_mul' hnb (binary_add' (binary_mul' hdim (binary_add' hd (.const 2)))
      (binary_mul' hnb hd))))

@[fun_prop] theorem criticalParameterExponent_polyTime {D H : α → ℕ}
    (hD : ComputableInPolyTime D enc encNat) (hH : ComputableInPolyTime H enc encNat) :
    ComputableInPolyTime (fun w => criticalParameterExponent (D w) (H w)) enc encNat := by
  have ht := binary_mul' (.const 2) hD
  have hdisc := binary_add' (binary_mul' (binarySize_polyTime ht) ht)
    (binary_mul' ht (binary_add' hH (binarySize_polyTime hD)))
  exact binary_add' (binary_add' (binary_add' hdisc hH)
    (binary_mul' hD (binary_add' hH (.const 2)))) (.const 2)

@[fun_prop] theorem criticalSpecializationExponent_polyTime {n d b : α → ℕ}
    (hn : ComputableInPolyTime n enc encUnary) (hd : ComputableInPolyTime d enc encNat)
    (hb : ComputableInPolyTime b enc encNat) :
    ComputableInPolyTime (fun w => criticalSpecializationExponent (n w) (d w) (b w)) enc encNat := by
  have hdim : ComputableInPolyTime (fun w => (d w + 1) ^ n w) enc encNat :=
    ComputableInPolyTime.binary_pow' (ComputableInPolyTime.binary_add' hd (.const 1)) hn
  exact criticalParameterExponent_polyTime hdim (criticalValueMassExponent_polyTime hn hd hb)

@[fun_prop] theorem criticalLabelInputMassExponent_polyTime {n d b : α → ℕ}
    (hn : ComputableInPolyTime n enc encUnary) (hd : ComputableInPolyTime d enc encNat)
    (hb : ComputableInPolyTime b enc encNat) :
    ComputableInPolyTime (fun w => criticalLabelInputMassExponent (n w) (d w) (b w)) enc encNat := by
  have hmass := criticalValueMassExponent_polyTime hn hd hb
  have hparameter := criticalSpecializationExponent_polyTime hn hd hb
  have hdegree := criticalValueParameterDegreeBound_polyTime hn hd
  exact binary_add' (binary_add' (binary_add' hmass (binary_mul' hparameter hdegree))
    (binary_add' hmass (.const 2))) (.const 2)

end LeanCanny.CountingHierarchy
