/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ChoiceTupleEncoding
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-! # Native decoding and polynomial widths for the bounded two-block choices -/

public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

@[fun_prop] theorem choiceTupleBound_polyTime {N H D : α → ℕ}
    (hN : ComputableInPolyTime N enc encNat) (hH : ComputableInPolyTime H enc encNat)
    (hD : ComputableInPolyTime D enc encNat) :
    ComputableInPolyTime (fun w => choiceTupleBound (N w) (H w) (D w)) enc encNat := by
  have hmu := ComputableInPolyTime.binary_mul' (ComputableInPolyTime.const 2)
    (ComputableInPolyTime.binary_add' (ComputableInPolyTime.binary_pow' hD (.const 3)) (.const 2))
  have ht := ComputableInPolyTime.binary_add'
    (ComputableInPolyTime.binary_mul' (.const 2) (ComputableInPolyTime.binary_mul' hD hmu)) (.const 1)
  exact ComputableInPolyTime.binary_max' hN (ComputableInPolyTime.binary_max' hH
    (ComputableInPolyTime.binary_max' hmu ht))

@[fun_prop] theorem choiceTupleWidth_polyTime {N H D n : α → ℕ}
    (hN : ComputableInPolyTime N enc encNat) (hH : ComputableInPolyTime H enc encNat)
    (hD : ComputableInPolyTime D enc encNat) (hn : ComputableInPolyTime n enc encUnary) :
    ComputableInPolyTime (fun w => choiceTupleWidth (N w) (H w) (D w) (n w)) enc encUnary :=
  natTupleWitnessWidth_polyTime (choiceTupleBound_polyTime hN hH hD)
    (ComputableInPolyTime.unary_add' (.const 1) (ComputableInPolyTime.unary_mul' (.const 4) hn))

@[fun_prop] theorem choiceEntry_polyTime {word : α → List Bool} {i j : α → ℕ}
    (hw : ComputableInPolyTime word enc encBits) (hi : ComputableInPolyTime i enc encNat)
    (hj : ComputableInPolyTime j enc encNat) :
    ComputableInPolyTime (fun w => choiceEntry (word w) (i w) (j w)) enc encNat := by
  have hpos := ComputableInPolyTime.binary_add'
    (ComputableInPolyTime.binary_add' (.const 1) (ComputableInPolyTime.binary_mul' (.const 4) hi)) hj
  simpa only [choiceEntry, List.getD_eq_getElem?_getD, Function.comp_def] using
    ComputableInPolyTime.listGetD_binary 0 (natTupleWord_polyTime.comp hw) hpos

@[fun_prop] theorem choiceDegree_polyTime {N : α → ℕ} {word : α → List Bool}
    (hN : ComputableInPolyTime N enc encNat) (hw : ComputableInPolyTime word enc encBits) :
    ComputableInPolyTime (fun w => (choiceDegree (N w) (word w)).val) enc encNat := by
  have hraw := ComputableInPolyTime.listGetD_binary (encA := encNat) 0 (natTupleWord_polyTime.comp hw)
    (ComputableInPolyTime.const 0)
  simpa only [choiceDegree, List.getD_eq_getElem?_getD, Function.comp_def] using
    ComputableInPolyTime.binary_mod.comp (hraw.prod (ComputableInPolyTime.binary_add' hN (.const 1)))

@[fun_prop] theorem choiceIndex_polyTime {H i : α → ℕ} {word : α → List Bool}
    (hH : ComputableInPolyTime H enc encNat) (hi : ComputableInPolyTime i enc encNat)
    (hw : ComputableInPolyTime word enc encBits) :
    ComputableInPolyTime (fun w => choiceIndex (H w) (word w) (i w)) enc encNat :=
  ComputableInPolyTime.binary_mod.comp ((choiceEntry_polyTime hw hi (.const 0)).prod
    (ComputableInPolyTime.binary_add' hH (.const 1)))

@[fun_prop] theorem choiceLabel_modulus_polyTime {D i : α → ℕ} {word : α → List Bool}
    (hD : ComputableInPolyTime D enc encNat) (hi : ComputableInPolyTime i enc encNat)
    (hw : ComputableInPolyTime word enc encBits) :
    ComputableInPolyTime (fun w => (choiceLabel (D w) (word w) (i w)).modulus) enc encNat :=
  normalizedFingerprintModulus_polyTime hD (choiceEntry_polyTime hw hi (.const 1))

@[fun_prop] theorem choiceLabel_parameter_polyTime {D i : α → ℕ} {word : α → List Bool}
    (hD : ComputableInPolyTime D enc encNat) (hi : ComputableInPolyTime i enc encNat)
    (hw : ComputableInPolyTime word enc encBits) :
    ComputableInPolyTime (fun w => (choiceLabel (D w) (word w) (i w)).parameter) enc encNat :=
  normalizedFingerprintData_parameter_polyTime hD (choiceEntry_polyTime hw hi (.const 1))
    (choiceEntry_polyTime hw hi (.const 2))

@[fun_prop] theorem choiceLabel_target_polyTime {D i : α → ℕ} {word : α → List Bool}
    (hD : ComputableInPolyTime D enc encNat) (hi : ComputableInPolyTime i enc encNat)
    (hw : ComputableInPolyTime word enc encBits) :
    ComputableInPolyTime (fun w => (choiceLabel (D w) (word w) (i w)).target) enc encIntBin :=
  normalizedFingerprintData_target_polyTime hD (choiceEntry_polyTime hw hi (.const 1))
    (choiceEntry_polyTime hw hi (.const 3))

end LeanCanny.CountingHierarchy
