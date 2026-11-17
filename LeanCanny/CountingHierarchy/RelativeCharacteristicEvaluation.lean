/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.FrozenCriticalCoefficients
public import LeanCanny.CountingHierarchy.BinaryPolynomialEvaluation
public import LeanCanny.CountingHierarchy.ControlledPreprocessing

/-! # Uniform relative characteristic evaluation from source access -/

@[expose] public section

namespace LeanCanny.CountingHierarchy.Controlled

open Cslib Cslib.Complexity Turing.MultiTapeTM

variable {α : Type} {n m : α → ℕ} {enc : α ↪ List Bool} {a : ℕ}
  {P : (w : α) → MvPolynomial (Fin (n w + m w)) ℤ}

noncomputable def relativeValue (C : Controlled P enc a) (d : α → ℕ)
    (q : α × (ℕ × List ℕ)) : ℕ :=
  binaryPolynomialValue q.2.1 ((d q.1 + 1) ^ n q.1) (q.2.2[0]?.getD 0)
    (fun k => zeroCoefficientValue q.2.1 (n q.1) (d q.1) (q.2.2[1]?.getD 0) k
      (fun y => C.evaluate (q.1, q.2.1, joinedPoint (n q.1) (m q.1) y (q.2.2.drop 2))))

theorem relativeValue_mem (C : Controlled P enc a) (E : Decoder enc)
    (hn : ComputableInPolyTime n enc encUnary) (hm : ComputableInPolyTime m enc encUnary)
    {d : α → ℕ} (hd : ComputableInPolyTime d enc encNat) :
    C.relativeValue d ∈ CountingFunction (a + 10) (encEvaluation enc) encNat := by
  let encQ := encEvaluation enc
  let encK := encPair encQ encNat
  have hw : ComputableInPolyTime (fun q : (α × (ℕ × List ℕ)) × ℕ => q.1.1) encK enc :=
    (ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.fst _ _)
  have hp : ComputableInPolyTime (fun q : (α × (ℕ × List ℕ)) × ℕ => q.1.2.1) encK encNat := by fun_prop
  have hz : ComputableInPolyTime (fun q : (α × (ℕ × List ℕ)) × ℕ => q.1.2.2)
      encK (encList encNat) := by fun_prop
  have hparams := (ComputableTidilyInPolyTime.listDropWithInput hz.tidy
    (ComputableTidilyInPolyTime.const 2)).computableInPolyTime
  have hu : ComputableInPolyTime (fun q : (α × (ℕ × List ℕ)) × ℕ => q.1.2.2[1]?.getD 0)
      encK encNat := by
    simpa only [List.getD_eq_getElem?_getD, Function.comp_apply] using
      ComputableInPolyTime.listGetD_binary 0 hz (ComputableInPolyTime.const 1)
  let CK := C.preprocess (fun q : (α × (ℕ × List ℕ)) × ℕ => q.1.1) hw
  let EK := Decoder.pair (Decoder.pair E (Decoder.pair Decoder.nat (Decoder.list Decoder.nat))) Decoder.nat
  have hc := CK.frozenCoefficient_mem EK (hn.comp hw) (hm.comp hw) hp (hd.comp hw) hu
    (ComputableInPolyTime.snd _ _) hparams
  have hq := ComputableInPolyTime.fst enc (encPair encNat (encList encNat))
  have hpq : ComputableInPolyTime (fun q : α × (ℕ × List ℕ) => q.2.1) encQ encNat := by fun_prop
  have hzq : ComputableInPolyTime (fun q : α × (ℕ × List ℕ) => q.2.2) encQ (encList encNat) := by fun_prop
  have ht : ComputableInPolyTime (fun q : α × (ℕ × List ℕ) => q.2.2[0]?.getD 0) encQ encNat := by
    simpa only [List.getD_eq_getElem?_getD, Function.comp_apply] using
      ComputableInPolyTime.listGetD_binary 0 hzq (ComputableInPolyTime.const 0)
  have hdim := ComputableInPolyTime.binary_pow'
    (ComputableInPolyTime.binary_add' (hd.comp hq) (.const 1)) (hn.comp hq)
  have hval := binaryPolynomialValue_mem
    (Decoder.pair E (Decoder.pair Decoder.nat (Decoder.list Decoder.nat))) hpq hdim ht hc
  change (fun q => C.relativeValue d q) ∈ _
  simpa only [relativeValue, frozenCoefficient, frozenEvaluate, preprocess, CK,
    Function.comp_apply, Nat.add_assoc] using hval

end LeanCanny.CountingHierarchy.Controlled
