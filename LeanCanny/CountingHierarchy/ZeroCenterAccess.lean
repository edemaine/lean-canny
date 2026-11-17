/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ZeroCenterCorrectness
public import LeanCanny.CountingHierarchy.QuotientCharacteristicEvaluation

/-! # Zero-center objective, Jacobian and relation access from source evaluations -/

public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM

/-- All three access programs are constructed from the same source evaluator.
The Jacobian and lower relations require only one additional function level. -/
theorem zeroEvaluationAccess_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p n ell u : α → ℕ} {value : α × List ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hn : ComputableInPolyTime n enc encUnary)
    (hell : ComputableInPolyTime ell enc encNat) (hu : ComputableInPolyTime u enc encNat)
    (hv : value ∈ CountingFunction a (encPair enc (encList encNat)) encNat) :
    ((fun q : α × List ℕ => zeroObjectiveValue (p q.1) (n q.1) (ell q.1) (u q.1)
      q.2 (fun y => value (q.1, y))) ∈ CountingFunction a (encPair enc (encList encNat)) encNat) ∧
    ((fun q : α × List ℕ => criticalJacobianValue (p q.1) (n q.1) (ell q.1) (u q.1)
      q.2 (fun y => value (q.1, y))) ∈ CountingFunction (a + 1) (encPair enc (encList encNat)) encNat) ∧
    ((fun q : α × (ℕ × List ℕ) => zeroLowerValue (p q.1) (n q.1) (u q.1)
      q.2.1 q.2.2 (fun y => value (q.1, y))) ∈
        CountingFunction (a + 1) (encPair enc (encPair encNat (encList encNat))) encNat) := by
  have hf := ComputableInPolyTime.fst enc (encList encNat)
  have hz := ComputableInPolyTime.snd enc (encList encNat)
  have hv' := CountingFunction.preprocess
    (input := encPair (encPair enc (encList encNat)) (encList encNat)) hv
    (g := fun q : (α × List ℕ) × List ℕ => (q.1.1, q.2)) (by fun_prop)
  have hobj := zeroObjectiveValue_mem (hp.comp hf) (hn.comp hf) (hell.comp hf) (hu.comp hf) hz hv'
  have hJ := criticalJacobianValue_mem (Decoder.pair E (Decoder.list Decoder.nat))
    (hp.comp hf) (hn.comp hf) (hell.comp hf) (hu.comp hf) hz hv'
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Function.comp_apply] using hobj
  · simpa only [Function.comp_apply] using hJ
  · have hf₂ := ComputableInPolyTime.fst enc (encPair encNat (encList encNat))
    have hi : ComputableInPolyTime (fun q : α × (ℕ × List ℕ) => q.2.1)
        (encPair enc (encPair encNat (encList encNat))) encNat := by fun_prop
    have hz₂ : ComputableInPolyTime (fun q : α × (ℕ × List ℕ) => q.2.2)
        (encPair enc (encPair encNat (encList encNat))) (encList encNat) := by fun_prop
    have hv₂ := CountingFunction.preprocess
      (input := encPair (encPair enc (encPair encNat (encList encNat))) (encList encNat)) hv
      (g := fun q : (α × (ℕ × List ℕ)) × List ℕ => (q.1.1, q.2)) (by fun_prop)
    simpa only [Function.comp_apply] using zeroLowerValue_mem
      (Decoder.pair E (Decoder.pair Decoder.nat (Decoder.list Decoder.nat)))
      (hp.comp hf₂) (hn.comp hf₂) (hu.comp hf₂) hi hz₂ hv₂

@[expose] noncomputable def zeroCoefficientValue (p n d u k : ℕ) (value : List ℕ → ℕ) : ℕ :=
  let ell := d + 1
  quotientCharacteristicValue p n ell (ell ^ n * (d + 2) + n * d) k
    (fun z => zeroObjectiveValue p n ell u z value)
    (fun z => criticalJacobianValue p n ell u z value)
    (fun i z => zeroLowerValue p n u i z value)

theorem zeroCoefficientValue_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p n d u k : α → ℕ} {value : α × List ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hn : ComputableInPolyTime n enc encUnary)
    (hd : ComputableInPolyTime d enc encNat) (hu : ComputableInPolyTime u enc encNat)
    (hk : ComputableInPolyTime k enc encNat)
    (hv : value ∈ CountingFunction a (encPair enc (encList encNat)) encNat) :
    (fun w => zeroCoefficientValue (p w) (n w) (d w) (u w) (k w) (fun y => value (w, y))) ∈
      CountingFunction (a + 9) enc encNat := by
  have hell := ComputableInPolyTime.binary_add' hd (.const 1)
  have haccess := zeroEvaluationAccess_mem E hp hn hell hu hv
  have hdim := ComputableInPolyTime.binary_pow' hell hn
  have hB := ComputableInPolyTime.binary_add'
    (ComputableInPolyTime.binary_mul' hdim (ComputableInPolyTime.binary_add' hd (.const 2)))
    (ComputableInPolyTime.binary_mul' (ComputableInPolyTime.unary_to_binary.comp hn) hd)
  have hcoeff := quotientCharacteristicValue_mem E hp hn hell hB hk
    (CountingFunction.mono (by omega : a ≤ a + 1) haccess.1) haccess.2.1 haccess.2.2
  simpa only [zeroCoefficientValue, Nat.add_assoc, Function.comp_apply] using hcoeff

end LeanCanny.CountingHierarchy
