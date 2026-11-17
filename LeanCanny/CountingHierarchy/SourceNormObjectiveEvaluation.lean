/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.SourceRootLabelEvaluation
public import LeanCanny.CountingHierarchy.PolynomialEvaluationComposition

/-! # Evaluating the actual second-quotient objective from source access -/

public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM

@[expose] def sourceCodedLabel (n d : ℕ) (data : List (ℕ × ℕ)) :
    List (Fin ((d + 1) ^ n) × SignType) :=
  codedRootLabel ((d + 1) ^ n) (criticalRootLabelLength n d) (by positivity) data

@[expose] def sourceNormShift (n d e : ℕ) : ℕ := e % ((d + 1) ^ n + 1)

theorem sourceNormShift_le (n d e : ℕ) : sourceNormShift n d e ≤ (d + 1) ^ n := by
  exact Nat.le_of_lt_succ (Nat.mod_lt _ (Nat.succ_pos _))

@[expose] noncomputable def codedCriticalNormObjective {n : ℕ} (d b : ℕ)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1)
    (data : List (ℕ × ℕ)) (e : ℕ) : MvPolynomial (Fin n) ℤ :=
  finiteCriticalNormObjective d b F hF (sourceCodedLabel n d data) (sourceNormShift n d e)

@[expose] noncomputable def sourceNormObjectiveValue (p n d b e : ℕ) (z : List ℕ)
    (data : List (ℕ × ℕ)) (value : List ℕ → ℕ) : ℕ :=
  modularSub p (sourceNormShift n d e) (4 * (d + 1) ^ n *
    sourceRootLabelValue p n d b
      (criticalObjectiveValue p n (d + 1) (criticalParameterResidue p n d b) z value) data value)

/-- Adaptive composition evaluates the label at the implicit objective value,
while retaining the original source context. It does not add a counting level. -/
theorem sourceNormObjectiveValue_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p n d b e : α → ℕ} {z : α → List ℕ} {data : α → List (ℕ × ℕ)}
    {value : α × List ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hn : ComputableInPolyTime n enc encUnary)
    (hd : ComputableInPolyTime d enc encNat) (hb : ComputableInPolyTime b enc encNat)
    (he : ComputableInPolyTime e enc encNat)
    (hz : ComputableInPolyTime z enc (encList encNat))
    (hdata : ComputableInPolyTime data enc encRootLabelCode)
    (hv : value ∈ CountingFunction a (encPair enc (encList encNat)) encNat) :
    (fun w => sourceNormObjectiveValue (p w) (n w) (d w) (b w) (e w) (z w) (data w)
      (fun y => value (w, y))) ∈ CountingFunction (a + 13) enc encNat := by
  have hell := ComputableInPolyTime.binary_add' hd (.const 1)
  have hu := criticalParameterResidue_polyTime hp hn hd hb
  have hobj := criticalObjectiveValue_mem hp hn hell hu hz hv
  have hf := ComputableInPolyTime.fst enc encNat
  have hx := ComputableInPolyTime.snd enc encNat
  have hv' := CountingFunction.preprocess
    (input := encPair (encPair enc encNat) (encList encNat)) hv
    (g := fun q : (α × ℕ) × List ℕ => (q.1.1, q.2)) (by fun_prop)
  have hlabel := sourceRootLabelValue_mem (Decoder.pair E Decoder.nat)
    (hp.comp hf) (hn.comp hf) (hd.comp hf) (hb.comp hf) hx (hdata.comp hf) hv'
  have hcomp := CountingFunction.comp_with hlabel (CountingFunction.mono (by omega : a ≤ a + 13) hobj)
  have hD := ComputableInPolyTime.binary_pow' hell hn
  have hshift := ComputableInPolyTime.binary_mod.comp
    (he.prod (ComputableInPolyTime.binary_add' hD (.const 1)))
  have hscale := ComputableInPolyTime.binary_mul' (ComputableInPolyTime.const 4) hD
  simpa only [sourceNormObjectiveValue, sourceNormShift, Function.comp_apply] using
    modularSub_mem (CountingFunction.of_polyTime hp) (CountingFunction.of_polyTime hshift)
      (CountingFunction.nat_mul (CountingFunction.of_polyTime hscale) hcomp)

/-- The modular objective is the actual source multivariate polynomial
used for the final quotient determinant, including the bounded shift. -/
theorem sourceNormObjectiveValue_cast {p n : ℕ} [Fact p.Prime]
    (d : ℕ) (hd : 1 ≤ d) (b e : ℕ) (F : MvPolynomial (Fin n) ℤ)
    (hF : F.totalDegree ≤ d + 1) (hcut : criticalCoefficientPrimeCutoff n d < p)
    (z : List ℕ) (data : List (ℕ × ℕ)) (value : List ℕ → ℕ)
    (hv : ∀ y, (value y : ZMod p) = MvPolynomial.eval
      (fun i : Fin n => ((y[i.val]?.getD 0 : ℕ) : ZMod p)) (F.map (Int.castRingHom (ZMod p)))) :
    (sourceNormObjectiveValue p n d b e z data value : ZMod p) =
      MvPolynomial.eval (fun i : Fin n => ((z[i.val]?.getD 0 : ℕ) : ZMod p))
        ((codedCriticalNormObjective d b F hF data e).map (Int.castRingHom (ZMod p))) := by
  have hobj := (sourceCriticalEvaluation_cast d b F hF hcut z value hv).1
  have hlabel := sourceRootLabelValue_cast d hd b
    (criticalObjectiveValue p n (d + 1) (criticalParameterResidue p n d b) z value)
    F hF hcut data value hv
  rw [sourceNormObjectiveValue, modularSub_cast (Fact.out : p.Prime).pos,
    Nat.cast_mul, Nat.cast_mul, hlabel,
    codedCriticalNormObjective, finiteCriticalNormObjective, eval_map_polynomial_aeval,
    finiteCriticalShiftedLabel, ← hobj, shiftedIntegerLabel]
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Int.coe_castRingHom, Int.cast_mul, Int.cast_neg, Int.cast_ofNat, Int.cast_natCast, Nat.cast_ofNat,
    sourceCodedLabel]
  ring

end LeanCanny.CountingHierarchy
