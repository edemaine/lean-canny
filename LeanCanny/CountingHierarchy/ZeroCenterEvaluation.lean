/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.CriticalJacobianEvaluation

/-! # Native access to zero-center relative critical equations -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial PurePowerResidue
open scoped BigOperators Classical

noncomputable def zeroPotentialResidue (p n ell : ℕ) (z : List ℕ) : ℕ :=
  unaryModularSum n (max 1 p) (fun i => powMod p (z[i]?.getD 0) (ell + 1))

noncomputable def zeroLowerValue (p n u i : ℕ) (z : List ℕ) (value : List ℕ → ℕ) : ℕ :=
  modularSub p 0 (u * firstPartialResidue p n i z value)

noncomputable def zeroObjectiveValue (p n ell u : ℕ) (z : List ℕ) (value : List ℕ → ℕ) : ℕ :=
  (zeroPotentialResidue p n ell z + (ell + 1) * u * value z) % p

variable {α : Type} {enc : α ↪ List Bool} {a : ℕ}

theorem zeroPotentialResidue_mem {p n ell : α → ℕ} {z : α → List ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hn : ComputableInPolyTime n enc encUnary)
    (hell : ComputableInPolyTime ell enc encNat) (hz : ComputableInPolyTime z enc (encList encNat)) :
    (fun w => zeroPotentialResidue (p w) (n w) (ell w) (z w)) ∈ CountingFunction a enc encNat := by
  have hf := ComputableInPolyTime.fst enc encNat
  have hi := ComputableInPolyTime.snd enc encNat
  have hx : ComputableInPolyTime (fun q : α × ℕ => (z q.1)[q.2]?.getD 0) (encPair enc encNat) encNat := by
    simpa only [List.getD_eq_getElem?_getD, Function.comp_apply] using
      ComputableInPolyTime.listGetD_binary 0 (hz.comp hf) hi
  have ht := computableInPolyTime_powMod (hp.comp hf) hx
    (ComputableInPolyTime.binary_add' (hell.comp hf) (.const 1))
  simpa only [zeroPotentialResidue, Function.comp_apply] using
    unaryModularSum_mem hn (ComputableInPolyTime.binary_max' (.const 1) hp)
      (fun _ => lt_of_lt_of_le (by decide : 0 < 1) (le_max_left _ _)) (CountingFunction.of_polyTime ht)

theorem zeroLowerValue_mem (E : Decoder enc) {p n u i : α → ℕ}
    {z : α → List ℕ} {value : α × List ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hn : ComputableInPolyTime n enc encUnary)
    (hu : ComputableInPolyTime u enc encNat) (hi : ComputableInPolyTime i enc encNat)
    (hz : ComputableInPolyTime z enc (encList encNat))
    (hv : value ∈ CountingFunction a (encPair enc (encList encNat)) encNat) :
    (fun w => zeroLowerValue (p w) (n w) (u w) (i w) (z w) (fun y => value (w, y))) ∈
      CountingFunction (a + 1) enc encNat :=
  modularSub_mem (CountingFunction.of_polyTime hp) (CountingFunction.of_polyTime (ComputableInPolyTime.const 0))
    (CountingFunction.nat_mul (CountingFunction.of_polyTime hu) (firstPartialResidue_mem E hp hn hi hz hv))

theorem zeroObjectiveValue_mem {p n ell u : α → ℕ} {z : α → List ℕ} {value : α × List ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hn : ComputableInPolyTime n enc encUnary)
    (hell : ComputableInPolyTime ell enc encNat) (hu : ComputableInPolyTime u enc encNat)
    (hz : ComputableInPolyTime z enc (encList encNat))
    (hv : value ∈ CountingFunction a (encPair enc (encList encNat)) encNat) :
    (fun w => zeroObjectiveValue (p w) (n w) (ell w) (u w) (z w) (fun y => value (w, y))) ∈
      CountingFunction a enc encNat := by
  have hpotential := zeroPotentialResidue_mem (a := a) hp hn hell hz
  have hscale := ComputableInPolyTime.binary_mul' (ComputableInPolyTime.binary_add' hell (.const 1)) hu
  have hsource := CountingFunction.preprocess hv (ComputableInPolyTime.id'.prod hz)
  have hsum := CountingFunction.map (CountingFunction.prod hpotential
    (CountingFunction.nat_mul (CountingFunction.of_polyTime hscale) hsource)) ComputableInPolyTime.binary_add
  exact CountingFunction.nat_mod hsum (CountingFunction.of_polyTime hp)

end LeanCanny.CountingHierarchy
