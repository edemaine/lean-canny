/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.UnaryModularAggregation
public import LeanCanny.CountingHierarchy.ModularArithmetic
public import LeanCanny.CountingHierarchy.RootLabelPolynomial

/-! # Evaluating cleared root labels without increasing the counting level

Only the number of sign tests is charged in unary. Each product omitting a
single denominator and the outer sum use the same fixed counting oracle.
-/

public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM

@[expose] noncomputable def modularClearedNumerator (p m : ℕ)
    (den num : ℕ → ℕ) (i : ℕ) : ℕ :=
  (num i * unaryModularProduct m p (fun j => if j = i then 1 else den j)) % p

@[expose] noncomputable def modularRootLabel (p m : ℕ)
    (den num target : ℕ → ℕ) : ℕ :=
  let E := unaryModularProduct m p den
  modularSub p (powMod p E 2) (4 * unaryModularSum m p (fun i =>
    powMod p (modularSub p (modularClearedNumerator p m den num i) (target i * E)) 2))

theorem modularClearedNumerator_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    {p m : α → ℕ} {den num : α × ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat)
    (hm : ComputableInPolyTime m enc encUnary) (hpos : ∀ w, 0 < p w)
    (hden : den ∈ CountingFunction a (encPair enc encNat) encNat)
    (hnum : num ∈ CountingFunction a (encPair enc encNat) encNat) :
    (fun q : α × ℕ => modularClearedNumerator (p q.1) (m q.1)
      (fun j => den (q.1, j)) (fun j => num (q.1, j)) q.2) ∈
        CountingFunction a (encPair enc encNat) encNat := by
  have hp' := hp.comp (ComputableInPolyTime.fst enc encNat)
  have hm' := hm.comp (ComputableInPolyTime.fst enc encNat)
  have hden' := CountingFunction.preprocess
    (input := encPair (encPair enc encNat) encNat) hden
    (g := fun q : (α × ℕ) × ℕ => (q.1.1, q.2)) (by fun_prop)
  have htest : ComputableInPolyTime
      (fun q : (α × ℕ) × ℕ => decide (q.2 = q.1.2))
      (encPair (encPair enc encNat) encNat) encBool := by fun_prop
  have hfactor := CountingFunction.ite (CountingFunction.of_polyTime htest)
    (CountingFunction.of_polyTime (ComputableInPolyTime.const 1)) hden'
  simp only [decide_eq_true_eq] at hfactor
  have hprod := unaryModularProduct_mem hm' hp' (fun q => hpos q.1) hfactor
  simpa only [modularClearedNumerator, Function.comp_apply] using
    CountingFunction.nat_mod (CountingFunction.nat_mul hnum hprod)
      (CountingFunction.of_polyTime hp')

/-- The squared-error score has polynomially many tests, even when its
expanded integer polynomial has exponentially many coefficients. -/
theorem modularRootLabel_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    {p m : α → ℕ} {den num target : α × ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat)
    (hm : ComputableInPolyTime m enc encUnary) (hpos : ∀ w, 0 < p w)
    (hden : den ∈ CountingFunction a (encPair enc encNat) encNat)
    (hnum : num ∈ CountingFunction a (encPair enc encNat) encNat)
    (htarget : target ∈ CountingFunction a (encPair enc encNat) encNat) :
    (fun w => modularRootLabel (p w) (m w)
      (fun j => den (w, j)) (fun j => num (w, j)) (fun j => target (w, j))) ∈
        CountingFunction a enc encNat := by
  have hE := unaryModularProduct_mem hm hp hpos hden
  have hE' := CountingFunction.preprocess hE (ComputableInPolyTime.fst enc encNat)
  have hp' := hp.comp (ComputableInPolyTime.fst enc encNat)
  have hcleared := modularClearedNumerator_mem hp hm hpos hden hnum
  have hdiff := modularSub_mem (CountingFunction.of_polyTime hp') hcleared
    (CountingFunction.nat_mul htarget hE')
  have hsquare := CountingFunction.powMod (CountingFunction.of_polyTime hp') hdiff
    (CountingFunction.of_polyTime (ComputableInPolyTime.const 2))
  have hsum := unaryModularSum_mem hm hp hpos hsquare
  have hfour := CountingFunction.nat_mul
    (CountingFunction.of_polyTime (ComputableInPolyTime.const 4)) hsum
  have hEsq := CountingFunction.powMod (CountingFunction.of_polyTime hp) hE
    (CountingFunction.of_polyTime (ComputableInPolyTime.const 2))
  simpa only [modularRootLabel, Function.comp_apply] using
    modularSub_mem (CountingFunction.of_polyTime hp) hEsq hfour

end LeanCanny.CountingHierarchy
