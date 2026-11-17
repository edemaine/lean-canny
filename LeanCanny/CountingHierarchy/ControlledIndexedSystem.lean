/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.IndexedEquationPositivity
public import LeanCanny.CountingHierarchy.ControlledAppendVariables
public import LeanCanny.CountingHierarchy.ControlledBounds
public import LeanCanny.CountingHierarchy.ControlledSumSquares
public import LeanCanny.CountingHierarchy.ControlledSelection

/-! # Uniform existential systems of controlled equations and strict inequalities -/

@[expose] public section

namespace LeanCanny.CountingHierarchy.Controlled

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial
open scoped BigOperators

noncomputable def indexedSystem {α : Type} {n : α → ℕ} {enc : α ↪ List Bool} {a : ℕ}
    {P Q : (w : α) → ℕ → MvPolynomial (Fin (n w)) ℤ}
    (CP : Controlled (fun q : α × ℕ => P q.1 q.2) (encPair enc encNat) a)
    (CQ : Controlled (fun q : α × ℕ => Q q.1 q.2) (encPair enc encNat) a)
    (E : Decoder enc) (hn : ComputableInPolyTime n enc encUnary)
    (e k D b cutoff : α → ℕ) (he : ComputableInPolyTime e enc encNat)
    (hk : ComputableInPolyTime k enc encUnary) (hD : ComputableInPolyTime D enc encNat)
    (hb : ComputableInPolyTime b enc encNat) (hc : ComputableInPolyTime cutoff enc encNat)
    (hPdeg : ∀ w i, (P w i).totalDegree ≤ D w)
    (hQdeg : ∀ w i, (Q w i).totalDegree ≤ D w)
    (hPmass : ∀ w i, LeanCanny.Algebra.MvMass.mass (P w i) ≤ 2 ^ b w)
    (hQmass : ∀ w i, LeanCanny.Algebra.MvMass.mass (Q w i) ≤ 2 ^ b w)
    (hPcut : ∀ w i, CP.cutoff (w, i) ≤ cutoff w) (hQcut : ∀ w i, CQ.cutoff (w, i) ≤ cutoff w) :
    Controlled (fun w => indexedEquationPositivityPolynomial (P w) (Q w) (e w) (k w)) enc (a + 1) := by
  have hf := ComputableInPolyTime.fst enc encNat
  have hi := ComputableInPolyTime.snd enc encNat
  let CP' := CP.withBounds (fun q => D q.1) (fun q => b q.1) (fun q => cutoff q.1)
    (hD.comp hf) (hb.comp hf) (hc.comp hf) (fun q => hPdeg q.1 q.2) (fun q => hPmass q.1 q.2) (fun q => hPcut q.1 q.2)
  let CQ' := CQ.withBounds (fun q => D q.1) (fun q => b q.1) (fun q => cutoff q.1)
    (hD.comp hf) (hb.comp hf) (hc.comp hf) (fun q => hQdeg q.1 q.2) (fun q => hQmass q.1 q.2) (fun q => hQcut q.1 q.2)
  let CPpad := CP'.appendVariables (fun q => k q.1) (hk.comp hf)
  let CQpad := CQ'.appendVariables (fun q => k q.1) (hk.comp hf)
  have htot := ComputableInPolyTime.unary_add' (hn.comp hf) (hk.comp hf)
  have hindex := ComputableInPolyTime.binary_add'
    ((ComputableInPolyTime.unary_to_binary.comp hn).comp hf) hi
  let CO := optionalCoordinate (a := a) htot hindex
  let one := constant (a := a) htot (fun _ => (1 : ℤ)) (ComputableInPolyTime.const 1)
  let CS := (CQpad.mul (CO.pow (fun _ => 2) (ComputableInPolyTime.const 2))).sub one
  let ds : α → ℕ := fun w => CS.degreeBound (w, 0)
  let bs : α → ℕ := fun w => CS.massExponent (w, 0)
  let cuts : α → ℕ := fun w => CS.cutoff (w, 0)
  have hzero : ComputableInPolyTime (fun w : α => (w, (0 : ℕ))) enc (encPair enc encNat) :=
    ComputableInPolyTime.id'.prod (ComputableInPolyTime.const 0)
  have hpSum := sumSquares (P := fun w i => MvPolynomial.rename (Fin.castAdd (k w)) (P w i))
    CPpad E (ComputableInPolyTime.unary_add' hn hk) e D b cutoff he hD hb hc
    (fun w i _ => CPpad.degree_le (w, i)) (fun w i _ => CPpad.mass_le (w, i)) (fun _ _ _ => le_rfl)
  have hqSum := sumSquares (P := fun w i => MvPolynomial.rename (Fin.castAdd (k w)) (Q w i) *
      LeanCanny.CountingHierarchy.optionalCoordinate (n w + k w) (n w + i) ^ 2 - MvPolynomial.C 1)
    CS E (ComputableInPolyTime.unary_add' hn hk) k ds bs cuts
    (ComputableInPolyTime.unary_to_binary.comp hk)
    (CS.degree_computable.comp hzero) (CS.mass_computable.comp hzero) (CS.cutoff_computable.comp hzero)
    (fun w i _ => by
      have h := CS.degree_le (w, i)
      have heq : CS.degreeBound (w, i) = ds w := rfl
      simpa only [Function.comp_def, heq] using h)
    (fun w i _ => by
      have h := CS.mass_le (w, i)
      have heq : CS.massExponent (w, i) = bs w := rfl
      simpa only [Function.comp_def, heq] using h)
    (fun _ _ _ => le_rfl)
  simpa only [indexedEquationPositivityPolynomial, MvPolynomial.C_1] using hpSum.add hqSum

end LeanCanny.CountingHierarchy.Controlled
