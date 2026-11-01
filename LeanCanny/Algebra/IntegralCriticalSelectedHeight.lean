/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalHeightValue
public import LeanCanny.Algebra.IntegralCriticalTotalCompanionSource
/-! # Selected common-cleared heights at actual creating states -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalScript
open LeanCanny.Encoding MatrixPower FixedWidthPolynomial UniformIntegralPrefix
open scoped Classical
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] Prefix.elementEntry

theorem State.clearedEntry_family {S B n W D C m : ℕ} (x : State S B n W D C m)
    (hm : m ≤ S) (command : Command n W D C) (select : ℕ → ℕ)
    (hs : ∀ j : Fin (n + 1), select j.val = command.selected j) (i r t modulus : ℕ) :
    x.clearedEntry select i r t modulus =
      IntegralHistoryCriticalBits.heightValue (family x hm command) i r t modulus := by
  unfold State.clearedEntry IntegralHistoryCriticalBits.heightValue
  apply congrArg (fun H => x.scalarPrefix.elementEntry H _ _ modulus)
  let pick (z : ℕ) : Option (Fin m) := if hz : z < m then some ⟨z, hz⟩ else none
  have HP (j : Fin (n + 1)) : pick (select j.val) = command.select m j :=
    congrArg pick (hs j)
  change CoordinateFrozenCriticalElimination.numerators
    (fun j : Fin (n + 1) => x.bank.selectedDenominator (pick (select j.val)))
    (fun j => x.bank.selectedNumerator (pick (select j.val))) i =
    CoordinateFrozenCriticalElimination.numerators
      (fun j => x.bank.selectedDenominator (command.select m j))
      (fun j => x.bank.selectedNumerator (command.select m j)) i
  simp only [HP]

theorem family_stateAt_congr {S B n W D C : ℕ} (rules : List (Command n W D C))
    (hl : rules.length ≤ S + 1) (hN : PurePowerReductionBounds.dimension (n + 1) D ≤ 2 ^ B)
    (a b : ℕ) (ha : (past rules a).length ≤ S) (hb : (past rules b).length ≤ S)
    (command : Command n W D C) (h : a = b) :
    family (stateAt rules hl hN a) ha command = family (stateAt rules hl hN b) hb command := by
  subst b
  rfl

end LeanCanny.Algebra.IntegralCriticalScript

namespace LeanCanny.Algebra.IntegralCriticalTotalHeightBits
open LeanCanny.Encoding MatrixPower FixedWidthPolynomial UniformIntegralPrefix
open IntegralCriticalScript IntegralCriticalTotalCompanionBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem selector_creating (F : Scripts) (q : List Bool) (h : valid F q)
    (i : Fin (F.ambient (root q) + 1)) :
    IntegralCriticalFlatClearedHeightBits.selector F q i.val =
      (chosen (F.rules (root q)) (IntegralCriticalFlatHeightBits.creatingIndex F q h)).selected i := by
  unfold IntegralCriticalFlatClearedHeightBits.selector IntegralCriticalScriptFP.selector
  rw [commandAt_creating F q h]
  exact dite_eq_left i.isLt

theorem prefix_family (F : Scripts) (q : List Bool) (h : valid F q)
    (hm : (past (F.rules (root q)) (IntegralCriticalFlatHeightBits.length F q)).length ≤ F.cap (root q)) :
    IntegralCriticalScript.family
      (stateAt (F.rules (root q)) (F.length_le (root q)) (F.scalar_bound (root q))
        (IntegralCriticalFlatHeightBits.length F q)) hm
      (chosen (F.rules (root q)) (IntegralCriticalFlatHeightBits.creatingIndex F q h)) =
      IntegralCriticalFlatHeightBits.creatingFamily F q h := by
  have HL : IntegralCriticalFlatHeightBits.length F q = IntegralCriticalHistoryTask.birth F.toParameters q :=
    (past_length _ _).trans (min_eq_left h.le)
  have HE : IntegralCriticalFlatHeightBits.length F q =
      (older (F.rules (root q)) (IntegralCriticalFlatHeightBits.creatingIndex F q h)).length :=
    HL.trans (IntegralCriticalFlatHeightBits.creating_older_length F q h).symm
  exact (family_stateAt_congr _ (F.length_le (root q)) (F.scalar_bound (root q)) _ _ hm _ _ HE).trans
    (IntegralCriticalScriptQueryBits.birthFamily_stateAt _ _ _ _)

end LeanCanny.Algebra.IntegralCriticalTotalHeightBits
