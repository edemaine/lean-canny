/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalScriptDenominatorFP

/-! # Selected numerator and cleared-height source identities

The state-at-prefix source and the creating source keep the same actual
algebra. Primitive selector metadata therefore selects exactly the same
numerator as well as the same integer scale. Their common-denominator
clearing is the actual original critical source's height.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalScriptDenominatorFP
open LeanCanny.Encoding LeanCanny.Computation MatrixPower FixedWidthPolynomial
open IntegralCriticalScript
set_option backward.isDefEq.respectTransparency false

variable (F : IntegralCriticalScriptGeneratorBits.Queries)

theorem selected_numerator_eq (c : List Bool) (i : Fin (F.ambient c + 1)) :
    (IntegralCriticalScriptHeightBits.state (queries F) c).bank.selectedNumerator
      (IntegralCriticalScriptHeightBits.select (queries F) c i.val) = ((atSource F c).data []).heights i := by
  change (stateAt (F.rules c) (F.length_le c) (F.scalar_bound c) (older (F.rules c) (F.selected c)).length).bank.selectedNumerator
    (IntegralCriticalScriptHeightBits.select (queries F) c i.val) =
    (stateAt (F.rules c) (F.length_le c) (F.scalar_bound c) (older (F.rules c) (F.selected c)).length).bank.selectedNumerator
      ((chosen (F.rules c) (F.selected c)).select (past (F.rules c) (older (F.rules c) (F.selected c)).length).length i)
  let pick (z : ℕ) : Option (Fin (past (F.rules c) (older (F.rules c) (F.selected c)).length).length) :=
    if hz : z < (past (F.rules c) (older (F.rules c) (F.selected c)).length).length then some ⟨z, hz⟩ else none
  exact congrArg (fun z => (stateAt (F.rules c) (F.length_le c) (F.scalar_bound c)
    (older (F.rules c) (F.selected c)).length).bank.selectedNumerator (pick z)) (selector_eq F c i)

theorem cleared_height_eq (c : List Bool) (i : ℕ) :
    CoordinateFrozenCriticalElimination.numerators
      (fun j : Fin (F.ambient c + 1) => IntegralCriticalScriptHeightBits.scales (queries F) c j.val)
      (fun j => (IntegralCriticalScriptHeightBits.state (queries F) c).bank.selectedNumerator
        (IntegralCriticalScriptHeightBits.select (queries F) c j.val)) i =
      (IntegralHistoryCriticalBits.original (atSource F c)).height [] i := by
  have HS : (fun j : Fin (F.ambient c + 1) => IntegralCriticalScriptHeightBits.scales (queries F) c j.val) =
      ((atSource F c).data []).scales := funext (scale_eq F c)
  have HN : (fun j : Fin (F.ambient c + 1) => (IntegralCriticalScriptHeightBits.state (queries F) c).bank.selectedNumerator
      (IntegralCriticalScriptHeightBits.select (queries F) c j.val)) = ((atSource F c).data []).heights :=
    funext (selected_numerator_eq F c)
  rw [HS, HN]
  rfl

end LeanCanny.Algebra.IntegralCriticalScriptDenominatorFP
