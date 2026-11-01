/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalProducerLeading
public import LeanCanny.Algebra.IntegralMixedFullPhysicalDenominator
/-! # Physical producer leading values are literal creating-command scalars -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalProducerLeadingBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedPhysicalCriticalBits IntegralMixedPhysicalUpperBits IntegralMixedHistory
set_option backward.isDefEq.respectTransparency false

theorem integer_actual (P : Parameters) (F : Family) (q : List Bool) :
    IntegralClearedCriticalLeadingBits.integer (critical P F) q =
      criticalLeading (F.state (IntegralMixedPhysicalTaskBits.saved P q))
        (F.birth_bound (IntegralMixedPhysicalTaskBits.saved P q)) (F.rule (IntegralMixedPhysicalTaskBits.saved P q)) := rfl

theorem value_actual (P : Parameters) (F : Family) (q : List Bool) :
    value P F q = residueBits (criticalLeading (F.state (IntegralMixedPhysicalTaskBits.saved P q))
      (F.birth_bound (IntegralMixedPhysicalTaskBits.saved P q)) (F.rule (IntegralMixedPhysicalTaskBits.saved P q)) : ZMod (modulus P q)) :=
  congrArg (fun z : ℤ => residueBits (z : ZMod (modulus P q))) (integer_actual P F q)

end LeanCanny.Algebra.IntegralMixedPhysicalProducerLeadingBits
namespace LeanCanny.Algebra.IntegralMixedFullPhysicalBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedHistory IntegralMixedFullHistoryScript
set_option backward.isDefEq.respectTransparency false

theorem producer_leading_critical (P : Parameters) (D : Data P) (q : List Bool)
    (r : CriticalRule (P.ambient (pairFst (IntegralMixedPhysicalTaskBits.saved P q))))
    (hc : creating P D (IntegralMixedPhysicalTaskBits.saved P q) = some (.critical r)) :
    IntegralMixedPhysicalProducerLeadingBits.value P (family P D) q = residueBits
      (IntegralMixedFullHistoryScript.leading ((family P D).state (IntegralMixedPhysicalTaskBits.saved P q))
        ((family P D).birth_bound (IntegralMixedPhysicalTaskBits.saved P q)) (.critical r) : ZMod (modulus P q)) := by
  rw [IntegralMixedPhysicalProducerLeadingBits.value_actual]
  change residueBits (criticalLeading ((family P D).state (IntegralMixedPhysicalTaskBits.saved P q))
    ((family P D).birth_bound (IntegralMixedPhysicalTaskBits.saved P q))
    (rule P D (IntegralMixedPhysicalTaskBits.saved P q)) : ZMod (modulus P q)) = _
  rw [rule_critical P D _ r hc]
  rfl

end LeanCanny.Algebra.IntegralMixedFullPhysicalBits
