/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedBankProducerReplies
/-! # Every full producer dispatcher reply has one canonical residue -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedProducerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open scoped Classical

attribute [local irreducible] integerMachine physicalMachine cutMachine

theorem canonical (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
    (h : Controls P D H) (q : List Bool) : ∃ z : ZMod (modulus P q), residueBits z = (machine P a D H h).model q := by
  change ∃ z : ZMod (modulus P q), residueBits z =
    if decide (InContext P 0 0 q) then (integerMachine P a D H h).model q else
      if decide (InContext P 1 1 q) then (physicalMachine P a D H h).model q else
        if decide (InContext P 2 4 q) then (cutMachine P a D H h).model q else []
  split_ifs
  · unfold integerMachine
    exact IntegralMixedIntegerFamilyBits.canonical P a (virtualFamily P D H) (virtualInput P a D H h) (IntegralMixedFramedIntegerBits.polynomial P D) h.integer q
  · unfold physicalMachine
    exact IntegralMixedPhysicalCompanionDispatcherBits.canonical P a _ (physicalInput P a D H h) q
  · unfold cutMachine
    exact IntegralMixedNormalizedCompanionDispatcherBits.canonical P a _
      (virtualInput P a D H h) (degreeInput P a D H h) q
  · exact ⟨0, (ArithmeticBits.zero_residueBits _).symm⟩

end LeanCanny.Algebra.IntegralMixedFramedProducerBits
