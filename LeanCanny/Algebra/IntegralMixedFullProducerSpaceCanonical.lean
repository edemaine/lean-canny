/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullProducerSpaceValues
/-! # Every full producer dispatcher reply has one canonical residue -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullProducerSpaceBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open scoped Classical

attribute [local irreducible] integerMachine physicalMachine cutMachine

theorem canonical (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : Controls P D) (q : List Bool) : ∃ z : ZMod (modulus P q), residueBits z = (machine P a D h).model q := by
  change ∃ z : ZMod (modulus P q), residueBits z =
    if decide (InContext P 0 0 q) then (integerMachine P a D h).model q else
      if decide (InContext P 1 1 q) then (physicalMachine P a D h).model q else
        if decide (InContext P 2 4 q) then (cutMachine P a D h).model q else []
  split_ifs
  · unfold integerMachine
    exact IntegralMixedIntegerProducerSpaceDispatcherBits.canonical P a D h.integer q
  · unfold physicalMachine
    exact IntegralMixedPhysicalCompanionDispatcherBits.canonical P a _ h.physical q
  · unfold cutMachine
    exact IntegralMixedNormalizedCompanionDispatcherBits.canonical P a _
      (IntegralMixedFullHistoryFamilyBits.inputMetadata P a D h.full) h.full.degree q
  · exact ⟨0, (ArithmeticBits.zero_residueBits _).symm⟩

end LeanCanny.Algebra.IntegralMixedFullProducerSpaceBits
