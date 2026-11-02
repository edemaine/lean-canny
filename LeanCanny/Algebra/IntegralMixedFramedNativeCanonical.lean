/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedNativeDispatcher
/-! # Canonical residues for the complete framed native controller -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedNativeBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedFramedHistoryFamilyBits (Plan)
set_option backward.isDefEq.respectTransparency false

theorem component_canonical (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (r : Fin 7) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = (component P a D H h r).model q := by
  fin_cases r
  · exact IntegralMixedFramedFullScalarBits.canonical P a D H h.scalar q
  · exact IntegralMixedFramedCriticalBits.canonical P a D H h.critical q
  · exact IntegralMixedFramedEntryBits.canonical P a D H h.critical q
  · exact IntegralMixedFramedDeterminantBits.canonical P a D H h.critical q
  · exact IntegralMixedFramedNormalizationBits.raw_canonical P a D H h.normalization q
  · exact IntegralMixedFramedNormalizationBits.canonical P a D H h.normalization q
  · exact IntegralMixedFramedProducerBits.canonical P a D H h.producer q

attribute [local irreducible] component

private theorem dispatch_canonical {code : List Bool → ℕ} (ns : List (PhaseNode code))
    (fallback : Machine) (m : ℕ) (q : List Bool)
    (hf : ∃ z : ZMod m, residueBits z = fallback.model q)
    (hn : ∀ n ∈ ns, ∃ z : ZMod m, residueBits z = n.machine.model q) :
    ∃ z : ZMod m, residueBits z = (phaseDispatch ns fallback).model q := by
  induction ns with
  | nil => exact hf
  | cons n ns ih =>
    change ∃ z : ZMod m, residueBits z = if n.machine.selected q then n.machine.model q else (phaseDispatch ns fallback).model q
    split_ifs
    · exact hn n List.mem_cons_self
    · exact ih (fun n hn' => hn n (List.mem_cons_of_mem _ hn'))

theorem canonical (P : Parameters) (a : Access P) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (h : Controls P D H) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = (machine P a D H h).model q := by
  apply dispatch_canonical _ _ _ q ⟨0, (ArithmeticBits.zero_residueBits _).symm⟩
  intro n hn
  simp only [nodes, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals exact component_canonical P a D H h _ q

end LeanCanny.Algebra.IntegralMixedFramedNativeBits
