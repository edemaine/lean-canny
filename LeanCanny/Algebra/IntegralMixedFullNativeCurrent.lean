/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullNative
public import LeanCanny.Algebra.IntegralMixedFullLimitCoordinate
/-! # All recursive arithmetic callbacks close against one current native model -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullNativeBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

abbrev Matches (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (answer : List Bool → List Bool) : Prop :=
  ∀ q, IntegralMixedVirtualCaps.valid P q → answer q = (machine P a D h).model q

theorem raw_matches (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (answer : List Bool → List Bool) (hm : Matches P a D h answer) :
    IntegralMixedRawDispatcherBits.Matches P a (family P D) (input P a D h) h.kind h.arithmetic.core.scalar.full.degree (IntegralMixedFullHistoryFamilyBits.routing P D) (IntegralMixedFullHistoryFamilyBits.routingAccess P D h.arithmetic.core.scalar.full) answer := by
  intro q hv hr
  exact (hm q hv).trans (model_raw P a D h q hr)

theorem determinant_matches (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (answer : List Bool → List Bool) (hm : Matches P a D h answer) :
    IntegralMixedFullDeterminantBits.Matches P a D h.arithmetic.core answer := by
  intro q hv hr
  exact (hm q hv).trans (model_determinant P a D h q hr)

theorem arithmetic_matches (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (answer : List Bool → List Bool) (hm : Matches P a D h answer) :
    IntegralMixedArithmeticEntriesBits.Matches P a D h.arithmetic answer := by
  intro q hv hr
  have H3 : IntegralMixedRoutineTaskBits.routine P q ≠ 3 := by rcases hr with hr | hr | hr | hr | hr <;> omega
  have H4 : IntegralMixedRoutineTaskBits.routine P q ≠ 4 := by rcases hr with hr | hr | hr | hr | hr <;> omega
  exact (hm q hv).trans (model_arithmetic P a D h q H3 H4)

theorem critical_matches (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (answer : List Bool → List Bool) (hm : Matches P a D h answer) :
    IntegralMixedVirtualContextComponentBits.Matches P (family P D) answer :=
  IntegralMixedFullEntryBits.virtual_matches P a D h.arithmetic.core answer
    (IntegralMixedNormalizedCoreBits.core_matches P a D h.arithmetic answer
      (IntegralMixedArithmeticEntriesBits.core_matches P a D h.arithmetic answer (arithmetic_matches P a D h answer hm)))

theorem producer_matches (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (answer : List Bool → List Bool) (hm : Matches P a D h answer) :
    IntegralMixedProducerActualBits.Matches P D answer :=
  IntegralMixedFullCoreBits.producer_matches P a D h.arithmetic.core answer
    (IntegralMixedNormalizedCoreBits.core_matches P a D h.arithmetic answer
      (IntegralMixedArithmeticEntriesBits.core_matches P a D h.arithmetic answer (arithmetic_matches P a D h answer hm)))

theorem gram_matches (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (answer : List Bool → List Bool) (hm : Matches P a D h answer) : IntegralMixedGramScopedBits.Matches P (family P D) answer :=
  IntegralMixedGramScopedBits.matches_of_current P a (family P D) (input P a D h) answer
    (IntegralMixedFullDeterminantBits.gram_matches P a D h.arithmetic.core answer (determinant_matches P a D h answer hm))

theorem psc_matches (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (answer : List Bool → List Bool) (hm : Matches P a D h answer) : IntegralMixedPscContextUpperModel.Matches P (family P D) answer :=
  IntegralMixedPscContextBranchBits.matches_of_current P a (family P D) (input P a D h) answer
    (IntegralMixedFullDeterminantBits.psc_matches P a D h.arithmetic.core answer (determinant_matches P a D h answer hm))

theorem correct (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P) (h : Controls P D)
    (x : (q : List Bool) → ZMod (modulus P q)) (hm : Matches P a D h (fun q => residueBits (x q))) :
    Correct (machine P a D h) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  apply choose_correct
  · apply withGuard_correct
    · exact IntegralMixedRawDispatcherBits.correct P a (family P D) (input P a D h) h.kind h.arithmetic.core.scalar.full.degree (IntegralMixedFullHistoryFamilyBits.routing P D) (IntegralMixedFullHistoryFamilyBits.routingAccess P D h.arithmetic.core.scalar.full)
        (IntegralMixedFullHistoryFamilyBits.geometry P D) x (raw_matches P a D h _ hm)
        (critical_matches P a D h _ hm)
        (IntegralMixedFullLimitCoordinate.bank_replies P D _ (producer_matches P a D h _ hm)) (gram_matches P a D h _ hm) (psc_matches P a D h _ hm)
    · intro q _
      exact IntegralMixedRawDispatcherBits.selected P a (family P D) (input P a D h) h.kind h.arithmetic.core.scalar.full.degree (IntegralMixedFullHistoryFamilyBits.routing P D) (IntegralMixedFullHistoryFamilyBits.routingAccess P D h.arithmetic.core.scalar.full) q
  · apply choose_correct
    · apply withGuard_correct
      · exact IntegralMixedFullDeterminantBits.correct P a D h.arithmetic.core x
          (IntegralMixedArithmeticEntriesBits.entry_matches P a D h.arithmetic _ (arithmetic_matches P a D h _ hm))
          (determinant_matches P a D h _ hm)
      · intro q _
        exact IntegralMixedFullDeterminantBits.selected P a D h.arithmetic.core q
    · exact IntegralMixedArithmeticEntriesBits.correct P a D h.arithmetic x (arithmetic_matches P a D h _ hm)
        (IntegralMixedRawDispatcherBits.raw_matches P a (family P D) (input P a D h) h.kind h.arithmetic.core.scalar.full.degree (IntegralMixedFullHistoryFamilyBits.routing P D) (IntegralMixedFullHistoryFamilyBits.routingAccess P D h.arithmetic.core.scalar.full) _
          (raw_matches P a D h _ hm))

end LeanCanny.Algebra.IntegralMixedFullNativeBits
