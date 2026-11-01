/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalContextProducts
public import LeanCanny.Algebra.IntegralMixedPhysicalContextReplyMatching
/-! # Finite physical low-stage replies from one current component match -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalContextStageReplyBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedPhysicalCriticalBits IntegralMixedPhysicalQueryBits IntegralMixedPhysicalNativeLowerBits
set_option backward.isDefEq.respectTransparency false
noncomputable def component (P : Parameters) (F : Family) : Phase → List Bool → List Bool
  | .originalCoefficient => original P F
  | .derivativeCoefficient => IntegralMixedPhysicalCoefficientBits.derivative P F
  | .clearedHeight => IntegralMixedPhysicalNativeLowerBits.height P F
  | .monomialFactor => IntegralMixedPhysicalFactorBits.monomial P F
  | .factorPower => IntegralMixedPhysicalFactorBits.power P F
  | .productEntry => IntegralMixedPhysicalLayeredBits.productEntry P F
  | .productPower => IntegralMixedPhysicalGridBits.product P F
  | .originalGridTerm => IntegralMixedPhysicalGridBits.term P F
  | .clearedGridSum => IntegralMixedPhysicalSpatialBits.cleared P F
  | _ => fun _ => []
theorem component_canonical (P : Parameters) (F : Family) (p : Phase) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = component P F p q := by
  cases p
  case originalCoefficient => exact IntegralMixedPhysicalCanonicalBits.original_canonical P F q
  case derivativeCoefficient => exact IntegralMixedPhysicalCanonicalBits.derivative_canonical P F q
  case clearedHeight => exact IntegralMixedPhysicalCanonicalBits.height_canonical P F q
  case monomialFactor => exact IntegralMixedPhysicalNativeLowerBits.monomial_canonical P F q
  case factorPower => exact IntegralMixedPhysicalCanonicalBits.power_canonical P F q
  case productEntry => exact IntegralMixedPhysicalCanonicalBits.productEntry_canonical P F q
  case productPower => exact IntegralMixedPhysicalCanonicalBits.product_canonical P F q
  case originalGridTerm => exact IntegralMixedPhysicalCanonicalBits.term_canonical P F q
  case clearedGridSum => exact IntegralMixedPhysicalCanonicalBits.cleared_canonical P F q
  all_goals exact ⟨0, (ArithmeticBits.zero_residueBits _).symm⟩

abbrev Matches (P : Parameters) (F : Family) (reply : List Bool → List Bool) : Prop :=
  ∀ p q, p.code ≤ 8 → IntegralMixedPhysicalContextBits.selected P p q = true → reply q = component P F p q

theorem matrix (P : Parameters) (F : Family) (reply : List Bool → List Bool) (hm : Matches P F reply)
    (p : Phase) (hp : p.code ≤ 8) (z : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P (pairFst z)) (hr : IntegralMixedRoutineTaskBits.routine P (pairFst z) = 1)
    (hx : get P .slot15 (pairFst z) = 1) :
    reply (IntegralCriticalFlatMatrixQuery.writer P p z) = component P F p (IntegralCriticalFlatMatrixQuery.writer P p z) :=
  hm p _ hp (IntegralMixedPhysicalContextReplyBits.matrix_selected P p z hv hr hx)

theorem grid_selected (P : Parameters) (p : Phase) (z : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P (pairFst z)) (hr : IntegralMixedRoutineTaskBits.routine P (pairFst z) = 1)
    (hx : get P .slot15 (pairFst z) = 1) : IntegralMixedPhysicalContextBits.selected P p (IntegralCriticalFlatGridBits.writer P p z) = true := by
  apply IntegralMixedPhysicalContextReplyBits.current_selected P p _ _
    (IntegralCriticalFlatGridBits.writer_root P p z) (IntegralCriticalFlatGridBits.writer_birth P p z) _
    (IntegralCriticalFlatGridBits.writer_other P p z .slot15 (by decide)) hv hr hx
    (IntegralCriticalFlatGridBits.writer_phase P p z)
  unfold IntegralMixedRoutineTaskBits.routine
  rw [IntegralCriticalFlatGridBits.writer_other P p z .slot14 (by decide)]

theorem factor_replies (P : Parameters) (F : Family) (reply : List Bool → List Bool) (hm : Matches P F reply)
    (q : List Bool) (hq : IntegralMixedPhysicalContextBits.selected P .factorPower q = true) : FactorRepliesAt P F reply q := by
  have HX := (IntegralMixedPhysicalContextBits.selected_iff P .factorPower q).mp hq
  have HQ := (selectedValid_iff P .factorPower q).mp HX.1
  intro r t
  apply matrix P F reply hm .monomialFactor (by decide)
  · simpa only [pairFst_pair] using HQ.1
  · simpa only [pairFst_pair] using HQ.2.1
  · simpa only [pairFst_pair] using HX.2

theorem product_replies (P : Parameters) (F : Family) (reply : List Bool → List Bool) (hm : Matches P F reply)
    (q : List Bool) (hq : IntegralMixedPhysicalContextBits.selected P .productPower q = true) : ProductRepliesAt P F reply q := by
  have HX := (IntegralMixedPhysicalContextBits.selected_iff P .productPower q).mp hq
  have HQ := (selectedValid_iff P .productPower q).mp HX.1
  intro r t
  apply matrix P F reply hm .productEntry (by decide)
  · simpa only [pairFst_pair] using HQ.1
  · simpa only [pairFst_pair] using HQ.2.1
  · simpa only [pairFst_pair] using HX.2

theorem entry_replies (P : Parameters) (F : Family) (reply : List Bool → List Bool) (hm : Matches P F reply)
    (q : List Bool) (hq : IntegralMixedPhysicalContextBits.selected P .productEntry q = true) : ProductEntryRepliesAt P F reply q := by
  have HX := (IntegralMixedPhysicalContextBits.selected_iff P .productEntry q).mp hq
  have HQ := (selectedValid_iff P .productEntry q).mp HX.1
  intro _
  let z := MatrixProductBits.factorQuery (productEntryFamily P F) (productEntryInput P F q)
  have HO : pairFst z = q := by
    simp only [z, MatrixProductBits.factorQuery, productEntryInput, IntegralCriticalFlatGenericProductEntryBits.input, pairFst_pair]
  change reply (IntegralCriticalFlatFactorQuery.writer P .factorPower z) =
    IntegralMixedPhysicalFactorBits.power P F (IntegralCriticalFlatFactorQuery.writer P .factorPower z)
  apply hm .factorPower _ (by decide)
  apply IntegralMixedPhysicalContextReplyBits.factor_selected
  · rw [HO]; exact HQ.1
  · rw [HO]; exact HQ.2.1
  · rw [HO]; exact HX.2

theorem term_replies (P : Parameters) (F : Family) (reply : List Bool → List Bool) (hm : Matches P F reply)
    (q : List Bool) (hq : IntegralMixedPhysicalContextBits.selected P .originalGridTerm q = true) : GridTermRepliesAt P F reply q := by
  have HX := (IntegralMixedPhysicalContextBits.selected_iff P .originalGridTerm q).mp hq
  have HQ := (selectedValid_iff P .originalGridTerm q).mp HX.1
  intro _
  change reply (IntegralCriticalFlatGridBits.writer P .productPower (gridTermInput P q)) =
    IntegralMixedPhysicalGridBits.product P F (IntegralCriticalFlatGridBits.writer P .productPower (gridTermInput P q))
  apply hm .productPower _ (by decide)
  apply grid_selected
  · rw [IntegralCriticalFlatGridBits.termInput_parent]; exact HQ.1
  · rw [IntegralCriticalFlatGridBits.termInput_parent]; exact HQ.2.1
  · rw [IntegralCriticalFlatGridBits.termInput_parent]; exact HX.2

theorem grid_replies (P : Parameters) (F : Family) (reply : List Bool → List Bool) (hm : Matches P F reply)
    (q : List Bool) (hq : IntegralMixedPhysicalContextBits.selected P .clearedGridSum q = true) : GridRepliesAt P F reply q := by
  have HX := (IntegralMixedPhysicalContextBits.selected_iff P .clearedGridSum q).mp hq
  have HQ := (selectedValid_iff P .clearedGridSum q).mp HX.1
  intro k _
  apply hm .originalGridTerm _ (by decide)
  apply grid_selected
  · simpa only [pairFst_pair] using HQ.1
  · simpa only [pairFst_pair] using HQ.2.1
  · simpa only [pairFst_pair] using HX.2

theorem factor_correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (g : IntegralMixedPhysicalCaps.RootGeometry P F) (reply : List Bool → List Bool) (hm : Matches P F reply) :
    NativeControllerBranch.Correct (IntegralMixedPhysicalContextBits.factorMachine P a F h) reply (IntegralMixedRoutineTaskBits.Frame P) :=
  IntegralMixedPhysicalContextBits.factor_correct P a F h g reply (factor_replies P F reply hm)

theorem entry_correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (g : IntegralMixedPhysicalCaps.RootGeometry P F) (reply : List Bool → List Bool) (hm : Matches P F reply) :
    NativeControllerBranch.Correct (IntegralMixedPhysicalContextBits.productEntryMachine P a F h) reply (IntegralMixedRoutineTaskBits.Frame P) :=
  IntegralMixedPhysicalContextBits.productEntry_correct P a F h g reply (entry_replies P F reply hm)

theorem product_correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (g : IntegralMixedPhysicalCaps.RootGeometry P F) (reply : List Bool → List Bool) (hm : Matches P F reply) :
    NativeControllerBranch.Correct (IntegralMixedPhysicalContextBits.productMachine P a F h) reply (IntegralMixedRoutineTaskBits.Frame P) :=
  IntegralMixedPhysicalContextBits.product_correct P a F h g reply (product_replies P F reply hm)

theorem term_correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (reply : List Bool → List Bool) (hm : Matches P F reply) :
    NativeControllerBranch.Correct (IntegralMixedPhysicalContextBits.gridTermMachine P a F h) reply (IntegralMixedRoutineTaskBits.Frame P) :=
  IntegralMixedPhysicalContextBits.gridTerm_correct P a F h reply (term_replies P F reply hm)

theorem grid_correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (g : IntegralMixedPhysicalCaps.RootGeometry P F) (reply : List Bool → List Bool) (hm : Matches P F reply) :
    NativeControllerBranch.Correct (IntegralMixedPhysicalContextBits.gridMachine P a F h) reply (IntegralMixedRoutineTaskBits.Frame P) :=
  IntegralMixedPhysicalContextBits.grid_correct P a F h g reply (grid_replies P F reply hm)

theorem leaves (P : Parameters) (F : Family) (reply : List Bool → List Bool) (hm : Matches P F reply) :
    IntegralMixedPhysicalContextReplyBits.Matches P F reply where
  original q hq := hm .originalCoefficient q (by decide) hq
  derivative q hq := hm .derivativeCoefficient q (by decide) hq
  height q hq := hm .clearedHeight q (by decide) hq

theorem derivative_correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (g : IntegralMixedPhysicalCaps.RootGeometry P F) (reply : List Bool → List Bool) (hm : Matches P F reply) :
    NativeControllerBranch.Correct (IntegralMixedPhysicalContextBits.derivativeMachine P a F h) reply (IntegralMixedRoutineTaskBits.Frame P) :=
  IntegralMixedPhysicalContextReplyBits.derivative_correct_of_matches P a F h g reply (leaves P F reply hm)

theorem monomial_correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (g : IntegralMixedPhysicalCaps.RootGeometry P F) (reply : List Bool → List Bool) (hm : Matches P F reply)
    (hc : IntegralMixedPhysicalContextReplyBits.Callbacks P F reply) :
    NativeControllerBranch.Correct (IntegralMixedPhysicalContextBits.monomialMachine P a F h) reply (IntegralMixedRoutineTaskBits.Frame P) :=
  IntegralMixedPhysicalContextReplyBits.monomial_correct_of_matches P a F h g reply (leaves P F reply hm) hc
end LeanCanny.Algebra.IntegralMixedPhysicalContextStageReplyBits
