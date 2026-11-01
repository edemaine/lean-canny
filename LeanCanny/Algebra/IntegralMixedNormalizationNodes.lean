/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationCanonical
public import LeanCanny.Computation.NativePhaseDispatch
/-! # Distinct phase nodes expose the actual normalization output branch -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationDispatcherBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedNormalizationTopBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

def node (M : Machine) (p : Phase) (hs : ∀ q, M.selected q = true → isPhase p q) : PhaseNode phase where
  machine := M
  code := p.code
  selected_phase := hs

noncomputable def nodes (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (hd : BinaryFn F.degree)
    (height : List Bool → ℕ) (hb : BinaryFn height) : List (PhaseNode phase) := [
  node (stage0 P a F hd) .originalCoefficient (fun q hs => ((selected_iff P .originalCoefficient q).mp hs).2.2),
  node (stage1 P a F h) .derivativeCoefficient (fun q hs => ((selected_iff P .derivativeCoefficient q).mp hs).2.2),
  node (stage2 P a F) .clearedHeight (fun q hs => ((selected_iff P .clearedHeight q).mp hs).2.2),
  node (stage3 P a F h) .monomialFactor (fun q hs => ((selected_iff P .monomialFactor q).mp hs).2.2),
  node (stage4 P a F h) .factorPower (fun q hs => ((selected_iff P .factorPower q).mp hs).2.2),
  node (stage5 P a F h) .productEntry (fun q hs => ((selected5_iff P F q).mp hs).1.2.2),
  node (stage6 P a F h) .productPower (fun q hs => ((selected_iff P .productPower q).mp hs).2.2),
  node (stage7 P a F height hb) .originalGridTerm (fun q hs => ((selected7_iff P q).mp hs).2.2.1),
  node (stage8 P a F h) .clearedGridSum (fun q hs => ((selected8_iff P F q).mp hs).2.2.1),
  node (stage9 P a F h) .frozenPowerTerm (fun q hs => ((selected9_iff P F q).mp hs).1.2.2),
  node (stage10 P a F h) .frozenPowerSum (fun q hs => ((selected10_iff P F q).mp hs).1.2.2),
  node (stage11 P a F h) .frozenConstant (fun q hs => ((selected_iff P .frozenConstant q).mp hs).2.2),
  node (stage12 P a F h) .frozenLower (fun q hs => ((selected12_iff P F q).mp hs).1.2.2),
  node (stage13 P a F h) .coordinateGradientProduct (fun q hs => ((selected13_iff P F q).mp hs).1.2.2)]

theorem nodes_codes (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (hd : BinaryFn F.degree)
    (height : List Bool → ℕ) (hb : BinaryFn height) :
    (nodes P a F h hd height hb).map PhaseNode.code = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] := rfl

theorem nodes_distinct (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (hd : BinaryFn F.degree)
    (height : List Bool → ℕ) (hb : BinaryFn height) :
    ((nodes P a F h hd height hb).map PhaseNode.code).Nodup := by
  rw [nodes_codes]
  decide

theorem machine_eq_dispatch (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (hd : BinaryFn F.degree)
    (height : List Bool → ℕ) (hb : BinaryFn height) :
    machine P a F h hd height hb = phaseDispatch (nodes P a F h hd height hb) (stage14 P a F h hd) := rfl

theorem model_selected_node (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (hd : BinaryFn F.degree)
    (height : List Bool → ℕ) (hb : BinaryFn height) (q : List Bool) (b : PhaseNode phase)
    (hm : b ∈ nodes P a F h hd height hb) (hs : b.machine.selected q = true) :
    (machine P a F h hd height hb).model q = b.machine.model q := by
  rw [machine_eq_dispatch]
  exact phaseDispatch_model_selected _ _ q b (nodes_distinct P a F h hd height hb) hm hs

theorem model_phase14 (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (hd : BinaryFn F.degree)
    (height : List Bool → ℕ) (hb : BinaryFn height) (q : List Bool)
    (hv : IntegralMixedVirtualCaps.valid P q) (hr : IntegralMixedRoutineTaskBits.routine P q = 5) (hp : isPhase .eulerSum q) :
    (machine P a F h hd height hb).model q = normalizedValue P F q := by
  have HN : phase q ∉ (nodes P a F h hd height hb).map PhaseNode.code := by
    rw [nodes_codes]
    change phase q = 14 at hp
    rw [hp]
    decide
  rw [machine_eq_dispatch, phaseDispatch_model_off _ _ q HN]
  exact stage14_model_valid P a F h hd q hv hr hp

end LeanCanny.Algebra.IntegralMixedNormalizationDispatcherBits
