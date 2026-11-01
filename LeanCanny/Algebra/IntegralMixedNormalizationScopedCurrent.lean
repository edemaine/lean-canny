/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationScoped
/-! # Current replies of the context-restricted normalization machine -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationScopedBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedCutSource IntegralMixedNormalizationTopBits
set_option backward.isDefEq.respectTransparency false

abbrev CurrentMatches (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (hd : BinaryFn F.degree) (height : List Bool → ℕ) (hb : BinaryFn height) (answer : List Bool → List Bool) : Prop :=
  ∀ q, InScope P q → answer q = (machine P a F h hd height hb).model q

theorem matches_of_current (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (hd : BinaryFn F.degree) (height : List Bool → ℕ) (hb : BinaryFn height) (answer : List Bool → List Bool)
    (hm : CurrentMatches P a F h hd height hb answer) : Matches P a F h hd height hb answer := by
  intro q hv hr hx
  have HQ : InScope P q := ⟨hv, hr, hx⟩
  exact (hm q HQ).trans (model_inside P a F h hd height hb q HQ)

theorem correct_of_current (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (hd : BinaryFn F.degree) (g : IntegralMixedVirtualCaps.RootGeometry P F) (height : List Bool → ℕ) (hb : BinaryFn height)
    (hh : ∀ q, IntegralMixedVirtualCaps.valid P q → ∀ i j,
      (top F (IntegralMixedVirtualTaskBits.saved P q) i j).natAbs ≤ 2 ^ height (RankedHistoryTask.root q))
    (hc : ∀ r, 2 * characteristicBudget P height r + 4 ≤ P.modulusBound r)
    (x : (q : List Bool) → ZMod (modulus P q))
    (hn : CurrentMatches P a F h hd height hb (fun q => residueBits (x q))) (hr : RawMatches P F (fun q => residueBits (x q))) :
    Correct (machine P a F h hd height hb) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) :=
  correct P a F h hd g height hb hh hc x (matches_of_current P a F h hd height hb _ hn) hr

theorem machine_selected (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (hd : BinaryFn F.degree) (height : List Bool → ℕ) (hb : BinaryFn height) (q : List Bool) :
    (machine P a F h hd height hb).selected q = true := by
  change (_ || true) = true
  exact Bool.or_true _

theorem model_physical_context (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (hd : BinaryFn F.degree) (height : List Bool → ℕ) (hb : BinaryFn height) (q : List Bool) (hx : get P .slot15 q = 1) :
    (machine P a F h hd height hb).model q = [] :=
  model_outside P a F h hd height hb q (fun HQ => by have := HQ.2.2.1; omega)

theorem model_phase14 (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (hd : BinaryFn F.degree) (height : List Bool → ℕ) (hb : BinaryFn height) (q : List Bool)
    (hq : InScope P q) (hp : isPhase .eulerSum q) : (machine P a F h hd height hb).model q = normalizedValue P F q :=
  (model_inside P a F h hd height hb q hq).trans
    (IntegralMixedNormalizationDispatcherBits.model_phase14 P a F h hd height hb q hq.1 hq.2.1 hp)
end LeanCanny.Algebra.IntegralMixedNormalizationScopedBits
