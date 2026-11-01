/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationContextPatch
public import LeanCanny.Algebra.IntegralMixedRoutineContextGuard
/-! # Native normalization restricted to virtual creating contexts -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationScopedBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedCutSource IntegralMixedNormalizationTopBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] IntegralMixedNormalizationDispatcherBits.machine

abbrev InScope (P : Parameters) := IntegralMixedRoutineContextGuard.Selected P 5 2 4
noncomputable def branch (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (hd : BinaryFn F.degree) (height : List Bool → ℕ) (hb : BinaryFn height) : Machine :=
  IntegralMixedRoutineContextGuard.machine P a 5 2 4 (IntegralMixedNormalizationDispatcherBits.machine P a F h hd height hb)
noncomputable def machine (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (hd : BinaryFn F.degree) (height : List Bool → ℕ) (hb : BinaryFn height) : Machine :=
  (branch P a F h hd height hb).choose zero

theorem branch_correct (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (hd : BinaryFn F.degree) (g : IntegralMixedVirtualCaps.RootGeometry P F) (height : List Bool → ℕ) (hb : BinaryFn height)
    (hh : ∀ q, IntegralMixedVirtualCaps.valid P q → ∀ i j,
      (top F (IntegralMixedVirtualTaskBits.saved P q) i j).natAbs ≤ 2 ^ height (RankedHistoryTask.root q))
    (hc : ∀ r, 2 * characteristicBudget P height r + 4 ≤ P.modulusBound r)
    (x : (q : List Bool) → ZMod (modulus P q))
    (hn : Matches P a F h hd height hb (fun q => residueBits (x q))) (hr : RawMatches P F (fun q => residueBits (x q))) :
    Correct (branch P a F h hd height hb) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  let y := patch P a F h hd height hb x
  have HN := patch_normalization P a F h hd height hb x hn
  have HR := patch_raw P a F h hd height hb x hr
  have HY := IntegralMixedNormalizationDispatcherBits.correct_of_matches P a F h hd height hb g hh hc y HN HR
  apply withGuard_oracle_correct _ _ _ (fun q => residueBits (y q)) (fun q => residueBits (x q)) _ HY
  · intro q _
    exact IntegralMixedNormalizationDispatcherBits.machine_selected P a F h hd height hb q
  · intro q hq budget c hreq
    have HQ : InScope P q := of_decide_eq_true hq
    have HE := IntegralMixedNormalizationContextBits.requests_context P a F h hd g height hb
      (fun q => residueBits (y q)) HN q (IntegralMixedNormalizationDispatcherBits.machine_selected P a F h hd height hb q) budget c hreq
    have HX : IntegralMixedVirtualContextBits.context P c := by
      unfold IntegralMixedVirtualContextBits.context
      rw [show get P .slot15 c = get P .slot15 q from HE]
      exact HQ.2.2
    exact congrArg residueBits (patch_good P a F h hd height hb x c HX)

theorem correct (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (hd : BinaryFn F.degree) (g : IntegralMixedVirtualCaps.RootGeometry P F) (height : List Bool → ℕ) (hb : BinaryFn height)
    (hh : ∀ q, IntegralMixedVirtualCaps.valid P q → ∀ i j,
      (top F (IntegralMixedVirtualTaskBits.saved P q) i j).natAbs ≤ 2 ^ height (RankedHistoryTask.root q))
    (hc : ∀ r, 2 * characteristicBudget P height r + 4 ≤ P.modulusBound r)
    (x : (q : List Bool) → ZMod (modulus P q))
    (hn : Matches P a F h hd height hb (fun q => residueBits (x q))) (hr : RawMatches P F (fun q => residueBits (x q))) :
    Correct (machine P a F h hd height hb) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) :=
  choose_correct _ _ _ _ (branch_correct P a F h hd g height hb hh hc x hn hr) (zero_correct _ _)

theorem model_inside (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (hd : BinaryFn F.degree) (height : List Bool → ℕ) (hb : BinaryFn height) (q : List Bool) (hq : InScope P q) :
    (machine P a F h hd height hb).model q = (IntegralMixedNormalizationDispatcherBits.machine P a F h hd height hb).model q := by
  change (if decide (InScope P q) then _ else _) = _
  rw [ite_eq_left (decide_eq_true hq)]
  rfl

theorem model_outside (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (hd : BinaryFn F.degree) (height : List Bool → ℕ) (hb : BinaryFn height) (q : List Bool) (hq : ¬InScope P q) :
    (machine P a F h hd height hb).model q = [] := by
  change (if decide (InScope P q) then _ else []) = []
  rw [ite_eq_right (by simpa only [decide_eq_true_eq] using hq)]

theorem canonical (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (hd : BinaryFn F.degree) (height : List Bool → ℕ) (hb : BinaryFn height) (q : List Bool) :
    ∃ z : ZMod (modulus P q), residueBits z = (machine P a F h hd height hb).model q := by
  by_cases HQ : InScope P q
  · rw [model_inside P a F h hd height hb q HQ]
    exact IntegralMixedNormalizationDispatcherBits.canonical P a F h hd height hb q
  · rw [model_outside P a F h hd height hb q HQ]
    exact ⟨0, (ArithmeticBits.zero_residueBits _).symm⟩
end LeanCanny.Algebra.IntegralMixedNormalizationScopedBits
