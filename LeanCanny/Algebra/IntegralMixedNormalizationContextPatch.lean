/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizationRequestContexts
public import LeanCanny.Algebra.IntegralMixedVirtualContextLeaves
/-! # A mathematical reply patch outside virtual normalization contexts -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizationScopedBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
open IntegralMixedCutSource IntegralMixedNormalizationTopBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

abbrev Matches (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (hd : BinaryFn F.degree) (height : List Bool → ℕ) (hb : BinaryFn height) (answer : List Bool → List Bool) : Prop :=
  ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 5 →
    IntegralMixedVirtualContextBits.context P q → answer q = (IntegralMixedNormalizationDispatcherBits.machine P a F h hd height hb).model q
abbrev RawMatches (P : Parameters) (F : Family) (answer : List Bool → List Bool) : Prop :=
  ∀ q, IntegralMixedVirtualCaps.valid P q → IntegralMixedRoutineTaskBits.routine P q = 4 → isPhase .companion q →
    IntegralMixedVirtualContextBits.context P q → answer q = rawCutValue P F q

noncomputable def rawResidue (P : Parameters) (F : Family) (q : List Bool) : ZMod (modulus P q) :=
  (IntegralCriticalTotalSnapshotBits.integerEntry
    ((IntegralMixedCutSource.source F).coefficient (IntegralMixedVirtualTaskBits.saved P q) (get P .coefficient q))
    (get P .row q) (get P .col q) : ℤ)

theorem rawResidue_value (P : Parameters) (F : Family) (q : List Bool) : residueBits (rawResidue P F q) = rawCutValue P F q := rfl

noncomputable def patch (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (hd : BinaryFn F.degree) (height : List Bool → ℕ) (hb : BinaryFn height)
    (x : (q : List Bool) → ZMod (modulus P q)) (q : List Bool) : ZMod (modulus P q) :=
  if IntegralMixedVirtualContextBits.context P q then x q else
  if IntegralMixedRoutineTaskBits.routine P q = 5 then Classical.choose (IntegralMixedNormalizationDispatcherBits.canonical P a F h hd height hb q) else
  if IntegralMixedRoutineTaskBits.routine P q = 4 then rawResidue P F q else x q

theorem patch_good (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (hd : BinaryFn F.degree) (height : List Bool → ℕ) (hb : BinaryFn height)
    (x : (q : List Bool) → ZMod (modulus P q)) (q : List Bool) (hc : IntegralMixedVirtualContextBits.context P q) :
    patch P a F h hd height hb x q = x q := by simp only [patch, ite_eq_left hc]

theorem patch_normalization (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (hd : BinaryFn F.degree) (height : List Bool → ℕ) (hb : BinaryFn height)
    (x : (q : List Bool) → ZMod (modulus P q))
    (hm : Matches P a F h hd height hb (fun q => residueBits (x q))) :
    IntegralMixedNormalizationDispatcherBits.Matches P a F h hd height hb (fun q => residueBits (patch P a F h hd height hb x q)) := by
  intro q hv hr
  dsimp only
  by_cases hc : IntegralMixedVirtualContextBits.context P q
  · rw [patch_good P a F h hd height hb x q hc]
    exact hm q hv hr hc
  · simp only [patch, ite_eq_right hc, ite_eq_left hr]
    exact Classical.choose_spec (IntegralMixedNormalizationDispatcherBits.canonical P a F h hd height hb q)

theorem patch_raw (P : Parameters) (a : Access P) (F : Family) (h : IntegralMixedVirtualQueryBits.InputMetadata F)
    (hd : BinaryFn F.degree) (height : List Bool → ℕ) (hb : BinaryFn height)
    (x : (q : List Bool) → ZMod (modulus P q)) (hm : RawMatches P F (fun q => residueBits (x q))) :
    IntegralMixedNormalizationTopBits.RawMatches P F (fun q => residueBits (patch P a F h hd height hb x q)) := by
  intro q hv hr hp
  dsimp only
  by_cases hc : IntegralMixedVirtualContextBits.context P q
  · rw [patch_good P a F h hd height hb x q hc]
    exact hm q hv hr hp hc
  · have hn : IntegralMixedRoutineTaskBits.routine P q ≠ 5 := by omega
    simp only [patch, ite_eq_right hc, ite_eq_right hn, ite_eq_left hr]
    exact rawResidue_value P F q
end LeanCanny.Algebra.IntegralMixedNormalizationScopedBits
