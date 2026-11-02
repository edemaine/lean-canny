/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedGramScopedCurrent
public import LeanCanny.Algebra.IntegralMixedFullEntryBoundaries
/-! # Full-history Gram arithmetic uses only current routine-two entries -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullGramBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

noncomputable abbrev machine (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : IntegralMixedFullCoreBits.Controls P D) :=
  IntegralMixedGramScopedBits.machine P a (IntegralMixedFullEntryBits.family P D) (IntegralMixedFullEntryBits.input P a D h)
abbrev Matches (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : IntegralMixedFullCoreBits.Controls P D) :=
  IntegralMixedGramScopedBits.CurrentMatches P a (IntegralMixedFullEntryBits.family P D) (IntegralMixedFullEntryBits.input P a D h)

theorem correct (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : IntegralMixedFullCoreBits.Controls P D) (x : (q : List Bool) → ZMod (modulus P q))
    (he : IntegralMixedFullEntryBits.Matches P a D h (fun q => residueBits (x q))) (hm : Matches P a D h (fun q => residueBits (x q))) :
    Correct (machine P a D h) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) :=
  IntegralMixedGramScopedBits.correct_of_entries P a (IntegralMixedFullEntryBits.family P D) (IntegralMixedFullEntryBits.input P a D h)
    (IntegralMixedFullHistoryFamilyBits.geometry P D) x he hm

theorem canonical (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : IntegralMixedFullCoreBits.Controls P D) (q : List Bool) : ∃ z : ZMod (modulus P q), residueBits z = (machine P a D h).model q :=
  IntegralMixedGramScopedBits.canonical P a (IntegralMixedFullEntryBits.family P D) (IntegralMixedFullEntryBits.input P a D h) q
end LeanCanny.Algebra.IntegralMixedFullGramBits
