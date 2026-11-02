/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFullGram
public import LeanCanny.Algebra.IntegralMixedArithmeticEntries
/-! # The shared arithmetic current model supplies every Gram row reply -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFullGramBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

theorem correct_of_arithmetic (P : Parameters) (a : Access P) (D : IntegralMixedFullHistoryFamilyBits.Data P)
    (h : IntegralMixedArithmeticEntriesBits.Controls P D) (x : (q : List Bool) → ZMod (modulus P q))
    (he : IntegralMixedArithmeticEntriesBits.Matches P a D h (fun q => residueBits (x q)))
    (hm : Matches P a D h.core (fun q => residueBits (x q))) :
    Correct (machine P a D h.core) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) :=
  correct P a D h.core x (IntegralMixedArithmeticEntriesBits.entry_matches P a D h _ he) hm
end LeanCanny.Algebra.IntegralMixedFullGramBits
