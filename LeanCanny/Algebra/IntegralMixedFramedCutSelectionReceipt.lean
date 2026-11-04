/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedHistoryFamily
/-! # Literal creating commands preserve the entire dependent selected-cut record -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedHistoryFamilyBits
open LeanCanny.Encoding IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralCriticalHistoryTask
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem selection_of_command (P : Parameters) (D : Plan P) (H : Data P D) (key : List Bool)
    (r : IntegralMixedCriticalSweep.Rule (P.ambient (pairFst key)))
    (k : IntegralMixedRelativeCuts.Kind (instruction P D key).source r) (d : ℕ)
    (ha : d≤IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient (pairFst key)+1) (instruction P D key).source.degree)
    (hd : d≤2^P.width (pairFst key))
    (hc : (instruction P D key).command=.cut r k d ha hd) :
    selection P D H key=⟨r,k,d,ha⟩:=by
 unfold selection
 rw [hc]

theorem selection_of_command_heq (P : Parameters) (D : Plan P) (H : Data P D) (key : List Bool)
    (i : Instruction (P.ambient (pairFst key)) (P.width (pairFst key))) (hi : instruction P D key=i)
    (r : IntegralMixedCriticalSweep.Rule (P.ambient (pairFst key)))
    (k : IntegralMixedRelativeCuts.Kind i.source r) (d : ℕ)
    (ha : d≤IntegralMixedExceptionalBounds.auxiliaryCap (P.ambient (pairFst key)+1) i.source.degree)
    (hd : d≤2^P.width (pairFst key)) (hc : i.command=.cut r k d ha hd) :
    HEq (selection P D H key) (⟨r,k,d,ha⟩ :IntegralMixedFullHistoryFamilyBits.Selection i.source):=by
 subst i
 exact heq_of_eq (selection_of_command P D H key r k d ha hd hc)

end LeanCanny.Algebra.IntegralMixedFramedHistoryFamilyBits
