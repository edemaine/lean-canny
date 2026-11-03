/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalRealizedVertex
/-! # Original integer roots yield one full vertex of the actual saved run

The hypotheses refer to the literal creating commands and their ORIGINAL
untruncated integer polynomials. Their actual sampler is constructed by
integer root extension; no supplied realization or scalar-only extraction
is needed. Reframing changes neither its full rows nor bank values.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalSquare
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family commands initial prefixLength)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)

theorem realizes_integer (key : List Bool) (values : ℕ→ℝ)
    (hr : ∀i : Fin (commands P D key).length,
      IntegralMixedIntegerRealization.Root (commands P D key)[i].command (values i.val)) :
    IntegralMixedIntegerRealization.Realizes ((family P D H).state key) values :=by
  have HC : (commands P D key).length≤P.cap (pairFst key)+1+1 :=by
    rw [commands,IntegralMixedFramedHistoryScript.paddedPast_length]
    unfold prefixLength IntegralMixedFullHistoryFamilyBits.prefixLength
    exact (min_le_right _ _).trans (Nat.le_succ _)
  have HE:=IntegralMixedFramedIntegerRealization.realizes (initial P D (pairFst key))
    (fun i : Fin 0=>Fin.elim0 i) (fun i=>Fin.elim0 i) (commands P D key) HC values hr
  exact HE

theorem exists_integer (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (key : List Bool→List Bool) (hpos : ∀c,0<(family P D H).birth (key c)) (c : List Bool) (values : ℕ→ℝ)
    (hr : ∀i : Fin (commands P D (key c)).length,
      IntegralMixedIntegerRealization.Root (commands P D (key c))[i].command (values i.val)) :
    ∃w,∃hw : SquareSampleCompleteVertices.Valid (input P D H L F C hs key hpos) c w,
      w.length=SquareSampleCompleteVertices.width (input P D H L F C hs key hpos) c ∧
      ∀i : Fin ((family P D H).birth (key c)),point P D H L F C hs key hpos c w hw i=values i.val :=
  exists_realized P D H L F C hs key hpos c values (realizes_integer P D H (key c) values hr)
end LeanCanny.Encoding.IntegralFramedPhysicalSquare
