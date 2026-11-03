/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCriticalSuccessorRows
public import LeanCanny.Encoding.IntegralFramedPhysicalNaturalPoint
/-! # Every literal critical-step joint root has a complete child word

The same full tuple is reindexed through the actual creating block. This
includes singular roots; there is no separate coordinate-root choice.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedPhysicalCriticalStepCapture
open LeanCanny.Algebra LeanCanny.Geometry LeanCanny.Computation IntegralCriticalHistoryTask IntegralMixedHistory
open IntegralMixedFramedHistoryFamilyBits (Plan family commands instruction keyAt prefixLength)
open IntegralMixedFramedPhysicalIndex (arity enumerate stepEquiv)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

noncomputable local instance familyFintype (P : Parameters) (D : Plan P)
    (H : IntegralMixedFramedHistoryFamilyBits.Data P D) (key : List Bool) :
    Fintype ((family P D H).physical key) :=
  inferInstanceAs (Fintype (IntegralMixedFramedHistoryScript.Index (Fin 0) (commands P D key)))

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (key : List Bool) (r : CriticalRule (P.ambient (pairFst key)))

noncomputable def natural
    (z : (((family P D H).physical key⊕FlatAffineCriticalStage.Variables (P.ambient (pairFst key)+1))⊕Unit)→ℝ)
    (j : ℕ) : ℝ :=
  if hj : j<arity (commands P D key)+IntegralMixedFramedPhysicalIndex.added
      (.critical (P:=(family P D H).spatial key) (B:=P.width (pairFst key)) r) then
    z ((stepEquiv (.critical (P:=(family P D H).spatial key) (B:=P.width (pairFst key)) r)
      (enumerate (commands P D key))).symm ⟨j,hj⟩) else 0

theorem tuple_natural
    (z : (((family P D H).physical key⊕FlatAffineCriticalStage.Variables (P.ambient (pairFst key)+1))⊕Unit)→ℝ) :
    IntegralMixedFramedCriticalSuccessorRows.tuple P D H key r (natural P D H key r z)=z :=by
  funext i
  unfold IntegralMixedFramedCriticalSuccessorRows.tuple natural
  rw [dite_eq_left ((stepEquiv (.critical (P:=(family P D H).spatial key)
    (B:=P.width (pairFst key)) r) (enumerate (commands P D key))) i).isLt]
  exact congrArg z (Equiv.symm_apply_apply _ i)

theorem roots_natural
    (z : (((family P D H).physical key⊕FlatAffineCriticalStage.Variables (P.ambient (pairFst key)+1))⊕Unit)→ℝ)
    (hz : ∀i,((criticalStep ((family P D H).state key) ((family P D H).birth_bound key) r).sampler.rows i).eval₂
      (Int.castRingHom ℝ) z=0) :
    ∀i,(IntegralMixedFramedCriticalSuccessorRows.rows P D H key r i).eval₂
      (Int.castRingHom ℝ) (natural P D H key r z)=0 :=by
  apply (IntegralMixedFramedCriticalSuccessorRows.rows_zero_iff P D H key r _).mpr
  rw [tuple_natural]
  exact hz

theorem exists_child_word
    (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
    (child : List Bool→List Bool) (hpos : ∀c,0<(family P D H).birth (child c))
    (c : List Bool) (hb : prefixLength P key≤P.cap (pairFst key))
    (hc : (instruction P D key).command=.critical r)
    (hkey : child c=keyAt (pairFst key) (prefixLength P key+1) c)
    (z : (((family P D H).physical key⊕FlatAffineCriticalStage.Variables (P.ambient (pairFst key)+1))⊕Unit)→ℝ)
    (hz : ∀i,((criticalStep ((family P D H).state key) ((family P D H).birth_bound key) r).sampler.rows i).eval₂
      (Int.castRingHom ℝ) z=0) :
    ∃w,∃hv : SquareSampleCompleteVertices.Valid (IntegralFramedPhysicalSquare.input P D H L F C hs child hpos) c w,
      ∀j<IntegralFramedPhysicalSquare.count P D (child c),
        IntegralFramedPhysicalSquare.naturalPoint P D H L F C hs child hpos c w hv j=
          natural P D H key r z j :=by
  have HR : ∀i,(IntegralMixedFramedPhysicalRowTransport.keyRow P D (child c) i).eval₂
      (Int.castRingHom ℝ) (natural P D H key r z)=0 :=by
    intro i
    rw [hkey,IntegralMixedFramedCriticalSuccessorRows.keyRow_successor P D H key c hb r hc i]
    exact roots_natural P D H key r z hz i
  obtain ⟨w,hv,hw⟩:=IntegralFramedPhysicalSquare.exists_joint_natural P D H L F C hs child hpos c
    (natural P D H key r z) HR
  refine ⟨w,hv,fun j hj=>?_⟩
  exact (IntegralFramedPhysicalSquare.naturalPoint_at P D H L F C hs child hpos c w hv ⟨j,hj⟩).trans (hw ⟨j,hj⟩)

end LeanCanny.Encoding.IntegralMixedPhysicalCriticalStepCapture
