/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedPhysicalSquareContext
/-! # Reindexing actual full physical sampler inputs

Every input field, including annihilator and numerical choice bounds,
composes literally. Complete labels therefore preserve the SAME ordinal
sample; no independent-system or arbitrary root-label invariance is used.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedPhysicalSquare
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan family)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

variable (P : Parameters) (D : Plan P) (H : IntegralMixedFramedHistoryFamilyBits.Data P D)
  (L F C : List Bool→ℕ) (hs : IntegralMixedFramedStepHeight.FamilyInputs P D L F C)
  (key : List Bool→List Bool) (hpos : ∀q,0<(family P D H).birth (key q))
  (f : List Bool→List Bool)

theorem finite_comp :finite P D H L F C hs (key∘f) (fun q=>hpos (f q))=
    NoInfinitySquareSample.comp (finite P D H L F C hs key hpos) f :=rfl

theorem input_comp :input P D H L F C hs (key∘f) (fun q=>hpos (f q))=
    SquareSampleInput.comp (input P D H L F C hs key hpos) f :=rfl

theorem width_comp (q : List Bool) :SquareSampleCompleteVertices.width
    (input P D H L F C hs (key∘f) (fun q=>hpos (f q))) q=
    SquareSampleCompleteVertices.width (input P D H L F C hs key hpos) (f q) :=by
  rw [input_comp]
  exact SquareSampleCompleteNaturality.complete_width_comp _ _ _

theorem valid_comp (q w : List Bool) :SquareSampleCompleteVertices.Valid
    (input P D H L F C hs (key∘f) (fun q=>hpos (f q))) q w↔
    SquareSampleCompleteVertices.Valid (input P D H L F C hs key hpos) (f q) w :=by
  rw [input_comp]
  exact SquareSampleCompleteNaturality.complete_valid_comp _ _ _ _

theorem candidate_comp (q w : List Bool)
    (hc : SquareSampleCompleteVertices.Valid (input P D H L F C hs (key∘f) (fun q=>hpos (f q))) q w)
    (ho : SquareSampleCompleteVertices.Valid (input P D H L F C hs key hpos) (f q) w) :
    (SquareSampleCompleteVertices.candidate (input P D H L F C hs (key∘f) (fun q=>hpos (f q))) q w hc).val=
      (SquareSampleCompleteVertices.candidate (input P D H L F C hs key hpos) (f q) w ho).val :=
  SquareSampleCompleteNaturality.candidate_comp (input P D H L F C hs key hpos) f q w hc ho

theorem naturalPoint_comp (q w : List Bool)
    (hc : SquareSampleCompleteVertices.Valid (input P D H L F C hs (key∘f) (fun q=>hpos (f q))) q w)
    (ho : SquareSampleCompleteVertices.Valid (input P D H L F C hs key hpos) (f q) w) :
    naturalPoint P D H L F C hs (key∘f) (fun q=>hpos (f q)) q w hc=
      naturalPoint P D H L F C hs key hpos (f q) w ho :=by
  have HE:=candidate_comp P D H L F C hs key hpos f q w hc ho
  funext i
  unfold naturalPoint
  simp only [Function.comp_apply]
  split_ifs with hi
  · exact congrFun HE ⟨i,hi⟩
  · rfl


theorem point_comp (q w : List Bool)
    (hc : SquareSampleCompleteVertices.Valid (input P D H L F C hs (key∘f) (fun q=>hpos (f q))) q w)
    (ho : SquareSampleCompleteVertices.Valid (input P D H L F C hs key hpos) (f q) w) :
    point P D H L F C hs (key∘f) (fun q=>hpos (f q)) q w hc=
      point P D H L F C hs key hpos (f q) w ho :=by
  have HE:=candidate_comp P D H L F C hs key hpos f q w hc ho
  unfold point joint
  rw [HE]
  rfl

end LeanCanny.Encoding.IntegralFramedPhysicalSquare
