/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedFixedTupleContinuation
public import LeanCanny.Algebra.IntegralMixedFramedRunObservation
/-! # Entire constructed tuples give natural roots of the actual full-row data -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedFixedContinuation
open IntegralMixedHistory IntegralMixedFramedHistoryScript IntegralMixedFramedPhysicalIndex
open IntegralMixedFramedRunObservation (ofCommands)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem tuple_observation {n S B :ℕ} {P :SpatialSource n}
    (initial :State P S B 0 (Fin 0)) (cs :List (Instruction n B)) (hc :cs.length≤S+1)
    (z :Index (Fin 0) cs→ℝ) (hz :∀i,((run initial cs hc).sampler.rows i).eval₂ (Int.castRingHom ℝ) z=0) :
    ∃u :ℕ→ℝ,(ofCommands initial cs hc).Roots u ∧∀i,u (enumerate cs i).val=z i:=by
  let u :ℕ→ℝ:=IntegralMixedFramedBankObservation.extend (z∘(enumerate cs).symm)
  have HU (i :Index (Fin 0) cs) :u (enumerate cs i).val=z i:=by
    dsimp only [u,IntegralMixedFramedBankObservation.extend]
    rw [dite_eq_left (enumerate cs i).isLt]
    exact congrArg z ((enumerate cs).symm_apply_apply i)
  refine ⟨u,(IntegralMixedFramedRunObservation.roots_actual initial cs hc u).mpr ?_,HU⟩
  rw [show (fun i=>u (enumerate cs i).val)=z from funext HU]
  exact hz

theorem tuple_append_observation {n S B :ℕ} {P :SpatialSource n}
    (initial :State P S B 0 (Fin 0)) (Q :SpatialSource n)
    (hQ :PurePowerReductionBounds.dimension (n+1) Q.degree≤2^B)
    (older :List (Instruction n B)) (ho :older.length≤S+1)
    (cs :List (IntegralMixedFullHistoryScript.Command Q B)) (hc :older.length+cs.length≤S+1)
    (z :IntegralMixedFullHistoryScript.Index (Index (Fin 0) older) cs→ℝ)
    (hz :∀i,((IntegralMixedFullHistoryScript.continueRun (reframe (run initial older ho) Q hQ) cs hc).sampler.rows i).eval₂
      (Int.castRingHom ℝ) z=0) :
    ∃u :ℕ→ℝ,∃y :Index (Fin 0) (cs.map (wrap Q hQ)++older)→ℝ,HEq y z ∧
      (ofCommands initial (cs.map (wrap Q hQ)++older)
        (by simp only [List.length_append,List.length_map];omega)).Roots u ∧
      ∀i,u (enumerate (cs.map (wrap Q hQ)++older) i).val=y i:=by
  obtain ⟨y,hy,hr⟩:=tuple_append initial Q hQ older ho cs hc z hz
  obtain ⟨u,hu,hcol⟩:=tuple_observation initial (cs.map (wrap Q hQ)++older) _ y hr
  exact ⟨u,y,hy,hu,hcol⟩

end LeanCanny.Algebra.IntegralMixedFramedFixedContinuation
