/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCompanionColumnsBase
/-! # Observe a companion after an already identified typed prefix -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedFixedContinuation
open LeanCanny.Geometry LeanCanny.Encoding IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedPhysicalIndex IntegralMixedPointCompanion IntegralMixedCausalRowConstructor
open scoped Classical
set_option backward.isDefEq.respectTransparency false

theorem companion_observation_from {n S B m L : ℕ} {P Q : SpatialSource n} {κ : Type} [fκ : Fintype κ]
    (initial : State P S B 0 (Fin 0))
    (hQ : PurePowerReductionBounds.dimension (n+1) Q.degree≤2^B)
    (older : List (Instruction n B)) (ho : older.length≤S+1)
    (x : State Q S B m κ) (hi : Index (Fin 0) older=κ) (hm : older.length=m)
    (hx : HEq (reframe (run initial older ho) Q hQ) x)
    (e : κ≃Fin L) (hL : arity older=L) (he : HEq (enumerate older) e)
    (frozen : Finset (Fin (n+1))) (double : Fin (n+1)→Bool)
    (rows : Fin (n+1)→Row m) (g : Free frozen) (z : κ→ℝ)
    (φ : x.sampler.scalarPrefix.carrier→ₐ[ℤ]ℝ)
    (old : Fin m→ℝ) (p : Fin (n+1)→ℝ) (js : List (Free frozen))
    (room : m+js.length≤S+1)
    (R : Realized x frozen double rows g z φ old p js room) :
    ∃u : ℕ→ℝ,
      (IntegralMixedFramedRunObservation.ofCommands initial
        ((commands (P:=Q) (B:=B) frozen double rows g js).map (wrap Q hQ)++older)
        (by simp only [List.length_append,List.length_map,commands_length];omega)).Roots u ∧
      (∀i,u (e i).val=z i) ∧
      (∀k : Fin js.length,∀i,
        u (L+(2*n+4)*(js.length-1-k.val)+i.val)^
          UniformIntegralPowerSchedule.physical S (2^B) (m+(js.length-1-k.val))=p i) ∧
      ∀i : Fin (m+js.length),
        (IntegralMixedFramedRunObservation.ofCommands initial
          ((commands (P:=Q) (B:=B) frozen double rows g js).map (wrap Q hQ)++older)
          (by simp only [List.length_append,List.length_map,commands_length];omega)).point u i.val=
            values p old js i:=by
  cases hi
  have HInst : fκ=IntegralMixedFramedHistoryScript.indexFintype (Fin 0) older:=Subsingleton.elim _ _
  subst fκ
  cases hm
  cases hL
  have HX : reframe (run initial older ho) Q hQ=x:=eq_of_heq hx
  subst x
  have HE : enumerate older=e:=eq_of_heq he
  subst e
  exact @companion_observation n B Q n S B P initial Q hQ older ho frozen double rows g z φ old p js room R

end LeanCanny.Algebra.IntegralMixedFramedFixedContinuation
