/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedNormalizedCompanionNative
/-! # Normalized producer and companion phases share one native model -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedNormalizedCompanionDispatcherBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedNormalizedCompanionBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

noncomputable def leadingNode (P : Parameters) (a : Access P) (F : Family) (hd : BinaryFn F.degree) : PhaseNode phase where
  machine := leadingStage P a F hd
  code := 0
  selected_phase q hs := ((selected_iff P .originalCoefficient q).mp hs).2.2.1

noncomputable def companionNode (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (hd : BinaryFn F.degree) : PhaseNode phase where
  machine := companionStage P a F h hd
  code := 26
  selected_phase q hs := ((selected_iff P .companion q).mp hs).2.2.1

noncomputable def nodes (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (hd : BinaryFn F.degree) : List (PhaseNode phase) :=
  [leadingNode P a F hd, companionNode P a F h hd]

noncomputable def machine (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (hd : BinaryFn F.degree) : Machine :=
  phaseDispatch (nodes P a F h hd) zero

theorem nodes_distinct (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (hd : BinaryFn F.degree) :
    ((nodes P a F h hd).map PhaseNode.code).Nodup := by change [0, 26].Nodup; decide

theorem model_leading (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (hd : BinaryFn F.degree) (q : List Bool)
    (hs : selected P .originalCoefficient q = true) :
    (machine P a F h hd).model q = IntegralMixedNormalizationTopBits.leadingValue P F q :=
  phaseDispatch_model_selected _ _ q (leadingNode P a F hd) (nodes_distinct P a F h hd)
    List.mem_cons_self hs

theorem model_companion (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (hd : BinaryFn F.degree) (q : List Bool)
    (hs : selected P .companion q = true) :
    (machine P a F h hd).model q = companionValue P F q :=
  phaseDispatch_model_selected _ _ q (companionNode P a F h hd) (nodes_distinct P a F h hd)
    (List.mem_cons_of_mem _ List.mem_cons_self) hs

theorem machine_selected (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (hd : BinaryFn F.degree) (q : List Bool) :
    (machine P a F h hd).selected q = true := by
  change ((selected P .originalCoefficient q) || ((selected P .companion q) || true)) = true
  rw [Bool.or_true, Bool.or_true]

theorem correct (P : Parameters) (a : Access P) (F : Family)
    (h : IntegralMixedVirtualQueryBits.InputMetadata F) (hd : BinaryFn F.degree)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (x : (q : List Bool) → ZMod (modulus P q))
    (hm : NormalizationMatches P F (fun q => residueBits (x q)))
    (hl : LeadingMatches P F (fun q => residueBits (x q))) :
    Correct (machine P a F h hd) (fun q => residueBits (x q)) (IntegralMixedRoutineTaskBits.Frame P) := by
  apply phaseDispatch_correct _ _ _ _ (zero_correct _ _)
  intro b hb
  rcases List.mem_cons.mp hb with rfl | hb
  · exact leading_correct P a F hd g x hm
  · rcases List.mem_cons.mp hb with rfl | hb
    · exact companion_correct P a F h hd g x hm hl
    · cases hb

end LeanCanny.Algebra.IntegralMixedNormalizedCompanionDispatcherBits
