/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalGridTransport
public import LeanCanny.Algebra.IntegralMixedPhysicalNativeMonomial
public import LeanCanny.Algebra.IntegralMixedPhysicalNativeProductPower
public import LeanCanny.Algebra.IntegralMixedPhysicalLowCanonical
public import LeanCanny.Algebra.IntegralCriticalNativeLowerContracts
/-! # Native guarded physical grid terms and finite cleared sums -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalNativeLowerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedPhysicalCriticalBits IntegralMixedPhysicalQueryBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false
noncomputable abbrev gridProgram (P : Parameters) (F : Family) := IntegralCriticalFlatGenericGridBits.program P (source P F)
noncomputable abbrev gridBudget (P : Parameters) (F : Family) := IntegralCriticalFlatGenericGridBits.budget P (source P F)
noncomputable abbrev gridTermProgram (P : Parameters) (F : Family) := IntegralCriticalFlatGenericGridBits.termProgram P (source P F)
abbrev gridTermInput (P : Parameters) := IntegralCriticalFlatGridBits.termInput P

theorem frame_grid (P : Parameters) (p : Phase) (z : List Bool) (hp : p.code < phase (pairFst z)) :
    IntegralMixedRoutineTaskBits.Frame P (pairFst z) (IntegralCriticalFlatGridBits.writer P p z) := by
  apply IntegralMixedMatrixFrames.frame_of_ordinary
  · unfold IntegralMixedRoutineTaskBits.routine
    rw [IntegralCriticalFlatGridBits.writer_other P p z .slot14 (by decide)]
  · exact ⟨IntegralCriticalFlatGridBits.writer_root P p z, IntegralCriticalFlatGridBits.writer_length P p z,
      IntegralCriticalFlatGridBits.writer_lower_rank P p z hp⟩

abbrev GridTermRepliesAt (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q : List Bool) : Prop :=
  (gridTermProgram P F).request (gridTermInput P q) = true →
    reply ((gridTermProgram P F).query (gridTermInput P q)) =
      IntegralMixedPhysicalGridBits.product P F ((gridTermProgram P F).query (gridTermInput P q))

theorem gridTerm_reply (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q : List Bool)
    (he : GridTermRepliesAt P F reply q) :
    ClearedCoordinateExponentBits.mask (IntegralClearedCoefficientBits.maskLayout
      (IntegralCriticalFlatGenericGridBits.source P (source P F))) (gridTermInput P q) →
      reply (IntegralCriticalFlatGridBits.writer P .productPower (gridTermInput P q)) =
        (IntegralClearedCoefficientBits.termSource (IntegralCriticalFlatGenericGridBits.source P (source P F))).value (gridTermInput P q) := by
  intro hm
  exact (he ((IntegralCriticalFlatGenericGridBits.term_request_iff P (source P F) q).mpr hm)).trans
    (IntegralMixedPhysicalGridBits.term_product_child P F q)

theorem gridTerm_value_at (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q : List Bool)
    (he : GridTermRepliesAt P F reply q) :
    (gridTermProgram P F).value reply (gridTermInput P q) = IntegralMixedPhysicalGridBits.term P F q :=
  IntegralCriticalFlatGenericGridBits.term_value_at P (source P F) reply q (gridTerm_reply P F reply q he)

noncomputable def gridTermMachine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : Machine :=
  ofPreparedSingleCall (gridTermProgram P F)
    ((gridTermProgram P F).certificates (IntegralCriticalFlatGenericGridBits.term_controls P a (source P F) (sourceAccess P a F h)))
    (gridTermInput P) (IntegralCriticalFlatGridBits.termInput_FP P a)
    (selectedValid P .originalGridTerm) (selectedValid_FP P a .originalGridTerm)
    (IntegralMixedPhysicalGridBits.term P F) (replyBound P) (replyBound_unary P a)

theorem gridTerm_requests_frame (P : Parameters) (S : IntegralEulerBits.Source)
    (reply : List Bool → List Bool) (budget : List Bool → ℕ) (q c : List Bool) (hp : isPhase .originalGridTerm q)
    (hc : ((IntegralCriticalFlatGenericGridBits.termProgram P S).controller.prepare (gridTermInput P)).Requests reply budget q c) :
    IntegralMixedRoutineTaskBits.Frame P q c := by
  let C := IntegralCriticalFlatGenericGridBits.termProgram P S
  have H0 := (RecursiveController.Controller.prepare_requests_iff C.controller (gridTermInput P) reply budget q c).mp hc
  have H1 := (C.requests_iff reply (fun _ => budget q) (gridTermInput P q) c).mp H0
  have HQ : C.query (gridTermInput P q) = IntegralCriticalFlatGridBits.writer P .productPower (gridTermInput P q) := rfl
  have HO : pairFst (gridTermInput P q) = q := IntegralCriticalFlatGridBits.termInput_parent P q
  have HF := frame_grid P .productPower (gridTermInput P q) (by rw [HO]; change phase q = 7 at hp; change 6 < phase q; omega)
  rw [HO] at HF
  exact Eq.mpr (congrArg (IntegralMixedRoutineTaskBits.Frame P q) (H1.2.trans HQ)) HF

theorem gridTerm_correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (reply : List Bool → List Bool) (he : ∀ q, selectedValid P .originalGridTerm q = true → GridTermRepliesAt P F reply q) :
    Correct (gridTermMachine P a F h) reply (IntegralMixedRoutineTaskBits.Frame P) := by
  apply ofPreparedSingleCall_correct
  · intro q hq
    exact gridTerm_value_at P F reply q (he q hq)
  · intro q hq hr
    have HV := gridTerm_value_at P F reply q (he q hq)
    simp only [SingleCall.Program.value, hr, ite_true] at HV
    change pairSnd (pair _ _) = _ at HV
    rw [pairSnd_pair] at HV
    change (reply ((gridTermProgram P F).query (gridTermInput P q))).length ≤ replyBound P q
    rw [HV]
    obtain ⟨z, hz⟩ := IntegralMixedPhysicalCanonicalBits.term_canonical P F q
    rw [← hz]
    let : NeZero (modulus P q) := ⟨modulus_ne_zero P q⟩
    exact residueBits_length_le _ _
  · intro q c budget hq hc
    exact gridTerm_requests_frame P (source P F) reply budget q c ((selectedValid_iff P .originalGridTerm q).mp hq).2.2 hc

abbrev GridRepliesAt (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q : List Bool) : Prop :=
  ∀ k < gridBudget P F q,
    reply (IntegralCriticalFlatGridBits.writer P .originalGridTerm (pair q (BinaryNatCode.encode k))) =
      IntegralMixedPhysicalGridBits.term P F (IntegralCriticalFlatGridBits.writer P .originalGridTerm (pair q (BinaryNatCode.encode k)))

theorem grid_replies (P : Parameters) (F : Family) (g : IntegralMixedPhysicalCaps.RootGeometry P F)
    (reply : List Bool → List Bool) (q : List Bool) (he : GridRepliesAt P F reply q) :
    ∀ k < gridBudget P F q,
      reply (IntegralCriticalFlatGridBits.writer P .originalGridTerm (pair q (BinaryNatCode.encode k))) =
        IntegralClearedCoefficientBits.maskedProgram (IntegralCriticalFlatGenericGridBits.source P (source P F)) (pair q (BinaryNatCode.encode k)) :=
  fun k hk => (he k hk).trans (IntegralMixedPhysicalGridBits.grid_child P F g q k hk)

noncomputable def gridMachine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : Machine where
  State := RecursiveFold.State
  defaultValue := default
  encoding := RecursiveFold.encState
  controller := (gridProgram P F).controller
  certificates := IntegralCriticalFlatGenericGridBits.certificates P a (source P F) (sourceAccess P a F h)
  selected := selectedValid P .clearedGridSum
  selected_FP := selectedValid_FP P a .clearedGridSum
  model := IntegralMixedPhysicalSpatialBits.cleared P F
  clock := gridBudget P F
  clock_binary := IntegralCriticalFlatGenericGridBits.budget_binary P a (source P F) (sourceAccess P a F h)
  stateBound := IntegralCriticalFlatGenericGridBits.stateBound P (source P F)
  stateBound_unary := IntegralCriticalFlatGenericGridBits.stateBound_unary P a (source P F) (sourceAccess P a F h)

theorem grid_correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (g : IntegralMixedPhysicalCaps.RootGeometry P F) (reply : List Bool → List Bool)
    (he : ∀ q, selectedValid P .clearedGridSum q = true → GridRepliesAt P F reply q) :
    Correct (gridMachine P a F h) reply (IntegralMixedRoutineTaskBits.Frame P) := by
  constructor
  · intro q _
    exact IntegralCriticalFlatGenericGridBits.halted_after P (source P F) reply q
  · intro q t hq hh
    simp only [gridMachine] at hh ⊢
    exact ((gridProgram P F).output_when_halted reply q t hh).trans
      (IntegralCriticalFlatGenericGridBits.value_at P (source P F) reply q
        (grid_replies P F g reply q (he q hq)))
  · intro q t hq
    exact IntegralCriticalFlatGenericGridBits.state_length_at P (source P F) reply q
      (grid_replies P F g reply q (he q hq)) t
  · intro q c budget hq hc
    have HP := ((selectedValid_iff P .clearedGridSum q).mp hq).2.2
    have HC := IntegralCriticalNativeLowerBits.fold_requests_bound (gridProgram P F) reply budget q c hc
    obtain ⟨k, _, rfl⟩ := (IntegralCriticalFlatGenericGridBits.requests_iff P (source P F) reply q c).mp HC
    simpa only [pairFst_pair] using frame_grid P .originalGridTerm (pair q (BinaryNatCode.encode k))
      (by simp only [pairFst_pair]; change phase q = 8 at HP; change 7 < phase q; omega)
end LeanCanny.Algebra.IntegralMixedPhysicalNativeLowerBits
