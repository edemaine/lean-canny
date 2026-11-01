/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalNativeLowerContracts
/-! # Native layered product-entry branch over actual factor powers -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalNativeProductEntryBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralCriticalFlatActualSources IntegralCriticalNativeBranchBits IntegralCriticalNativeLowerBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalTotalCreatingBits.atFamily
attribute [local irreducible] IntegralCriticalHistoryTask.get IntegralCriticalHistoryTask.numericCap IntegralCriticalHistoryTask.rank
noncomputable abbrev source (F : Scripts) := IntegralCriticalFlatActualLow.source F
noncomputable abbrev access (F : Scripts) (h : Controls F) := IntegralCriticalFlatActualLow.access F h
noncomputable abbrev program (F : Scripts) := IntegralCriticalFlatGenericProductEntryBits.program F.toParameters (source F)
noncomputable abbrev input (F : Scripts) := IntegralCriticalFlatGenericProductEntryBits.input F.toParameters (source F)
noncomputable abbrev family (F : Scripts) := IntegralPowerProductBits.productFamily (IntegralMonomialTermBits.family (source F))

theorem certificates (F : Scripts) (h : Controls F) :
    (program F).controller.Certificates (encQ := Turing.MultiTapeTM.encBits) (encS := SingleCall.encState) :=
  (program F).certificates (IntegralCriticalFlatGenericProductEntryBits.controls F.toParameters h.task.toAccess (source F) (access F h))

noncomputable def machine (F : Scripts) (h : Controls F) : Machine :=
  ofPreparedSingleCall (program F) (certificates F h) (input F)
    (IntegralCriticalFlatGenericProductEntryBits.input_FP F.toParameters h.task.toAccess (source F) (access F h))
    (selected F .productEntry) (selected_FP F h .productEntry) (IntegralCriticalActualLowMatrixModel.productEntry F)
    (IntegralCriticalHistoryEvaluator.residueWidth F.toParameters)
    (IntegralCriticalHistoryEvaluator.residueWidth_unary F.toParameters h.task.toAccess)

theorem parent_query (F : Scripts) (q : List Bool) :
    pairFst (MatrixProductBits.factorQuery (family F) (input F q)) = q := by
  simp only [MatrixProductBits.factorQuery, IntegralCriticalFlatGenericProductEntryBits.input, pairFst_pair]

theorem query_eq (F : Scripts) (q : List Bool) : (program F).query (input F q) =
    IntegralCriticalFlatFactorQuery.writer F.toParameters .factorPower (MatrixProductBits.factorQuery (family F) (input F q)) := rfl

theorem requests_frame (F : Scripts) (reply : List Bool → List Bool) (budget : List Bool → ℕ) (q c : List Bool)
    (hp : isPhase .productEntry q) (hc : ((program F).controller.prepare (input F)).Requests reply budget q c) : Frame F q c := by
  have H0 := (RecursiveController.Controller.prepare_requests_iff (program F).controller (input F) reply budget q c).mp hc
  have H1 := ((program F).requests_iff reply (fun _ => budget q) (input F q) c).mp H0
  apply Eq.mpr (congrArg (Frame F q) H1.2)
  rw [query_eq]
  have HP : 4 < phase (pairFst (MatrixProductBits.factorQuery (family F) (input F q))) := by
    rw [parent_query]
    change phase q = 5 at hp
    omega
  have HF := frame_factor F .factorPower (MatrixProductBits.factorQuery (family F) (input F q)) HP
  rw [parent_query] at HF
  exact HF

theorem value_at (F : Scripts) (h : Controls F) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hm : Matches F x)
    (q : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F q) :
    (program F).value (answer F x) (input F q) = IntegralCriticalActualLowMatrixModel.productEntry F q := by
  apply Eq.trans (single_value_congr_at (program F) (answer F x) (IntegralCriticalActualFactorModel.power F) (input F q) ?_)
    (IntegralCriticalActualProductEntryTransport.entry_value F h q hv)
  intro _
  rw [query_eq]
  exact matches_factor F x hm .factorPower (by decide) _ (by rw [parent_query]; exact hv)

theorem correct (F : Scripts) (h : Controls F) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hm : Matches F x) :
    Correct (machine F h) (answer F x) (Frame F) := by
  apply prepared_correct_of_frame F h .productEntry (program F) (certificates F h) (input F)
    (IntegralCriticalFlatGenericProductEntryBits.input_FP F.toParameters h.task.toAccess (source F) (access F h))
    (IntegralCriticalActualLowMatrixModel.productEntry F) x
  · intro q hq
    exact value_at F h x hm q ((selected_iff F .productEntry q).mp hq).1
  · intro q c budget hq hc
    exact requests_frame F (answer F x) budget q c ((selected_iff F .productEntry q).mp hq).2 hc

end LeanCanny.Algebra.IntegralCriticalNativeProductEntryBits
