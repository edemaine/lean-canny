/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalNativeLowerContracts
/-! # Native finite folds of actual lower arithmetic values -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalNativeLowerFoldBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralCriticalFlatActualSources IntegralCriticalNativeBranchBits IntegralCriticalNativeLowerBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalTotalCreatingBits.atFamily
attribute [local irreducible] IntegralCriticalHistoryTask.get IntegralCriticalHistoryTask.numericCap IntegralCriticalHistoryTask.rank
noncomputable abbrev euler (F : Scripts) := IntegralCriticalTotalCreatingBits.euler F
noncomputable abbrev frozen (F : Scripts) := IntegralCriticalTotalCreatingBits.FrozenStages.source F
noncomputable abbrev frozenAccess (F : Scripts) (h : Controls F) := IntegralCriticalTotalCreatingBits.FrozenStages.access F h

theorem grid_replies (F : Scripts) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hm : Matches F x)
    (q : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F q) :
    ∀ i < IntegralCriticalFlatGenericGridBits.budget F.toParameters (euler F) q,
      answer F x (IntegralCriticalFlatGridBits.writer F.toParameters .originalGridTerm (pair q (BinaryNatCode.encode i))) =
        IntegralClearedCoefficientBits.maskedProgram (IntegralCriticalFlatGenericGridBits.source F.toParameters (euler F))
          (pair q (BinaryNatCode.encode i)) := by
  intro i hi
  exact (matches_grid F x hm .originalGridTerm (by decide) (pair q (BinaryNatCode.encode i))
    (by simpa only [pairFst_pair] using hv)).trans (IntegralCriticalActualGridTransport.grid_child F q hv i hi)

theorem frozen_replies (F : Scripts) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hm : Matches F x)
    (q : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F q) :
    IntegralCriticalFlatFrozenSumBits.RepliesAt F.toParameters (frozen F) (answer F x) q := by
  intro i hi
  exact (matches_coordinate F x hm .frozenPowerTerm (by decide) (pair q (BinaryNatCode.encode i))
    (by simpa only [pairFst_pair] using hv)).trans (IntegralCriticalActualScalarModels.frozenSum_child_finite F q i hi)

theorem euler_replies (F : Scripts) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hm : Matches F x)
    (q : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F q) :
    ∀ i < (euler F).free q, answer F x (IntegralCriticalFlatEulerRowsBits.sumTask F.toParameters (euler F)
      (pair q (BinaryNatCode.encode i))) = residueBits ((euler F).summand q i : ZMod ((euler F).modulus q)) := by
  intro i hi
  have HM := matches_spatial F x hm .coordinateGradientProduct (by decide) 0
    (IntegralEulerBits.termQuery (euler F) (pair q (BinaryNatCode.encode i))) (by
      simpa only [IntegralEulerBits.termQuery, pairFst_pair] using hv)
  exact HM.trans ((IntegralCriticalActualProductModel.sum_child F q i hi).trans
    (IntegralEulerBits.term_packet (euler F) q ⟨i, hi⟩))

noncomputable def gridMachine (F : Scripts) (h : Controls F) : Machine where
  State := RecursiveFold.State
  defaultValue := default
  encoding := RecursiveFold.encState
  controller := (IntegralCriticalFlatGenericGridBits.program F.toParameters (euler F)).controller
  certificates := IntegralCriticalFlatGenericGridBits.certificates F.toParameters h.task.toAccess (euler F) (eulerAccess F h)
  selected := selected F .clearedGridSum
  selected_FP := selected_FP F h .clearedGridSum
  model := IntegralCriticalActualSpatialTransport.cleared F
  clock := IntegralCriticalFlatGenericGridBits.budget F.toParameters (euler F)
  clock_binary := IntegralCriticalFlatGenericGridBits.budget_binary F.toParameters h.task.toAccess (euler F) (eulerAccess F h)
  stateBound := IntegralCriticalFlatGenericGridBits.stateBound F.toParameters (euler F)
  stateBound_unary := IntegralCriticalFlatGenericGridBits.stateBound_unary F.toParameters h.task.toAccess (euler F) (eulerAccess F h)

theorem grid_correct (F : Scripts) (h : Controls F) (x : (q : List Bool) → ZMod (modulus F.toParameters q))
    (hm : Matches F x) : Correct (gridMachine F h) (answer F x) (Frame F) := by
  constructor
  · intro q _
    exact IntegralCriticalFlatGenericGridBits.halted_after F.toParameters (euler F) (answer F x) q
  · intro q t hq hh
    exact ((IntegralCriticalFlatGenericGridBits.program F.toParameters (euler F)).output_when_halted (answer F x) q t hh).trans
      (IntegralCriticalFlatGenericGridBits.value_at F.toParameters (euler F) (answer F x) q (grid_replies F x hm q ((selected_iff F .clearedGridSum q).mp hq).1))
  · intro q t hq
    have H := IntegralCriticalFlatGenericGridBits.state_length_at F.toParameters (euler F) (answer F x) q
      (grid_replies F x hm q ((selected_iff F .clearedGridSum q).mp hq).1) t
    exact H
  · intro q c budget hq hc
    have HP := ((selected_iff F .clearedGridSum q).mp hq).2
    change phase q = 8 at HP
    have HC := fold_requests_bound (IntegralCriticalFlatGenericGridBits.program F.toParameters (euler F)) (answer F x) budget q c hc
    obtain ⟨i, _, rfl⟩ := (IntegralCriticalFlatGenericGridBits.requests_iff F.toParameters (euler F) (answer F x) q c).mp HC
    simpa only [pairFst_pair] using frame_grid F .originalGridTerm (pair q (BinaryNatCode.encode i)) (by
      simp only [pairFst_pair]
      change 7 < phase q
      omega)

noncomputable def frozenMachine (F : Scripts) (h : Controls F) : Machine where
  State := RecursiveFold.State
  defaultValue := default
  encoding := RecursiveFold.encState
  controller := (IntegralCriticalFlatFrozenSumBits.program F.toParameters (frozen F)).controller
  certificates := IntegralCriticalTotalCreatingBits.FrozenStages.sum_certificates F h
  selected := selected F .frozenPowerSum
  selected_FP := selected_FP F h .frozenPowerSum
  model := IntegralCriticalActualScalarModels.frozenSum F
  clock := fun q => (frozen F).arity q
  clock_binary := BinaryFn.ofUnary (frozenAccess F h).arity
  stateBound := IntegralCriticalFlatFrozenSumBits.stateBound (frozen F)
  stateBound_unary := IntegralCriticalFlatFrozenSumBits.stateBound_unary (frozen F) (frozenAccess F h)

theorem frozen_correct (F : Scripts) (h : Controls F) (x : (q : List Bool) → ZMod (modulus F.toParameters q))
    (hm : Matches F x) : Correct (frozenMachine F h) (answer F x) (Frame F) := by
  constructor
  · intro q _
    exact IntegralCriticalFlatFrozenSumBits.halted_after F.toParameters (frozen F) (answer F x) q
  · intro q t hq hh
    exact (IntegralCriticalFlatFrozenSumBits.output_when_halted_local F.toParameters (frozen F) (answer F x) q
      (frozen_replies F x hm q ((selected_iff F .frozenPowerSum q).mp hq).1) t hh).trans
        (IntegralCriticalActualScalarModels.frozenSum_eq F q).symm
  · intro q t hq
    have H := IntegralCriticalFlatFrozenSumBits.state_length_local F.toParameters (frozen F) (answer F x) q
      (frozen_replies F x hm q ((selected_iff F .frozenPowerSum q).mp hq).1) t
    exact H
  · intro q c budget hq hc
    have HP := ((selected_iff F .frozenPowerSum q).mp hq).2
    change phase q = 10 at HP
    have HC := fold_requests_bound (IntegralCriticalFlatFrozenSumBits.program F.toParameters (frozen F)) (answer F x) budget q c hc
    obtain ⟨i, _, rfl⟩ := (IntegralCriticalFlatFrozenSumBits.requests_iff F.toParameters (frozen F) (answer F x) q c).mp HC
    simpa only [pairFst_pair] using frame_coordinate F .frozenPowerTerm (pair q (BinaryNatCode.encode i)) (by
      simp only [pairFst_pair]
      change 9 < phase q
      omega)

noncomputable def eulerMachine (F : Scripts) (h : Controls F) : Machine where
  State := RecursiveFold.State
  defaultValue := default
  encoding := RecursiveFold.encState
  controller := (IntegralCriticalFlatGenericEulerBits.sumProgram F.toParameters (euler F)).controller
  certificates := IntegralCriticalFlatGenericEulerBits.sum_certificates F.toParameters h.task.toAccess (euler F) (eulerAccess F h)
  selected := selected F .eulerSum
  selected_FP := selected_FP F h .eulerSum
  model := IntegralCriticalActualScalarModels.sum F
  clock := fun q => (euler F).free q
  clock_binary := BinaryFn.ofUnary (eulerAccess F h).free
  stateBound := IntegralCriticalFlatGenericEulerBits.scanStateBound (euler F) (euler F).free
  stateBound_unary := IntegralCriticalFlatGenericEulerBits.sum_stateBound_unary (euler F) (eulerAccess F h)

theorem euler_correct (F : Scripts) (h : Controls F) (x : (q : List Bool) → ZMod (modulus F.toParameters q))
    (hm : Matches F x) : Correct (eulerMachine F h) (answer F x) (Frame F) := by
  constructor
  · intro q _
    exact IntegralCriticalFlatGenericEulerBits.sum_halted_after F.toParameters (euler F) (answer F x) q
  · intro q t hq hh
    exact (IntegralCriticalFlatGenericEulerBits.sum_output_when_halted_at F.toParameters (euler F) (answer F x) q
      (euler_replies F x hm q ((selected_iff F .eulerSum q).mp hq).1) t hh).trans
        (IntegralCriticalActualScalarModels.sum_eq F q).symm
  · intro q t hq
    have H := IntegralCriticalFlatGenericEulerBits.sum_state_length_at F.toParameters (euler F) (answer F x) q
      (euler_replies F x hm q ((selected_iff F .eulerSum q).mp hq).1) t
    rw [show (IntegralCriticalFlatGenericEulerBits.sumProgram F.toParameters (euler F)).initial q =
      (IntegralCriticalFlatGenericEulerBits.sumProgram F.toParameters (euler F)).controller.initial q from rfl] at H
    simpa only [eulerMachine, IntegralCriticalFlatGenericEulerBits.scanStateBound, Turing.MultiTapeTM.encNat_apply,
      Nat.size_eq_bits_len, BinaryNatCode.length_encode] using H
  · intro q c budget hq hc
    have HP := ((selected_iff F .eulerSum q).mp hq).2
    change phase q = 14 at HP
    have HC := fold_requests_bound (IntegralCriticalFlatGenericEulerBits.sumProgram F.toParameters (euler F)) (answer F x) budget q c hc
    obtain ⟨i, _, rfl⟩ := (IntegralCriticalFlatGenericEulerBits.sum_requests_iff F.toParameters (euler F) (answer F x) q c).mp HC
    simpa only [IntegralCriticalFlatEulerRowsBits.sumTask, IntegralEulerBits.termQuery, pairFst_pair] using
      frame_spatial F .coordinateGradientProduct 0 (IntegralEulerBits.termQuery (euler F) (pair q (BinaryNatCode.encode i))) (by
        simp only [IntegralEulerBits.termQuery, pairFst_pair]
        change 13 < phase q
        omega)

end LeanCanny.Algebra.IntegralCriticalNativeLowerFoldBits
