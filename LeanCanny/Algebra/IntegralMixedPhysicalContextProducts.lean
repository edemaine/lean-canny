/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalContextLeaves
public import LeanCanny.Algebra.IntegralMixedPhysicalNativeGrid
public import LeanCanny.Algebra.IntegralMixedPhysicalNativeProductEntry
/-! # Context-restricted physical product and cleared-grid machines

Every reply obligation is at one current selected physical task and its
finite actual requests. Virtual contexts require no physical value matches.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalContextBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedPhysicalCriticalBits IntegralMixedPhysicalQueryBits NativeControllerBranch
open IntegralMixedPhysicalNativeLowerBits
set_option backward.isDefEq.respectTransparency false

noncomputable def factorMachine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : Machine where
  State := List Bool
  defaultValue := []
  encoding := Turing.MultiTapeTM.encBits
  controller := IntegralCriticalFlatGenericPowerBits.factorController P (monomialSource P F) (monomialAccess P a F h)
  certificates := IntegralCriticalFlatGenericPowerBits.certificates P a
    (IntegralCriticalFlatGenericPowerBits.factorAccess P (monomialSource P F) (monomialAccess P a F h))
    (IntegralCriticalFlatGenericPowerBits.factor_controls P a (monomialSource P F) (monomialAccess P a F h)) .monomialFactor
  selected := selected P .factorPower
  selected_FP := selected_FP P a .factorPower
  model := IntegralMixedPhysicalFactorBits.power P F
  clock := ModularRecursiveStage.clock (IntegralCriticalFlatGenericPowerBits.factorFamily P (monomialSource P F))
  clock_binary := ModularRecursiveStage.clock_binary
    (IntegralCriticalFlatGenericPowerBits.factorAccess P (monomialSource P F) (monomialAccess P a F h))
    (IntegralCriticalFlatGenericPowerBits.factor_controls P a (monomialSource P F) (monomialAccess P a F h))
  stateBound := ModularRecursiveStage.stateBound (IntegralCriticalFlatGenericPowerBits.factorFamily P (monomialSource P F))
  stateBound_unary := ModularRecursiveStage.stateBound_unary
    (IntegralCriticalFlatGenericPowerBits.factorAccess P (monomialSource P F) (monomialAccess P a F h))
    (IntegralCriticalFlatGenericPowerBits.factor_controls P a (monomialSource P F) (monomialAccess P a F h))

theorem factor_correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (g : IntegralMixedPhysicalCaps.RootGeometry P F) (reply : List Bool → List Bool)
    (he : ∀ q, selected P .factorPower q = true → FactorRepliesAt P F reply q) :
    Correct (factorMachine P a F h) reply (IntegralMixedRoutineTaskBits.Frame P) := by
  constructor
  · intro q hq
    exact IntegralCriticalFlatGenericPowerBits.halted_after_local P
      (IntegralCriticalFlatGenericPowerBits.factorAccess P (monomialSource P F) (monomialAccess P a F h)) .monomialFactor reply q
      (factor_replies P F g reply q (he q hq))
  · intro q t hq hh
    exact (IntegralCriticalFlatGenericPowerBits.factor_value_local P (monomialSource P F) (monomialAccess P a F h) reply q
      (factor_replies P F g reply q (he q hq)) t hh).trans
        (IntegralMixedPhysicalFactorBits.power_value P F q)
  · intro q t hq
    exact IntegralCriticalFlatGenericPowerBits.state_length_local P
      (IntegralCriticalFlatGenericPowerBits.factorAccess P (monomialSource P F) (monomialAccess P a F h)) .monomialFactor reply q
      (factor_replies P F g reply q (he q hq)) t
  · intro q c budget hq hc
    have HP := ((IntegralMixedPhysicalNativeLowerBits.selectedValid_iff P .factorPower q).mp (selected_raw P .factorPower q hq)).2.2
    change phase q = 4 at HP
    obtain ⟨r, t, rfl⟩ := IntegralCriticalFlatGenericPowerBits.requests_in_bounds_local P
      (IntegralCriticalFlatGenericPowerBits.factorAccess P (monomialSource P F) (monomialAccess P a F h)) .monomialFactor reply q
      (factor_replies P F g reply q (he q hq)) budget c hc
    simpa only [pairFst_pair] using IntegralMixedMatrixFrames.matrix_frame P .monomialFactor
      (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))
      (by simp only [pairFst_pair]; change 3 < phase q; omega)

noncomputable def productEntryMachine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : Machine :=
  ofPreparedSingleCall (productEntryProgram P F)
    ((productEntryProgram P F).certificates (IntegralCriticalFlatGenericProductEntryBits.controls P a (monomialSource P F) (monomialAccess P a F h)))
    (productEntryInput P F) (IntegralCriticalFlatGenericProductEntryBits.input_FP P a (monomialSource P F) (monomialAccess P a F h))
    (selected P .productEntry) (selected_FP P a .productEntry)
    (IntegralMixedPhysicalLayeredBits.productEntry P F) (replyBound P) (replyBound_unary P a)

theorem productEntry_correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (g : IntegralMixedPhysicalCaps.RootGeometry P F) (reply : List Bool → List Bool)
    (he : ∀ q, selected P .productEntry q = true → ProductEntryRepliesAt P F reply q) :
    Correct (productEntryMachine P a F h) reply (IntegralMixedRoutineTaskBits.Frame P) := by
  apply ofPreparedSingleCall_correct
  · intro q hq
    exact productEntry_value_at P a F h g reply q (he q hq)
  · intro q hq hr
    have HV := productEntry_value_at P a F h g reply q (he q hq)
    simp only [SingleCall.Program.value, hr, ite_true] at HV
    change pairSnd (pair _ _) = _ at HV
    rw [pairSnd_pair] at HV
    change (reply ((productEntryProgram P F).query (productEntryInput P F q))).length ≤ replyBound P q
    rw [HV]
    obtain ⟨z, hz⟩ := IntegralMixedPhysicalCanonicalBits.productEntry_canonical P F q
    rw [← hz]
    let : NeZero (modulus P q) := ⟨modulus_ne_zero P q⟩
    exact residueBits_length_le _ _
  · intro q c budget hq hc
    exact productEntry_requests_frame P (monomialSource P F) reply budget q c
      ((IntegralMixedPhysicalNativeLowerBits.selectedValid_iff P .productEntry q).mp (selected_raw P .productEntry q hq)).2.2 hc

noncomputable def productMachine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : Machine where
  State := List Bool
  defaultValue := []
  encoding := Turing.MultiTapeTM.encBits
  controller := IntegralCriticalFlatGenericPowerBits.productController P (monomialSource P F) (monomialAccess P a F h)
  certificates := IntegralCriticalFlatGenericPowerBits.certificates P a
    (IntegralCriticalFlatGenericPowerBits.productAccess (monomialSource P F) (monomialAccess P a F h))
    (IntegralCriticalFlatGenericPowerBits.product_controls (monomialSource P F) (monomialAccess P a F h)) .productEntry
  selected := selected P .productPower
  selected_FP := selected_FP P a .productPower
  model := IntegralMixedPhysicalGridBits.product P F
  clock := ModularRecursiveStage.clock (IntegralCriticalFlatGenericPowerBits.productFamily (monomialSource P F))
  clock_binary := ModularRecursiveStage.clock_binary
    (IntegralCriticalFlatGenericPowerBits.productAccess (monomialSource P F) (monomialAccess P a F h))
    (IntegralCriticalFlatGenericPowerBits.product_controls (monomialSource P F) (monomialAccess P a F h))
  stateBound := ModularRecursiveStage.stateBound (IntegralCriticalFlatGenericPowerBits.productFamily (monomialSource P F))
  stateBound_unary := ModularRecursiveStage.stateBound_unary
    (IntegralCriticalFlatGenericPowerBits.productAccess (monomialSource P F) (monomialAccess P a F h))
    (IntegralCriticalFlatGenericPowerBits.product_controls (monomialSource P F) (monomialAccess P a F h))

theorem product_correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (g : IntegralMixedPhysicalCaps.RootGeometry P F) (reply : List Bool → List Bool)
    (he : ∀ q, selected P .productPower q = true → ProductRepliesAt P F reply q) :
    Correct (productMachine P a F h) reply (IntegralMixedRoutineTaskBits.Frame P) := by
  constructor
  · intro q hq
    exact IntegralCriticalFlatGenericPowerBits.halted_after_local P
      (IntegralCriticalFlatGenericPowerBits.productAccess (monomialSource P F) (monomialAccess P a F h)) .productEntry reply q
      (product_replies P F g reply q (he q hq))
  · intro q t hq hh
    exact (IntegralCriticalFlatGenericPowerBits.product_value_local P (monomialSource P F) (monomialAccess P a F h) reply q
      (product_replies P F g reply q (he q hq)) t hh)
  · intro q t hq
    exact IntegralCriticalFlatGenericPowerBits.state_length_local P
      (IntegralCriticalFlatGenericPowerBits.productAccess (monomialSource P F) (monomialAccess P a F h)) .productEntry reply q
      (product_replies P F g reply q (he q hq)) t
  · intro q c budget hq hc
    have HP := ((IntegralMixedPhysicalNativeLowerBits.selectedValid_iff P .productPower q).mp (selected_raw P .productPower q hq)).2.2
    change phase q = 6 at HP
    obtain ⟨r, t, rfl⟩ := IntegralCriticalFlatGenericPowerBits.requests_in_bounds_local P
      (IntegralCriticalFlatGenericPowerBits.productAccess (monomialSource P F) (monomialAccess P a F h)) .productEntry reply q
      (product_replies P F g reply q (he q hq)) budget c hc
    simpa only [pairFst_pair] using IntegralMixedMatrixFrames.matrix_frame P .productEntry
      (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))
      (by simp only [pairFst_pair]; change 5 < phase q; omega)

noncomputable def gridTermMachine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : Machine :=
  ofPreparedSingleCall (gridTermProgram P F)
    ((gridTermProgram P F).certificates (IntegralCriticalFlatGenericGridBits.term_controls P a (source P F) (sourceAccess P a F h)))
    (gridTermInput P) (IntegralCriticalFlatGridBits.termInput_FP P a)
    (selected P .originalGridTerm) (selected_FP P a .originalGridTerm)
    (IntegralMixedPhysicalGridBits.term P F) (replyBound P) (replyBound_unary P a)

theorem gridTerm_correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (reply : List Bool → List Bool) (he : ∀ q, selected P .originalGridTerm q = true → GridTermRepliesAt P F reply q) :
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
    exact gridTerm_requests_frame P (source P F) reply budget q c ((IntegralMixedPhysicalNativeLowerBits.selectedValid_iff P .originalGridTerm q).mp (selected_raw P .originalGridTerm q hq)).2.2 hc

noncomputable def gridMachine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : Machine where
  State := RecursiveFold.State
  defaultValue := default
  encoding := RecursiveFold.encState
  controller := (gridProgram P F).controller
  certificates := IntegralCriticalFlatGenericGridBits.certificates P a (source P F) (sourceAccess P a F h)
  selected := selected P .clearedGridSum
  selected_FP := selected_FP P a .clearedGridSum
  model := IntegralMixedPhysicalSpatialBits.cleared P F
  clock := gridBudget P F
  clock_binary := IntegralCriticalFlatGenericGridBits.budget_binary P a (source P F) (sourceAccess P a F h)
  stateBound := IntegralCriticalFlatGenericGridBits.stateBound P (source P F)
  stateBound_unary := IntegralCriticalFlatGenericGridBits.stateBound_unary P a (source P F) (sourceAccess P a F h)

theorem grid_correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (g : IntegralMixedPhysicalCaps.RootGeometry P F) (reply : List Bool → List Bool)
    (he : ∀ q, selected P .clearedGridSum q = true → GridRepliesAt P F reply q) :
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
    have HP := ((IntegralMixedPhysicalNativeLowerBits.selectedValid_iff P .clearedGridSum q).mp (selected_raw P .clearedGridSum q hq)).2.2
    have HC := IntegralCriticalNativeLowerBits.fold_requests_bound (gridProgram P F) reply budget q c hc
    obtain ⟨k, _, rfl⟩ := (IntegralCriticalFlatGenericGridBits.requests_iff P (source P F) reply q c).mp HC
    simpa only [pairFst_pair] using frame_grid P .originalGridTerm (pair q (BinaryNatCode.encode k))
      (by simp only [pairFst_pair]; change phase q = 8 at HP; change 7 < phase q; omega)

end LeanCanny.Algebra.IntegralMixedPhysicalContextBits
