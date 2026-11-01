/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalNativeLowerFrames
/-! # Native actual factor and monomial product power branches -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalNativeLowerPowerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralCriticalFlatActualSources IntegralCriticalNativeBranchBits IntegralCriticalNativeLowerBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalTotalCreatingBits.atFamily
attribute [local irreducible] IntegralCriticalHistoryTask.get IntegralCriticalHistoryTask.numericCap IntegralCriticalHistoryTask.rank
noncomputable abbrev source (F : Scripts) := IntegralCriticalFlatActualLow.source F
noncomputable abbrev access (F : Scripts) (h : Controls F) := IntegralCriticalFlatActualLow.access F h

theorem factor_replies (F : Scripts) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hm : Matches F x)
    (q : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F q) :
    IntegralCriticalFlatGenericPowerBits.RepliesAt F.toParameters (IntegralCriticalFlatGenericPowerBits.factorFamily F.toParameters (source F)) .monomialFactor (answer F x) q := by
  intro r t
  exact (matches_matrix F x hm .monomialFactor (by decide)
    (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))
    (by simpa only [pairFst_pair] using hv)).trans (IntegralCriticalActualFactorTransport.factor_replies F q r t)

noncomputable def factorMachine (F : Scripts) (h : Controls F) : Machine where
  State := List Bool
  defaultValue := []
  encoding := Turing.MultiTapeTM.encBits
  controller := IntegralCriticalFlatGenericPowerBits.factorController F.toParameters (source F) (access F h)
  certificates := IntegralCriticalFlatActualLow.factor_certificates F h
  selected := selected F .factorPower
  selected_FP := selected_FP F h .factorPower
  model := IntegralCriticalActualFactorModel.power F
  clock := ModularRecursiveStage.clock (IntegralCriticalFlatGenericPowerBits.factorFamily F.toParameters (source F))
  clock_binary := ModularRecursiveStage.clock_binary (IntegralCriticalFlatGenericPowerBits.factorAccess F.toParameters (source F) (access F h)) (IntegralCriticalFlatGenericPowerBits.factor_controls F.toParameters h.task.toAccess (source F) (access F h))
  stateBound := ModularRecursiveStage.stateBound (IntegralCriticalFlatGenericPowerBits.factorFamily F.toParameters (source F))
  stateBound_unary := ModularRecursiveStage.stateBound_unary (IntegralCriticalFlatGenericPowerBits.factorAccess F.toParameters (source F) (access F h)) (IntegralCriticalFlatGenericPowerBits.factor_controls F.toParameters h.task.toAccess (source F) (access F h))

theorem factor_correct (F : Scripts) (h : Controls F) (x : (q : List Bool) → ZMod (modulus F.toParameters q))
    (hm : Matches F x) : Correct (factorMachine F h) (answer F x) (Frame F) := by
  constructor
  · intro q hq
    exact IntegralCriticalFlatGenericPowerBits.halted_after_local F.toParameters (IntegralCriticalFlatGenericPowerBits.factorAccess F.toParameters (source F) (access F h)) .monomialFactor
      (answer F x) q (factor_replies F x hm q ((selected_iff F .factorPower q).mp hq).1)
  · intro q t hq hh
    exact (IntegralCriticalFlatGenericPowerBits.factor_value_local F.toParameters (source F) (access F h)
      (answer F x) q (factor_replies F x hm q ((selected_iff F .factorPower q).mp hq).1) t hh).trans
        (IntegralCriticalActualProductEntryTransport.power_value F q)
  · intro q t hq
    exact IntegralCriticalFlatGenericPowerBits.state_length_local F.toParameters (IntegralCriticalFlatGenericPowerBits.factorAccess F.toParameters (source F) (access F h)) .monomialFactor
      (answer F x) q (factor_replies F x hm q ((selected_iff F .factorPower q).mp hq).1) t
  · intro q c budget hq hc
    have HP := ((selected_iff F .factorPower q).mp hq).2
    change phase q = 4 at HP
    obtain ⟨r, t, rfl⟩ := IntegralCriticalFlatGenericPowerBits.requests_in_bounds_local F.toParameters (IntegralCriticalFlatGenericPowerBits.factorAccess F.toParameters (source F) (access F h))
      .monomialFactor (answer F x) q (factor_replies F x hm q ((selected_iff F .factorPower q).mp hq).1) budget c hc
    simpa only [pairFst_pair] using frame_matrix F .monomialFactor
      (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val))) (by
        simp only [pairFst_pair]
        change 3 < phase q
        omega)

theorem product_replies (F : Scripts) (x : (q : List Bool) → ZMod (modulus F.toParameters q)) (hm : Matches F x)
    (q : List Bool) (hv : IntegralCriticalTotalCompanionBits.valid F q) :
    IntegralCriticalFlatGenericPowerBits.RepliesAt F.toParameters (IntegralCriticalFlatGenericPowerBits.productFamily (source F)) .productEntry (answer F x) q := by
  intro r t
  exact (matches_matrix F x hm .productEntry (by decide)
    (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))
    (by simpa only [pairFst_pair] using hv)).trans (IntegralCriticalActualLowMatrixModel.power_replies F q hv r t)

noncomputable def productMachine (F : Scripts) (h : Controls F) : Machine where
  State := List Bool
  defaultValue := []
  encoding := Turing.MultiTapeTM.encBits
  controller := IntegralCriticalFlatGenericPowerBits.productController F.toParameters (source F) (access F h)
  certificates := IntegralCriticalFlatActualLow.product_certificates F h
  selected := selected F .productPower
  selected_FP := selected_FP F h .productPower
  model := IntegralCriticalActualGridTransport.product F
  clock := ModularRecursiveStage.clock (IntegralCriticalFlatGenericPowerBits.productFamily (source F))
  clock_binary := ModularRecursiveStage.clock_binary (IntegralCriticalFlatGenericPowerBits.productAccess (source F) (access F h)) (IntegralCriticalFlatGenericPowerBits.product_controls (source F) (access F h))
  stateBound := ModularRecursiveStage.stateBound (IntegralCriticalFlatGenericPowerBits.productFamily (source F))
  stateBound_unary := ModularRecursiveStage.stateBound_unary (IntegralCriticalFlatGenericPowerBits.productAccess (source F) (access F h)) (IntegralCriticalFlatGenericPowerBits.product_controls (source F) (access F h))

theorem product_correct (F : Scripts) (h : Controls F) (x : (q : List Bool) → ZMod (modulus F.toParameters q))
    (hm : Matches F x) : Correct (productMachine F h) (answer F x) (Frame F) := by
  constructor
  · intro q hq
    exact IntegralCriticalFlatGenericPowerBits.halted_after_local F.toParameters (IntegralCriticalFlatGenericPowerBits.productAccess (source F) (access F h)) .productEntry
      (answer F x) q (product_replies F x hm q ((selected_iff F .productPower q).mp hq).1)
  · intro q t hq hh
    exact IntegralCriticalFlatGenericPowerBits.product_value_local F.toParameters (source F) (access F h)
      (answer F x) q (product_replies F x hm q ((selected_iff F .productPower q).mp hq).1) t hh
  · intro q t hq
    exact IntegralCriticalFlatGenericPowerBits.state_length_local F.toParameters (IntegralCriticalFlatGenericPowerBits.productAccess (source F) (access F h)) .productEntry
      (answer F x) q (product_replies F x hm q ((selected_iff F .productPower q).mp hq).1) t
  · intro q c budget hq hc
    have HP := ((selected_iff F .productPower q).mp hq).2
    change phase q = 6 at HP
    obtain ⟨r, t, rfl⟩ := IntegralCriticalFlatGenericPowerBits.requests_in_bounds_local F.toParameters (IntegralCriticalFlatGenericPowerBits.productAccess (source F) (access F h))
      .productEntry (answer F x) q (product_replies F x hm q ((selected_iff F .productPower q).mp hq).1) budget c hc
    simpa only [pairFst_pair] using frame_matrix F .productEntry
      (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val))) (by
        simp only [pairFst_pair]
        change 5 < phase q
        omega)

end LeanCanny.Algebra.IntegralCriticalNativeLowerPowerBits
