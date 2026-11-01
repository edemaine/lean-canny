/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalLayeredTransport
public import LeanCanny.Algebra.IntegralMixedPhysicalNativeFactorPower
public import LeanCanny.Algebra.IntegralMixedPhysicalGridModel
public import LeanCanny.Algebra.IntegralMixedMatrixFrames
/-! # Native full products of actual physical factor matrices -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalNativeLowerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedPhysicalCriticalBits IntegralMixedPhysicalQueryBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

abbrev ProductRepliesAt (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q : List Bool) : Prop :=
  ∀ (r t : Fin ((IntegralCriticalFlatGenericPowerBits.productFamily (monomialSource P F)).dimension q)),
    reply (IntegralCriticalFlatMatrixQuery.writer P .productEntry (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))) =
      IntegralMixedPhysicalLayeredBits.productEntry P F
        (IntegralCriticalFlatMatrixQuery.writer P .productEntry (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val))))

theorem product_replies (P : Parameters) (F : Family) (g : IntegralMixedPhysicalCaps.RootGeometry P F)
    (reply : List Bool → List Bool) (q : List Bool) (he : ProductRepliesAt P F reply q) :
    IntegralCriticalFlatGenericPowerBits.RepliesAt P (IntegralCriticalFlatGenericPowerBits.productFamily (monomialSource P F)) .productEntry reply q := by
  intro r t
  exact (he r t).trans (IntegralMixedPhysicalLayeredBits.product_replies P F g q r t)

noncomputable def productMachine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : Machine where
  State := List Bool
  defaultValue := []
  encoding := Turing.MultiTapeTM.encBits
  controller := IntegralCriticalFlatGenericPowerBits.productController P (monomialSource P F) (monomialAccess P a F h)
  certificates := IntegralCriticalFlatGenericPowerBits.certificates P a
    (IntegralCriticalFlatGenericPowerBits.productAccess (monomialSource P F) (monomialAccess P a F h))
    (IntegralCriticalFlatGenericPowerBits.product_controls (monomialSource P F) (monomialAccess P a F h)) .productEntry
  selected := selectedValid P .productPower
  selected_FP := selectedValid_FP P a .productPower
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
    (he : ∀ q, selectedValid P .productPower q = true → ProductRepliesAt P F reply q) :
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
    have HP := ((selectedValid_iff P .productPower q).mp hq).2.2
    change phase q = 6 at HP
    obtain ⟨r, t, rfl⟩ := IntegralCriticalFlatGenericPowerBits.requests_in_bounds_local P
      (IntegralCriticalFlatGenericPowerBits.productAccess (monomialSource P F) (monomialAccess P a F h)) .productEntry reply q
      (product_replies P F g reply q (he q hq)) budget c hc
    simpa only [pairFst_pair] using IntegralMixedMatrixFrames.matrix_frame P .productEntry
      (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))
      (by simp only [pairFst_pair]; change 5 < phase q; omega)
end LeanCanny.Algebra.IntegralMixedPhysicalNativeLowerBits
