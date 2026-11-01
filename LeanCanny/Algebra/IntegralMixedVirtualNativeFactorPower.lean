/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedVirtualFactorTransport
public import LeanCanny.Algebra.IntegralMixedVirtualNativeValidBranch
public import LeanCanny.Algebra.IntegralMixedMatrixFrames
/-! # Native powers of actual virtual monomial factor matrices -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedVirtualNativeLowerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedCutSource IntegralMixedVirtualQueryBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

noncomputable abbrev monomialSource (P : Parameters) (F : Family) := IntegralMixedVirtualMonomialBits.source P F
noncomputable abbrev monomialAccess (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) := IntegralMixedVirtualMonomialBits.access P a F h

abbrev FactorRepliesAt (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q : List Bool) : Prop :=
  ∀ (r t : Fin ((IntegralCriticalFlatGenericPowerBits.factorFamily P (monomialSource P F)).dimension q)),
    reply (IntegralCriticalFlatMatrixQuery.writer P .monomialFactor (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))) =
      IntegralMixedVirtualFactorBits.monomial P F
        (IntegralCriticalFlatMatrixQuery.writer P .monomialFactor (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val))))

theorem factor_replies (P : Parameters) (F : Family) (g : IntegralMixedVirtualCaps.RootGeometry P F)
    (reply : List Bool → List Bool) (q : List Bool) (hv : IntegralMixedVirtualCaps.valid P q) (he : FactorRepliesAt P F reply q) :
    IntegralCriticalFlatGenericPowerBits.RepliesAt P (IntegralCriticalFlatGenericPowerBits.factorFamily P (monomialSource P F)) .monomialFactor reply q := by
  intro r t
  exact (he r t).trans (IntegralMixedVirtualFactorBits.factor_replies P F g q hv r t)

noncomputable def factorMachine (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F) : Machine where
  State := List Bool
  defaultValue := []
  encoding := Turing.MultiTapeTM.encBits
  controller := IntegralCriticalFlatGenericPowerBits.factorController P (monomialSource P F) (monomialAccess P a F h)
  certificates := IntegralCriticalFlatGenericPowerBits.certificates P a
    (IntegralCriticalFlatGenericPowerBits.factorAccess P (monomialSource P F) (monomialAccess P a F h))
    (IntegralCriticalFlatGenericPowerBits.factor_controls P a (monomialSource P F) (monomialAccess P a F h)) .monomialFactor
  selected := selectedValid P .factorPower
  selected_FP := selectedValid_FP P a .factorPower
  model := IntegralMixedVirtualFactorBits.power P F
  clock := ModularRecursiveStage.clock (IntegralCriticalFlatGenericPowerBits.factorFamily P (monomialSource P F))
  clock_binary := ModularRecursiveStage.clock_binary
    (IntegralCriticalFlatGenericPowerBits.factorAccess P (monomialSource P F) (monomialAccess P a F h))
    (IntegralCriticalFlatGenericPowerBits.factor_controls P a (monomialSource P F) (monomialAccess P a F h))
  stateBound := ModularRecursiveStage.stateBound (IntegralCriticalFlatGenericPowerBits.factorFamily P (monomialSource P F))
  stateBound_unary := ModularRecursiveStage.stateBound_unary
    (IntegralCriticalFlatGenericPowerBits.factorAccess P (monomialSource P F) (monomialAccess P a F h))
    (IntegralCriticalFlatGenericPowerBits.factor_controls P a (monomialSource P F) (monomialAccess P a F h))

theorem factor_correct (P : Parameters) (a : Access P) (F : Family) (h : InputMetadata F)
    (g : IntegralMixedVirtualCaps.RootGeometry P F) (reply : List Bool → List Bool)
    (he : ∀ q, selectedValid P .factorPower q = true → FactorRepliesAt P F reply q) :
    Correct (factorMachine P a F h) reply (IntegralMixedRoutineTaskBits.Frame P) := by
  constructor
  · intro q hq
    exact IntegralCriticalFlatGenericPowerBits.halted_after_local P
      (IntegralCriticalFlatGenericPowerBits.factorAccess P (monomialSource P F) (monomialAccess P a F h)) .monomialFactor reply q
      (factor_replies P F g reply q ((selectedValid_iff P .factorPower q).mp hq).1 (he q hq))
  · intro q t hq hh
    exact (IntegralCriticalFlatGenericPowerBits.factor_value_local P (monomialSource P F) (monomialAccess P a F h) reply q
      (factor_replies P F g reply q ((selectedValid_iff P .factorPower q).mp hq).1 (he q hq)) t hh).trans
        (IntegralMixedVirtualFactorBits.power_value P F q)
  · intro q t hq
    exact IntegralCriticalFlatGenericPowerBits.state_length_local P
      (IntegralCriticalFlatGenericPowerBits.factorAccess P (monomialSource P F) (monomialAccess P a F h)) .monomialFactor reply q
      (factor_replies P F g reply q ((selectedValid_iff P .factorPower q).mp hq).1 (he q hq)) t
  · intro q c budget hq hc
    have HP := ((selectedValid_iff P .factorPower q).mp hq).2.2
    change phase q = 4 at HP
    obtain ⟨r, t, rfl⟩ := IntegralCriticalFlatGenericPowerBits.requests_in_bounds_local P
      (IntegralCriticalFlatGenericPowerBits.factorAccess P (monomialSource P F) (monomialAccess P a F h)) .monomialFactor reply q
      (factor_replies P F g reply q ((selectedValid_iff P .factorPower q).mp hq).1 (he q hq)) budget c hc
    simpa only [pairFst_pair] using IntegralMixedMatrixFrames.matrix_frame P .monomialFactor
      (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))
      (by simp only [pairFst_pair]; change 3 < phase q; omega)
end LeanCanny.Algebra.IntegralMixedVirtualNativeLowerBits
