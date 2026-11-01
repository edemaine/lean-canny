/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedPhysicalFactorTransport
public import LeanCanny.Algebra.IntegralMixedPhysicalNativeMonomial
public import LeanCanny.Algebra.IntegralMixedMatrixFrames
/-! # Native powers of actual physical monomial factor matrices -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedPhysicalNativeLowerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralMixedPhysicalCriticalBits IntegralMixedPhysicalQueryBits NativeControllerBranch
set_option backward.isDefEq.respectTransparency false

abbrev FactorRepliesAt (P : Parameters) (F : Family) (reply : List Bool → List Bool) (q : List Bool) : Prop :=
  ∀ (r t : Fin ((IntegralCriticalFlatGenericPowerBits.factorFamily P (monomialSource P F)).dimension q)),
    reply (IntegralCriticalFlatMatrixQuery.writer P .monomialFactor (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))) =
      IntegralMixedPhysicalFactorBits.monomial P F
        (IntegralCriticalFlatMatrixQuery.writer P .monomialFactor (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val))))

theorem factor_replies (P : Parameters) (F : Family) (g : IntegralMixedPhysicalCaps.RootGeometry P F)
    (reply : List Bool → List Bool) (q : List Bool) (he : FactorRepliesAt P F reply q) :
    IntegralCriticalFlatGenericPowerBits.RepliesAt P (IntegralCriticalFlatGenericPowerBits.factorFamily P (monomialSource P F)) .monomialFactor reply q := by
  intro r t
  exact (he r t).trans (IntegralMixedPhysicalFactorBits.factor_replies P F g q r t)

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
    (he : ∀ q, selectedValid P .factorPower q = true → FactorRepliesAt P F reply q) :
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
    have HP := ((selectedValid_iff P .factorPower q).mp hq).2.2
    change phase q = 4 at HP
    obtain ⟨r, t, rfl⟩ := IntegralCriticalFlatGenericPowerBits.requests_in_bounds_local P
      (IntegralCriticalFlatGenericPowerBits.factorAccess P (monomialSource P F) (monomialAccess P a F h)) .monomialFactor reply q
      (factor_replies P F g reply q (he q hq)) budget c hc
    simpa only [pairFst_pair] using IntegralMixedMatrixFrames.matrix_frame P .monomialFactor
      (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))
      (by simp only [pairFst_pair]; change 3 < phase q; omega)
end LeanCanny.Algebra.IntegralMixedPhysicalNativeLowerBits
