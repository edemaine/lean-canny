/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalFlatGenericProductEntry
public import LeanCanny.Algebra.IntegralCriticalFlatGenericMonomial
public import LeanCanny.Algebra.IntegralCriticalTotalFrozenStages
public import LeanCanny.Algebra.IntegralCriticalTotalCreatingDenominator
/-! # Actual total-source adapters for the low flat arithmetic stages -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatActualLow
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM
open IntegralCriticalFlatActualSources
set_option backward.isDefEq.respectTransparency false

noncomputable def source (F : Scripts) :=
  IntegralCriticalFlatGenericGridBits.monomialSource F.toParameters (IntegralCriticalTotalCreatingBits.euler F)
noncomputable def access (F : Scripts) (h : Controls F) : IntegralMonomialTermBits.Access (source F) :=
  IntegralCriticalFlatGenericGridBits.monomialAccess F.toParameters h.task.toAccess
    (IntegralCriticalTotalCreatingBits.euler F) (eulerAccess F h)

theorem source_denominator (F : Scripts) (q : List Bool) :
    (source F).denominator q = (IntegralCriticalTotalCreatingBits.euler F).denominator q := by
  change (IntegralCriticalTotalCreatingBits.euler F).denominator
    (pairFst (IntegralCriticalFlatGridBits.termInput F.toParameters q)) = _
  rw [IntegralCriticalFlatGridBits.termInput_parent]

theorem source_modulus (F : Scripts) (q : List Bool) :
    (source F).modulus q = IntegralCriticalHistoryTask.modulus F.toParameters q := by
  change IntegralCriticalHistoryTask.modulus F.toParameters
    (pairFst (IntegralCriticalFlatGridBits.termInput F.toParameters q)) = _
  rw [IntegralCriticalFlatGridBits.termInput_parent]

theorem denominator_FP (F : Scripts) (h : Controls F) : (access F h).denominator ∈ FP := by
  apply mem_FP_of_eq
    (f := fun q => residueBits ((IntegralCriticalTotalCreatingBits.euler F).denominator q :
      ZMod (IntegralCriticalHistoryTask.modulus F.toParameters q)))
    (g := (access F h).denominator)
    (IntegralCriticalTotalCreatingBits.denominator_FP F h.task h.metadata)
  intro q
  rw [(access F h).denominator_eq, source_denominator, source_modulus]

theorem productEntry_certificates (F : Scripts) (h : Controls F) :
    (IntegralCriticalFlatGenericProductEntryBits.controller F.toParameters (source F)).Certificates
      (encQ := encBits) (encS := SingleCall.encState) :=
  IntegralCriticalFlatGenericProductEntryBits.certificates F.toParameters h.task.toAccess (source F) (access F h)

theorem monomial_certificates (F : Scripts) (h : Controls F) :
    (IntegralCriticalFlatGenericMonomialBits.controller F.toParameters (source F) (access F h)).Certificates
      (encQ := encBits) (encS := SingleCall.encState) :=
  IntegralCriticalFlatGenericMonomialBits.certificates F.toParameters h.task.toAccess (source F) (access F h) (denominator_FP F h)

theorem product_certificates (F : Scripts) (h : Controls F) :
    (IntegralCriticalFlatGenericPowerBits.productController F.toParameters (source F) (access F h)).Certificates
      (encQ := encBits) (encS := encBits) :=
  IntegralCriticalFlatGenericPowerBits.certificates F.toParameters h.task.toAccess
    (IntegralCriticalFlatGenericPowerBits.productAccess (source F) (access F h))
    (IntegralCriticalFlatGenericPowerBits.product_controls (source F) (access F h)) .productEntry

theorem factor_certificates (F : Scripts) (h : Controls F) :
    (IntegralCriticalFlatGenericPowerBits.factorController F.toParameters (source F) (access F h)).Certificates
      (encQ := encBits) (encS := encBits) :=
  IntegralCriticalFlatGenericPowerBits.certificates F.toParameters h.task.toAccess
    (IntegralCriticalFlatGenericPowerBits.factorAccess F.toParameters (source F) (access F h))
    (IntegralCriticalFlatGenericPowerBits.factor_controls F.toParameters h.task.toAccess (source F) (access F h)) .monomialFactor

end LeanCanny.Algebra.IntegralCriticalFlatActualLow
