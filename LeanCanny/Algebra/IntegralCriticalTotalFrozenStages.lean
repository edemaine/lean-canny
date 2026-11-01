/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralCriticalFlatFrozenLower
public import LeanCanny.Algebra.IntegralCriticalFlatActualSources
public import LeanCanny.Algebra.IntegralCriticalTotalCreatingLeading
/-! # Native frozen stages from one actual total creating source

The only scalar multiplier is the selected original integer leading
residue, derived from primitive script metadata. Retained heights remain
recursive matrix-entry requests throughout phases 9 through 12.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalTotalCreatingBits.FrozenStages
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM
open IntegralCriticalFlatActualSources
set_option backward.isDefEq.respectTransparency false

noncomputable def source (F : Scripts) := (euler F).toGradient.toFrozen
noncomputable def access (F : Scripts) (h : Controls F) : IntegralFrozenPowerBits.Access (source F) :=
  (eulerAccess F h).toGradient.toFrozen

theorem source_leading (F : Scripts) (q : List Bool) : (source F).leading q = (euler F).leading q := rfl
theorem source_modulus (F : Scripts) (q : List Bool) :
    (source F).modulus q = IntegralCriticalHistoryTask.modulus F.toParameters q := rfl

theorem leading_FP (F : Scripts) (h : Controls F) : (access F h).leading ∈ FP := by
  apply mem_FP_of_eq
    (f := fun q => residueBits ((euler F).leading q : ZMod (IntegralCriticalHistoryTask.modulus F.toParameters q)))
    (g := (access F h).leading) (IntegralCriticalTotalCreatingBits.leading_FP F h.task h.metadata)
  intro q
  rw [(access F h).leading_eq, source_leading, source_modulus]

theorem term_certificates (F : Scripts) (h : Controls F) :
    (IntegralCriticalFlatFrozenTermBits.controller F.toParameters (source F) (access F h)).Certificates
      (encQ := encBits) (encS := RecursiveController.Controller.encChoice SingleCall.encState encBits) :=
  IntegralCriticalFlatFrozenTermBits.certificates F.toParameters h.task.toAccess (source F) (access F h)

theorem term_clock_binary (F : Scripts) (h : Controls F) :
    BinaryFn (IntegralCriticalFlatFrozenTermBits.clock F.toParameters (source F)) :=
  IntegralCriticalFlatFrozenTermBits.clock_binary F.toParameters h.task.toAccess (source F) (access F h)

theorem term_stateBound_unary (F : Scripts) (h : Controls F) :
    UnaryFn (IntegralCriticalFlatFrozenTermBits.stateBound F.toParameters (source F)) :=
  IntegralCriticalFlatFrozenTermBits.stateBound_unary F.toParameters (source F) (access F h)

theorem sum_certificates (F : Scripts) (h : Controls F) :
    (IntegralCriticalFlatFrozenSumBits.program F.toParameters (source F)).controller.Certificates
      (encQ := encBits) (encS := RecursiveFold.encState) :=
  IntegralCriticalFlatFrozenSumBits.certificates F.toParameters h.task.toAccess (source F) (access F h)

theorem constant_certificates (F : Scripts) (h : Controls F) :
    (IntegralCriticalFlatFrozenConstantBits.program F.toParameters (source F) (access F h)).controller.Certificates
      (encQ := encBits) (encS := SingleCall.encState) :=
  IntegralCriticalFlatFrozenConstantBits.certificates F.toParameters h.task.toAccess (source F) (access F h) (leading_FP F h)

theorem lower_certificates (F : Scripts) (h : Controls F) :
    (IntegralCriticalFlatFrozenLowerBits.program F.toParameters (source F)).controller.Certificates
      (encQ := encBits) (encS := RecursiveFold.encState) :=
  IntegralCriticalFlatFrozenLowerBits.certificates F.toParameters h.task.toAccess (source F) (access F h)

end LeanCanny.Algebra.IntegralCriticalTotalCreatingBits.FrozenStages
