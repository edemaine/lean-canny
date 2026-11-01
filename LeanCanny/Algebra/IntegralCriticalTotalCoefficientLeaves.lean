/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalFlatDerivative
public import LeanCanny.Algebra.IntegralCriticalTotalCreatingAccess

/-! # Actual integer and spatial derivative leaves of total creating sources

The polynomial at phase 0 is the selected original integer polynomial,
mapped into its exact old algebra. Phase 1 uses the selected spatial
derivative of that same polynomial. These adapters supply the structural
source identities rather than asking for algebraic coefficient readers.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalTotalCreatingBits.CoefficientLeaves
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralCriticalTotalCompanionBits
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] atFamily

noncomputable def original (F : Scripts) := IntegralCriticalFlatGridSourceBits.original (euler F)

noncomputable def integer (F : Scripts) (q : List Bool) : MvPolynomial (Fin ((original F).arity q)) ℤ :=
  ((atFamily F q).data []).low

theorem mapped (F : Scripts) (q : List Bool) :
    letI := (original F).ring q
    (original F).polynomial q = (integer F q).map (Int.castRingHom ((original F).carrier q)) := rfl

noncomputable def originalValue (F : Scripts) (scalar : List Bool → List Bool) :=
  IntegralCriticalFlatOriginalCoefficientBits.value F.toParameters (original F) scalar

theorem originalValue_FP (F : Scripts) (a : Access F)
    (n : IntegralCriticalScriptFP.Access (IntegralCriticalFlatClearedHeightBits.metadata F))
    (ho : BinaryFn (commandObjective F)) (scalar : List Bool → List Bool) (hs : scalar ∈ FP) :
    originalValue F scalar ∈ FP :=
  IntegralCriticalFlatOriginalCoefficientBits.value_FP F.toParameters a.toAccess (original F)
    (IntegralCriticalTotalCreatingBits.access F a n ho).toGradient.toFrozen.toAccess scalar hs

theorem originalValue_space (F : Scripts) (a : Access F)
    (n : IntegralCriticalScriptFP.Access (IntegralCriticalFlatClearedHeightBits.metadata F))
    (ho : BinaryFn (commandObjective F)) (scalar : List Bool → List Bool) (hs : SpaceFunction scalar) :
    SpaceFunction (originalValue F scalar) :=
  IntegralCriticalFlatOriginalCoefficientBits.value_space F.toParameters a.toAccess (original F)
    (IntegralCriticalTotalCreatingBits.access F a n ho).toGradient.toFrozen.toAccess scalar hs

theorem originalValue_actual (F : Scripts) (scalar : List Bool → List Bool)
    (hs : ∀ q k, scalar (pair q (BinaryNatCode.encode k)) = residueBits
      (IntegralCriticalFlatOriginalCoefficientBits.coefficient (original F) (integer F) q k : ZMod ((original F).modulus q)))
    (q : List Bool) :
    letI := (original F).ring q
    originalValue F scalar q = residueBits ((Algebra.leftMulMatrix ((original F).basis q)
      (((original F).polynomial q).coeff (RationalSubstitution.Indexed.exponentVector ((original F).arity q)
        (FixedWidthPolynomial.entry ((original F).sourceWidth q) (IntegralCriticalHistoryTask.get F.toParameters .sourceIndex q))))
      (IntegralCriticalFlatOriginalCoefficientBits.index F.toParameters (original F) .row q)
      (IntegralCriticalFlatOriginalCoefficientBits.index F.toParameters (original F) .col q) : ℤ) : ZMod ((original F).modulus q)) :=
  IntegralCriticalFlatOriginalCoefficientBits.actual_value F.toParameters (original F) (integer F) (mapped F) scalar hs q

noncomputable def derivative (F : Scripts) :=
  IntegralCriticalFlatDerivativeBits.eulerSource F.toParameters (euler F)

noncomputable def derivativeAccess (F : Scripts) (a : Access F)
    (n : IntegralCriticalScriptFP.Access (IntegralCriticalFlatClearedHeightBits.metadata F))
    (ho : BinaryFn (commandObjective F)) : IntegralDerivativeBits.Access (derivative F) :=
  IntegralCriticalFlatDerivativeBits.eulerAccess F.toParameters a.toAccess (euler F)
    (IntegralCriticalTotalCreatingBits.access F a n ho)

theorem derivative_certificates (F : Scripts) (a : Access F)
    (n : IntegralCriticalScriptFP.Access (IntegralCriticalFlatClearedHeightBits.metadata F))
    (ho : BinaryFn (commandObjective F)) :
    (IntegralCriticalFlatDerivativeBits.controller F.toParameters (derivative F)).Certificates
      (encQ := Turing.MultiTapeTM.encBits) (encS := SingleCall.encState) :=
  IntegralCriticalFlatDerivativeBits.certificates F.toParameters a.toAccess (derivative F) (derivativeAccess F a n ho)

end LeanCanny.Algebra.IntegralCriticalTotalCreatingBits.CoefficientLeaves
