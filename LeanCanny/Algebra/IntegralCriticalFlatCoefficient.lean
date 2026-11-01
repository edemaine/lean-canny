/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalFlatEuler
public import LeanCanny.Algebra.IntegralCriticalScriptDenominatorFP
public import LeanCanny.Algebra.IntegralCriticalLeadingFP
public import LeanCanny.Algebra.IntegralScaledCharacteristicController

/-! # Flat actual critical coefficients from one relative coefficient

The actual creating polynomial's common leading scalar is computed from
primitive script metadata. One lower-phase relative characteristic request
is followed by binary modular rescaling; no coefficient or height evaluator
is assumed by the local certificate.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatCoefficientBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Controls (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) : Prop extends
    IntegralCriticalScriptEulerBits.Controls F q where
  coordinate : BinaryFn (fun c => ((IntegralCriticalScriptQueryBits.generatorSource F q).coordinate c).val)
  coefficient : BinaryFn q.coefficientIndex

noncomputable def access (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (h : Controls F q) :
    IntegralClearedCriticalBits.Access (IntegralCriticalScriptQueryBits.generatorSource F q) where
  toEuler := IntegralCriticalScriptEulerBits.access F q h.toControls
  bound := PurePowerReductionBounds.bound_binary
    (BinaryFn.ofUnary (IntegralCriticalScriptEulerBits.free_unary F q h.toControls)) h.script.degree
  coordinate := h.coordinate
  coefficientIndex := h.coefficient

noncomputable def relative (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) :=
  IntegralClearedCriticalBits.relativeSource (IntegralCriticalScriptQueryBits.generatorSource F q)

noncomputable def relativeAccess (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (h : Controls F q) :=
  IntegralClearedCriticalBits.relativeAccess _ (access F q h)

noncomputable def characteristic (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) :=
  IntegralReductionActionBits.actionSource (IntegralPurePowerActionBits.reductionSource (relative F q))

noncomputable def characteristicAccess (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (h : Controls F q) :=
  IntegralReductionActionBits.actionAccess _ (IntegralPurePowerReductionBits.reductionAccess (relative F q) (relativeAccess F q h))

theorem scalar_FP (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (h : Controls F q)
    (n : IntegralCriticalScriptFP.Access (IntegralCriticalFlatCompanionBits.metadata F)) :
    (fun c => residueBits ((relative F q).leading c : ZMod (F.modulus c))) ∈ FP := by
  have HQ : (IntegralCriticalScriptEulerBits.access F q h.toControls).denominator ∈ FP :=
    IntegralCriticalScriptDenominatorFP.queried_denominator_FP F q h.script n
  have HA := IntegralCriticalScriptEulerBits.leading_FP F q h.toControls n
  exact IntegralCriticalLeadingBits.value_FP _
    (IntegralCriticalScriptEulerBits.access F q h.toControls).toGradient.toFrozen HQ HA

noncomputable def program (P : IntegralCriticalHistoryTask.Parameters)
    (F : IntegralCriticalScriptGeneratorBits.Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) : SingleCall.Program :=
  IntegralScaledCharacteristicBits.program (characteristic F q) (relative F q).leading
    (fun c => (relative F q).layout.bound c + 1) (IntegralCriticalFlatEulerBits.next P .relativePower)

theorem program_controls (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : IntegralCriticalScriptGeneratorBits.Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (h : Controls F q) (n : IntegralCriticalScriptFP.Access (IntegralCriticalFlatCompanionBits.metadata F)) :
    (program P F q).Controls :=
  IntegralScaledCharacteristicBits.program_controls _ (characteristicAccess F q h) _ _
    ((relativeAccess F q h).bound.add (BinaryFn.const 1)) (scalar_FP F q h n) _
    (IntegralCriticalFlatEulerBits.next_FP P a .relativePower)

theorem program_value (P : IntegralCriticalHistoryTask.Parameters)
    (F : IntegralCriticalScriptGeneratorBits.Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (answer : List Bool → List Bool)
    (ha : ∀ c, answer (IntegralCriticalFlatEulerBits.next P .relativePower c) = (characteristic F q).value c)
    (c : List Bool) : (program P F q).value answer c =
      (IntegralCriticalScriptQueryBits.generatorSource F q).value c := by
  have H := IntegralScaledCharacteristicBits.program_value (characteristic F q) (relative F q).leading
    (fun c => (relative F q).layout.bound c + 1) (IntegralCriticalFlatEulerBits.next P .relativePower) answer ha c
  exact H.trans (congrFun (IntegralPurePowerActionBits.polynomial_value (relative F q)) c)

theorem requests_rank (P : IntegralCriticalHistoryTask.Parameters)
    (F : IntegralCriticalScriptGeneratorBits.Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (answer : List Bool → List Bool) (budget : List Bool → ℕ) (c child : List Bool)
    (hp : IntegralCriticalHistoryTask.isPhase .criticalCoefficient c)
    (hc : (program P F q).controller.Requests answer budget c child) :
    IntegralCriticalHistoryTask.rank P child < IntegralCriticalHistoryTask.rank P c := by
  have HE := (IntegralScaledCharacteristicBits.program_requests_iff _ _ _ _ answer budget c child).mp hc
  rw [HE]
  exact IntegralCriticalFlatEulerBits.next_lower_rank P .relativePower c (by change 24 < IntegralCriticalHistoryTask.phase c; change IntegralCriticalHistoryTask.phase c = 25 at hp; omega)

end LeanCanny.Algebra.IntegralCriticalFlatCoefficientBits
