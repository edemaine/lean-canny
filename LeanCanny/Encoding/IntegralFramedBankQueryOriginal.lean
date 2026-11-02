/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedBankQuery
public import LeanCanny.Algebra.IntegralMixedFramedCurrentQFromOriginal

/-! # Original syntax supplies the same actual bank-query interface

Literal original slopes use the current-Q controller's original mode. The
source, saved key, bank and all complete-candidate semantics stay unchanged.
The original controller's own normalization budget remains explicit.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedBankQueryOriginal
open LeanCanny.Algebra LeanCanny.Computation
open IntegralFramedBankQuery (Bank)
open IntegralMixedFramedCompanionUniformBits (lifted liftedPlan lifted_access)

noncomputable def access (B : Bank) (a : IntegralCriticalHistoryTask.Access B.parameters)
    (Hnew : IntegralMixedFramedHistoryFamilyBits.Data (lifted B.parameters) (liftedPlan B.parameters B.plan))
    (s : IntegralMixedFramedNativeBits.Syntax (lifted B.parameters) (liftedPlan B.parameters B.plan) Hnew)
    (hb : IntegralMixedFramedNativeBits.Bounds (lifted B.parameters) (liftedPlan B.parameters B.plan) Hnew
      (IntegralMixedFramedNativeBits.Controls.ofSyntax (lifted B.parameters) (lifted_access B.parameters a)
        (liftedPlan B.parameters B.plan) Hnew s))
    (hL : BinaryFn B.nodes) (hF : BinaryFn B.factor) (hC : BinaryFn B.seed)
    (hk : B.key∈FP) (hi : UnaryFn (fun c=>(B.coordinate c).val)) : IntegralFramedBankQuery.Access B where
  parameters:=a
  liftedData:=Hnew
  controls:=IntegralMixedFramedCurrentQFromOriginal.ofSyntax (lifted B.parameters) (lifted_access B.parameters a)
    (liftedPlan B.parameters B.plan) Hnew s
  bounds:=IntegralMixedFramedCurrentQFromOriginal.syntax_bounds (lifted B.parameters) (lifted_access B.parameters a)
    (liftedPlan B.parameters B.plan) Hnew s hb
  nodes:=hL
  factor:=hF
  seed:=hC
  key:=hk
  coordinate:=hi

end LeanCanny.Encoding.IntegralFramedBankQueryOriginal
