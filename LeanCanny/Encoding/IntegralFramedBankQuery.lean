/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.IntegralFramedBankUnivariateTest

/-! # Actual bank-query data and original native controls

This bundle permits comparisons between different framed scripts. Its access
certificate contains native current-Q controls and original metadata; no bank
coordinate, polynomial-test or integer coefficient evaluator is a field.
-/
@[expose] public section
namespace LeanCanny.Encoding.IntegralFramedBankQuery
open LeanCanny.Algebra LeanCanny.Computation IntegralCriticalHistoryTask
open IntegralMixedFramedHistoryFamilyBits (Plan)
open IntegralMixedFramedCompanionUniformBits (lifted liftedPlan)
open IntegralMixedFramedBankSnapshotBits (atKey)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

structure Bank where
  parameters : Parameters
  plan : Plan parameters
  data : IntegralMixedFramedHistoryFamilyBits.Data parameters plan
  nodes : List Bool→ℕ
  factor : List Bool→ℕ
  seed : List Bool→ℕ
  bounds : IntegralMixedFramedStepHeight.FamilyInputs parameters plan nodes factor seed
  key : List Bool→List Bool
  positive : ∀ c,0<(atKey parameters plan data (key c)).count
  coordinate : (c : List Bool)→Fin (atKey parameters plan data (key c)).count

structure Access (B : Bank) where
  parameters : IntegralCriticalHistoryTask.Access B.parameters
  liftedData : IntegralMixedFramedHistoryFamilyBits.Data (lifted B.parameters) (liftedPlan B.parameters B.plan)
  controls : IntegralMixedFramedCurrentQNativeBits.Controls (lifted B.parameters) (liftedPlan B.parameters B.plan) liftedData
  bounds : IntegralMixedFramedCurrentQNativeBits.Bounds (lifted B.parameters) (liftedPlan B.parameters B.plan) liftedData controls
  nodes : BinaryFn B.nodes
  factor : BinaryFn B.factor
  seed : BinaryFn B.seed
  key : B.key∈FP
  coordinate : UnaryFn (fun c=>(B.coordinate c).val)

noncomputable abbrev input (B : Bank) :=
  IntegralFramedBankUnivariateTest.input B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds B.key B.positive

theorem input_access (B : Bank) (h : Access B) : (input B).Access :=
  IntegralFramedCurrentQSquare.access_native B.parameters h.parameters B.plan B.data h.liftedData h.controls h.bounds
    B.nodes B.factor B.seed B.bounds h.nodes h.factor h.seed B.key h.key B.positive

noncomputable def value (B : Bank) (Q : IntegerPolynomialRootQueriesBits.Source) :=
  IntegralFramedBankUnivariateTest.value B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds B.key B.positive
    (fun c _=>B.coordinate c) Q

theorem evaluator (B : Bank) (h : Access B) (Q : IntegerPolynomialRootQueriesBits.Source)
    (hQ : IntegerPolynomialRootQueriesBits.Access Q) : SpaceFunction (value B Q) :=
  IntegralFramedBankUnivariateTest.evaluator B.parameters h.parameters B.plan B.data h.liftedData h.controls h.bounds
    h.nodes h.factor h.seed B.bounds B.key h.key B.positive (fun c _=>B.coordinate c)
    (h.coordinate.comp pairFst_mem_FP) Q hQ

noncomputable def point (B : Bank) (c w : List Bool) (hw : SquareSampleCompleteVertices.Valid (input B) c w) : ℝ :=
  LeanCanny.Geometry.IntegralMixedCanonicalBankPoint.point
    (LeanCanny.Geometry.IntegralMixedFramedBankTermSign.state B.parameters B.plan B.data (B.key c))
    (SquareSampleCompleteVertices.candidate (input B) c w hw).val (B.coordinate c)

theorem packet (B : Bank) (Q : IntegerPolynomialRootQueriesBits.Source) (c w d : List Bool)
    (hw : SquareSampleCompleteVertices.Valid (input B) c w) :
    value B Q (pair (pair c w) d)=InfinitesimalSign.encode
      (SignType.sign ((Q.polynomial (pair c d)).eval₂ (Int.castRingHom ℝ) (point B c w hw))) :=
  IntegralFramedBankUnivariateTest.packet B.parameters B.plan B.data B.nodes B.factor B.seed B.bounds B.key B.positive
    (fun c _=>B.coordinate c) Q c w d hw

end LeanCanny.Encoding.IntegralFramedBankQuery
