import LeanCanny.Encoding.FormulaSignSlotRadialJointStratumSampler
import Lean.Util.CollectAxioms

open LeanCanny LeanCanny.Algebra LeanCanny.Computation LeanCanny.Encoding LeanCanny.Geometry
open CoerciveComponentSampling
open scoped Classical

namespace ImplicitStratumSamplerRegression
local notation "S" => FormulaSignSlotRadialJointStratum.source
local notation "A" => FormulaSignSlotRadialJointStratumNative.access
local notation "hp" => FormulaSignSlotRadialJointStratumSampler.positive

-- The actual source has a closed native sampler certificate.
example : (ImplicitSourceGramGrid.input S hp).Access := ImplicitSourceGramGrid.access S A hp
example : FormulaSignSlotRadialJointStratumSampler.language ∈ Cslib.Complexity.PSPACE Turing.MultiTapeTM.encBits :=
  FormulaSignSlotRadialJointStratumSampler.mem_PSPACE
example : UnaryFn FormulaSignSlotRadialJointStratumSampler.tableBound :=
  FormulaSignSlotRadialJointStratumSampler.tableBound_unary
example : UnaryFn FormulaSignSlotRadialJointStratumSampler.ownwordBound :=
  FormulaSignSlotRadialJointStratumSampler.ownwordBound_unary

-- No validity assumption on the coefficient-witness table supplies nonzeroness.
example (c : List Bool) (i : Fin (ImplicitSourceGramGrid.count S c)) :
    ImplicitSourceGramGrid.polynomial S c i ≠ 0 := ImplicitSourceGramGrid.nonzero S c i

-- Acceptance pins the exact zero-feature count at the SAME decoded point.
example (c w : List Bool)
    (hw : SquareSampleCompleteVertices.Valid FormulaSignSlotRadialJointStratumSampler.input c w)
    (hq : pair c w ∈ FormulaSignSlotRadialJointStratumSampler.language) :
    SquareFeatureProduct.zeroCount
      (FormulaSignSlotRadialJointStratum.values (ImplicitSourceGramGrid.header c)
        (SquareSampleCompleteVertices.candidate FormulaSignSlotRadialJointStratumSampler.input c w hw).val) =
      FormulaSignSlotRadialJointStratum.selected (ImplicitSourceGramGrid.header c) := by
  apply (SquareFeatureProduct.exists_certificate_iff _ _).mp
  exact ⟨_, ((FormulaSignSlotRadialJointStratumSampler.accepted_iff c w hw).mp hq).2⟩

-- Completeness uses no supplied finite system, native reader or association.
example (u : List Bool) :
    Nonempty (Zeros (((S).polynomial u).map (Int.castRingHom ℝ))) ↔
      ∃ Gamma : List Bool, Gamma.length ≤ FormulaSignSlotRadialJointStratumSampler.tableBound u ∧
        ∃ w : List Bool, w.length ≤ FormulaSignSlotRadialJointStratumSampler.ownwordBound u ∧
          pair (pair u Gamma) w ∈ FormulaSignSlotRadialJointStratumSampler.language :=
  FormulaSignSlotRadialJointStratumSampler.nonempty_iff u

end ImplicitStratumSamplerRegression

open Lean in
run_cmd do
  let names := #[
    `LeanCanny.Geometry.CoerciveGramComponentGrid.joined_sample,
    `LeanCanny.Geometry.CoerciveGramWitnessGrid.joined_sample,
    `LeanCanny.Encoding.FormulaSignSlotRadialJointStratumNative.access,
    `LeanCanny.Encoding.ImplicitSourceCoerciveBoxGram.reader,
    `LeanCanny.Encoding.ImplicitSourceGramSliceNative.evaluator,
    `LeanCanny.Encoding.ImplicitSourceGramGrid.access,
    `LeanCanny.Encoding.ImplicitSourceGramGridWords.exists_word,
    `LeanCanny.Encoding.ImplicitSourceGramGridWordBudget.exists_bounded_word,
    `LeanCanny.Encoding.ImplicitSourceComponentSampler.component_hit,
    `LeanCanny.Encoding.FormulaSignSlotRadialJointStratumSampler.mem_PSPACE,
    `LeanCanny.Encoding.FormulaSignSlotRadialJointStratumSampler.accepted_iff,
    `LeanCanny.Encoding.FormulaSignSlotRadialJointStratumSampler.component_hit,
    `LeanCanny.Encoding.FormulaSignSlotRadialJointStratumSampler.nonempty_iff]
  for name in names do
    for ax in ← collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "{name} depends on unexpected axiom {ax}"
  logInfo m!"Checked the actual implicit-stratum sampler and {names.size} standard-axiom closures."
