/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalFlatGrid
public import LeanCanny.Algebra.IntegralMonomialTermController
public import LeanCanny.Algebra.IntegralCriticalScriptDenominatorFP

/-! # Actual monomial sources at flat original-grid indices

Pulling back the existing monomial source through the bounded source-index
packet preserves its algebra elements and their actual multiplication
matrices. The original common-denominator reader is native FP; no factor,
coefficient, or height evaluator is an input to the source adapter.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralMonomialTermBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
set_option backward.isDefEq.respectTransparency false

noncomputable def Source.requery (S : Source) (input : List Bool → List Bool) : Source where
  arity c := S.arity (input c)
  rank c := S.rank (input c)
  carrier c := S.carrier (input c)
  ring c := S.ring (input c)
  basis c := S.basis (input c)
  coefficient c := S.coefficient (input c)
  denominator c := S.denominator (input c)
  height c := S.height (input c)
  exponent c := S.exponent (input c)
  allowance c := S.allowance (input c)
  offset c := S.offset (input c)
  free c := S.free (input c)
  row c := S.row (input c)
  col c := S.col (input c)
  modulus c := S.modulus (input c)
  modulus_ne_zero c := S.modulus_ne_zero (input c)

def readerQuery (input : List Bool → List Bool) (p : List Bool) : List Bool :=
  pair (input (pairFst p)) (pairSnd p)

theorem readerQuery_FP (input : List Bool → List Bool) (hi : input ∈ FP) : readerQuery input ∈ FP :=
  mem_FP_pair (mem_FP_comp pairFst_mem_FP hi) pairSnd_mem_FP

noncomputable def Access.requery (S : Source) (a : Access S) (input : List Bool → List Bool) (hi : input ∈ FP) :
    Access (S.requery input) where
  arity := a.arity.comp hi
  rank := a.rank.comp hi
  modulus := a.modulus.comp hi
  row := a.row.comp hi
  col := a.col.comp hi
  allowance := a.allowance.comp hi
  offset := a.offset.comp hi
  free := a.free.comp hi
  exponent := by
    have H := a.exponent.comp (readerQuery_FP input hi)
    simpa only [Function.comp_def, readerQuery, pairFst_pair, pairSnd_pair, Source.requery] using H
  coefficient := a.coefficient ∘ readerQuery input
  height := a.height ∘ readerQuery input
  denominator := a.denominator ∘ input
  coefficient_eq c r t := by
    simp only [Function.comp_apply, readerQuery, pairFst_pair, pairSnd_pair]
    exact a.coefficient_eq (input c) r t
  height_eq c i r t := by
    simp only [Function.comp_apply, readerQuery, pairFst_pair, pairSnd_pair]
    exact a.height_eq (input c) i r t
  denominator_eq c := a.denominator_eq (input c)

theorem requery_factor (S : Source) (input : List Bool → List Bool) (c : List Bool) (s : ℕ) :
    letI := S.ring (input c)
    factor (S.requery input) c s = factor S (input c) s := rfl

theorem requery_value (S : Source) (input : List Bool → List Bool) (c : List Bool) :
    (S.requery input).value c = S.value (input c) := rfl

end LeanCanny.Algebra.IntegralMonomialTermBits

namespace LeanCanny.Algebra.IntegralCriticalFlatMonomialSourceBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
set_option backward.isDefEq.respectTransparency false

noncomputable def source (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) : IntegralMonomialTermBits.Source :=
  (IntegralClearedCoefficientBits.termSource (IntegralCriticalFlatGridBits.source P F q)).requery
    (IntegralCriticalFlatGridBits.termInput P)

noncomputable def access (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : IntegralCriticalScriptGeneratorBits.Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (h : IntegralCriticalScriptEulerBits.Controls F q) : IntegralMonomialTermBits.Access (source P F q) :=
  (IntegralClearedCoefficientBits.termAccess (IntegralCriticalFlatGridBits.source P F q)
    (IntegralCriticalFlatGridBits.access P a F q h)).requery _ (IntegralCriticalFlatGridBits.termInput P)
      (IntegralCriticalFlatGridBits.termInput_FP P a)

theorem arity (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (c : List Bool) :
    (source P F q).arity c = F.ambient c + 1 := by
  change (IntegralCriticalFlatGridBits.source P F q).arity (pairFst (IntegralCriticalFlatGridBits.termInput P c)) = _
  rw [IntegralCriticalFlatGridBits.termInput_parent, IntegralCriticalFlatGridBits.source_arity]

theorem rank (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (c : List Bool) :
    (source P F q).rank c = (IntegralCriticalFlatEulerRowsBits.source P F q).rank c := by
  change (IntegralCriticalFlatEulerRowsBits.source P F q).rank
    (pairFst (IntegralCriticalFlatGridBits.termInput P c)) = _
  rw [IntegralCriticalFlatGridBits.termInput_parent]

theorem exponent (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (c : List Bool) (i : ℕ) (hi : i < F.ambient c + 1) :
    (source P F q).exponent c i = FixedWidthPolynomial.entry (F.sourceWidth c)
      (IntegralCriticalHistoryTask.get P .sourceIndex c) i := by
  change (IntegralClearedCoefficientBits.termSource (IntegralCriticalFlatGridBits.source P F q)).exponent
    (IntegralCriticalFlatGridBits.termInput P c) i = _
  rw [IntegralClearedCoefficientBits.term_exponent]
  · simp only [IntegralCriticalFlatGridBits.source_sourceWidth,
      IntegralCriticalFlatGridBits.termInput, pairFst_pair, pairSnd_pair, BinaryNatCode.encode, Nat.fromBitsLE_bits]
  · simpa only [IntegralCriticalFlatGridBits.termInput_parent, IntegralCriticalFlatGridBits.source_arity] using hi

theorem value (P : IntegralCriticalHistoryTask.Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (c : List Bool) :
    (source P F q).value c = (IntegralClearedCoefficientBits.termSource (IntegralCriticalFlatGridBits.source P F q)).value
      (IntegralCriticalFlatGridBits.termInput P c) := rfl

theorem denominator_FP (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : IntegralCriticalScriptGeneratorBits.Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (h : IntegralCriticalScriptEulerBits.Controls F q)
    (n : IntegralCriticalScriptFP.Access (IntegralCriticalFlatCompanionBits.metadata F)) :
    (access P a F q h).denominator ∈ FP := by
  have HD := IntegralCriticalScriptDenominatorFP.queried_denominator_FP F q h.script n
  refine mem_FP_of_eq HD (fun c => ?_)
  change residueBits ((IntegralCriticalScriptQueryBits.generatorSource F q).denominator c : ZMod (F.modulus c)) =
    residueBits ((IntegralCriticalScriptQueryBits.generatorSource F q).denominator
      (pairFst (IntegralCriticalFlatGridBits.termInput P c)) : ZMod (F.modulus (pairFst (IntegralCriticalFlatGridBits.termInput P c))))
  rw [IntegralCriticalFlatGridBits.termInput_parent]

end LeanCanny.Algebra.IntegralCriticalFlatMonomialSourceBits
