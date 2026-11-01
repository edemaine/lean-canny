/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalFlatFactorQuery

/-! # Actual flat monomial product powers

Phase 6 powers the layered matrix of actual original-grid factors.
Its phase 5 children contain fresh matrix ranks. Native local clocks and
state bounds use only source metadata and semantic child replies.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatProductBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalHistoryTask.rank IntegralCriticalHistoryTask.Tasks
abbrev Queries := IntegralCriticalScriptGeneratorBits.Queries

noncomputable def family (P : IntegralCriticalHistoryTask.Parameters) (F : Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) : IntegralPowerProductBits.Family :=
  IntegralMonomialTermBits.family (IntegralCriticalFlatMonomialSourceBits.source P F q)

noncomputable def access (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (h : IntegralCriticalScriptEulerBits.Controls F q) : IntegralPowerProductBits.Access (family P F q) :=
  IntegralMonomialTermBits.familyAccess _ (IntegralCriticalFlatMonomialSourceBits.access P a F q h)

noncomputable def controller (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (h : IntegralCriticalScriptEulerBits.Controls F q) :=
  IntegralPowerProductBits.ProductStage.controller (family P F q) (access P a F q h)
    (IntegralCriticalFlatMatrixQuery.writer P .productEntry)

theorem certificates (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (h : IntegralCriticalScriptEulerBits.Controls F q) :
    (controller P a F q h).Certificates (encQ := encBits) (encS := encBits) :=
  IntegralPowerProductBits.ProductStage.certificates _ _ _
    (IntegralCriticalFlatMatrixQuery.writer_FP P a .productEntry)

noncomputable def clock (P : IntegralCriticalHistoryTask.Parameters) (F : Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) :=
  ModularRecursiveStage.clock (IntegralPowerProductBits.productFamily (family P F q)).power
noncomputable def stateBound (P : IntegralCriticalHistoryTask.Parameters) (F : Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) :=
  ModularRecursiveStage.stateBound (IntegralPowerProductBits.productFamily (family P F q)).power

theorem clock_binary (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (h : IntegralCriticalScriptEulerBits.Controls F q) : BinaryFn (clock P F q) :=
  IntegralPowerProductBits.ProductStage.clock_binary _ (access P a F q h)
theorem stateBound_unary (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (h : IntegralCriticalScriptEulerBits.Controls F q) : UnaryFn (stateBound P F q) :=
  IntegralPowerProductBits.ProductStage.stateBound_unary _ (access P a F q h)

abbrev Replies (P : IntegralCriticalHistoryTask.Parameters) (F : Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (answer : List Bool → List Bool) : Prop :=
  ∀ c (i j : Fin ((IntegralPowerProductBits.productFamily (family P F q)).power.dimension c)),
    answer (IntegralCriticalFlatMatrixQuery.writer P .productEntry (pair c
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
      residueBits ((IntegralPowerProductBits.productFamily (family P F q)).power.matrix c i j)

theorem halted_after (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (h : IntegralCriticalScriptEulerBits.Controls F q) (answer : List Bool → List Bool)
    (he : Replies P F q answer) (c : List Bool) :
    (controller P a F q h).halted (((controller P a F q h).reference answer)^[clock P F q c]
      ((controller P a F q h).initial c)) = true :=
  IntegralPowerProductBits.ProductStage.halted_after _ _ _ answer he c

theorem output_when_halted (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (h : IntegralCriticalScriptEulerBits.Controls F q) (answer : List Bool → List Bool)
    (he : Replies P F q answer) (c : List Bool) (t : ℕ)
    (hh : (controller P a F q h).halted (((controller P a F q h).reference answer)^[t]
      ((controller P a F q h).initial c)) = true) :
    (controller P a F q h).output (((controller P a F q h).reference answer)^[t]
      ((controller P a F q h).initial c)) =
      (IntegralClearedCoefficientBits.termSource (IntegralCriticalFlatGridBits.source P F q)).value
        (IntegralCriticalFlatGridBits.termInput P c) := by
  exact IntegralMonomialTermBits.ProductStage.output_when_halted _ _ _ answer he c t hh

theorem state_length (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (h : IntegralCriticalScriptEulerBits.Controls F q) (answer : List Bool → List Bool)
    (he : Replies P F q answer) (c : List Bool) (t : ℕ) :
    (((controller P a F q h).reference answer)^[t] ((controller P a F q h).initial c)).length ≤ stateBound P F q c :=
  IntegralPowerProductBits.ProductStage.state_length _ _ _ answer he c t

theorem requests_in_bounds (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (h : IntegralCriticalScriptEulerBits.Controls F q) (answer : List Bool → List Bool)
    (he : Replies P F q answer) (budget : List Bool → ℕ) (c child : List Bool)
    (hc : (controller P a F q h).Requests answer budget c child) :
    ∃ i j : Fin ((IntegralPowerProductBits.productFamily (family P F q)).power.dimension c),
      child = IntegralCriticalFlatMatrixQuery.writer P .productEntry
        (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) :=
  MatrixProductBits.RecursiveStage.requests_in_bounds _ _ _ answer he budget c child hc

theorem requests_rank (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (h : IntegralCriticalScriptEulerBits.Controls F q) (answer : List Bool → List Bool)
    (he : Replies P F q answer) (budget : List Bool → ℕ) (c child : List Bool)
    (hp : IntegralCriticalHistoryTask.isPhase .productPower c)
    (hc : (controller P a F q h).Requests answer budget c child) :
    IntegralCriticalHistoryTask.rank P child < IntegralCriticalHistoryTask.rank P c := by
  obtain ⟨i, j, rfl⟩ := requests_in_bounds P a F q h answer he budget c child hc
  have HL := IntegralCriticalFlatMatrixQuery.writer_lower_rank P .productEntry
    (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))
  simp only [pairFst_pair] at HL
  apply HL
  change IntegralCriticalHistoryTask.phase c = 6 at hp
  change 5 < IntegralCriticalHistoryTask.phase c
  omega

theorem requests_tasks (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (h : IntegralCriticalScriptEulerBits.Controls F q) (answer : List Bool → List Bool)
    (he : Replies P F q answer) (budget : List Bool → ℕ) (r c child : List Bool)
    (ht : IntegralCriticalHistoryTask.Tasks P r c)
    (hc : (controller P a F q h).Requests answer budget c child) :
    IntegralCriticalHistoryTask.Tasks P r child := by
  obtain ⟨i, j, rfl⟩ := requests_in_bounds P a F q h answer he budget c child hc
  apply IntegralCriticalFlatMatrixQuery.writer_tasks
  simpa only [pairFst_pair] using ht

end LeanCanny.Algebra.IntegralCriticalFlatProductBits
