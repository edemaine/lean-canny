/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalFlatProduct
public import LeanCanny.Algebra.MatrixPowerModularRequery

/-! # Actual factor powers on flat contexts

The selected factor is read from bounded slot 8. Matrix-entry children
replace only row and column, preserving that position and the original
source. Replies are required only at actual flat contexts and Fin ranks.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatFactorBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalHistoryTask.rank IntegralCriticalHistoryTask.Tasks
abbrev Queries := IntegralCriticalScriptGeneratorBits.Queries

noncomputable def family (P : IntegralCriticalHistoryTask.Parameters) (F : Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) : ModularFamily :=
  (IntegralPowerProductBits.powerFamily (IntegralCriticalFlatProductBits.family P F q)).requery
    (IntegralCriticalFlatFactorQuery.input P)

noncomputable def access (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (h : IntegralCriticalScriptEulerBits.Controls F q) : ModularAccess (family P F q) :=
  (IntegralPowerProductBits.powerAccess (IntegralCriticalFlatProductBits.family P F q)
    (IntegralCriticalFlatProductBits.access P a F q h)).requery _ (IntegralCriticalFlatFactorQuery.input P)

theorem controls (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (h : IntegralCriticalScriptEulerBits.Controls F q) : (access P a F q h).ControlsPolyTime :=
  ModularAccess.requery_controls _ _ (IntegralPowerProductBits.power_controls _
    (IntegralCriticalFlatProductBits.access P a F q h)) _ (IntegralCriticalFlatFactorQuery.input_FP P a)

noncomputable def controller (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (h : IntegralCriticalScriptEulerBits.Controls F q) :=
  ModularRecursiveStage.stage (access P a F q h)
    (IntegralCriticalFlatMatrixQuery.writer P .monomialFactor)

theorem certificates (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (h : IntegralCriticalScriptEulerBits.Controls F q) :
    (controller P a F q h).Certificates (encQ := encBits) (encS := encBits) :=
  ModularRecursiveStage.certificates (access P a F q h) (controls P a F q h) _
    (IntegralCriticalFlatMatrixQuery.writer_FP P a .monomialFactor)

noncomputable def clock (P : IntegralCriticalHistoryTask.Parameters) (F : Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) :=
  ModularRecursiveStage.clock (family P F q)
noncomputable def stateBound (P : IntegralCriticalHistoryTask.Parameters) (F : Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) :=
  ModularRecursiveStage.stateBound (family P F q)

theorem clock_binary (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (h : IntegralCriticalScriptEulerBits.Controls F q) : BinaryFn (clock P F q) :=
  ModularRecursiveStage.clock_binary (access P a F q h) (controls P a F q h)
theorem stateBound_unary (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (h : IntegralCriticalScriptEulerBits.Controls F q) : UnaryFn (stateBound P F q) :=
  ModularRecursiveStage.stateBound_unary (access P a F q h) (controls P a F q h)

abbrev Replies (P : IntegralCriticalHistoryTask.Parameters) (F : Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (answer : List Bool → List Bool) : Prop :=
  ∀ c (i j : Fin ((family P F q).dimension c)),
    answer (IntegralCriticalFlatMatrixQuery.writer P .monomialFactor (pair c
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
      residueBits ((family P F q).matrix c i j)

theorem halted_after (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (h : IntegralCriticalScriptEulerBits.Controls F q) (answer : List Bool → List Bool)
    (he : Replies P F q answer) (c : List Bool) :
    (controller P a F q h).halted (((controller P a F q h).reference answer)^[clock P F q c]
      ((controller P a F q h).initial c)) = true :=
  ModularRecursiveStage.halted_after (access P a F q h) _ answer he c

theorem output_when_halted (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (h : IntegralCriticalScriptEulerBits.Controls F q) (answer : List Bool → List Bool)
    (he : Replies P F q answer) (c : List Bool) (t : ℕ)
    (hh : (controller P a F q h).halted (((controller P a F q h).reference answer)^[t]
      ((controller P a F q h).initial c)) = true) :
    (controller P a F q h).output (((controller P a F q h).reference answer)^[t]
      ((controller P a F q h).initial c)) =
      (IntegralPowerProductBits.powerFamily (IntegralCriticalFlatProductBits.family P F q)).value
        (IntegralCriticalFlatFactorQuery.input P c) :=
  ModularRecursiveStage.output_when_halted (access P a F q h) _ answer he c t hh

theorem state_length (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (h : IntegralCriticalScriptEulerBits.Controls F q) (answer : List Bool → List Bool)
    (he : Replies P F q answer) (c : List Bool) (t : ℕ) :
    (((controller P a F q h).reference answer)^[t] ((controller P a F q h).initial c)).length ≤ stateBound P F q c :=
  ModularRecursiveStage.state_length (access P a F q h) _ answer he c t

theorem requests_in_bounds (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (h : IntegralCriticalScriptEulerBits.Controls F q) (answer : List Bool → List Bool)
    (he : Replies P F q answer) (budget : List Bool → ℕ) (c child : List Bool)
    (hc : (controller P a F q h).Requests answer budget c child) :
    ∃ i j : Fin ((family P F q).dimension c),
      child = IntegralCriticalFlatMatrixQuery.writer P .monomialFactor
        (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) :=
  ModularRecursiveStage.requests_in_bounds (access P a F q h) _ answer he budget c child hc

theorem requests_rank (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (h : IntegralCriticalScriptEulerBits.Controls F q) (answer : List Bool → List Bool)
    (he : Replies P F q answer) (budget : List Bool → ℕ) (c child : List Bool)
    (hp : IntegralCriticalHistoryTask.isPhase .factorPower c)
    (hc : (controller P a F q h).Requests answer budget c child) :
    IntegralCriticalHistoryTask.rank P child < IntegralCriticalHistoryTask.rank P c := by
  obtain ⟨i, j, rfl⟩ := requests_in_bounds P a F q h answer he budget c child hc
  have HL := IntegralCriticalFlatMatrixQuery.writer_lower_rank P .monomialFactor
    (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))
  simp only [pairFst_pair] at HL
  apply HL
  change IntegralCriticalHistoryTask.phase c = 4 at hp
  change 3 < IntegralCriticalHistoryTask.phase c
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

end LeanCanny.Algebra.IntegralCriticalFlatFactorBits
