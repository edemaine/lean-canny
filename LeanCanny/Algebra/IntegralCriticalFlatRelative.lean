/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalFlatCoefficient
public import LeanCanny.Algebra.IntegralCriticalFlatMatrixQuery
public import LeanCanny.Algebra.IntegralBerkowitzRecursiveStage

/-! # Flat powering for the actual relative characteristic coefficient

The critical coefficient's exact action source supplies the relative
characteristic matrix. Its streamed entries are fresh phase23 tasks.
The native local clock and state bound are derived by the matrix-power
controller; child computation is handled by the shared ranked stack.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatRelativeBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM
open scoped Classical
set_option backward.isDefEq.respectTransparency false

abbrev Queries := IntegralCriticalScriptGeneratorBits.Queries

noncomputable def controller (P : IntegralCriticalHistoryTask.Parameters) (F : Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (h : IntegralCriticalFlatCoefficientBits.Controls F q) :=
  IntegralBerkowitzBlockBits.RecursiveStage.controller (IntegralCriticalFlatCoefficientBits.characteristic F q)
    (IntegralCriticalFlatCoefficientBits.characteristicAccess F q h)
    (IntegralCriticalFlatMatrixQuery.writer P .relativeFactor)

theorem certificates (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (h : IntegralCriticalFlatCoefficientBits.Controls F q) :
    (controller P F q h).Certificates (encQ := encBits) (encS := encBits) :=
  IntegralBerkowitzBlockBits.RecursiveStage.certificates _ _ _
    (IntegralCriticalFlatMatrixQuery.writer_FP P a .relativeFactor)

abbrev Replies (P : IntegralCriticalHistoryTask.Parameters) (F : Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (answer : List Bool → List Bool) : Prop :=
  ∀ c (i j : Fin (IntegralBerkowitzBlockBits.powerDimension (IntegralCriticalFlatCoefficientBits.characteristic F q) c)),
    answer (IntegralCriticalFlatMatrixQuery.writer P .relativeFactor (pair c
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
      residueBits (((IntegralCriticalFlatCoefficientBits.characteristic F q).powerMatrix c i j : ℤ) : ZMod (F.modulus c))

noncomputable def clock (F : Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) : List Bool → ℕ :=
  ModularRecursiveStage.clock (IntegralBerkowitzBlockBits.powerFamily (IntegralCriticalFlatCoefficientBits.characteristic F q))

noncomputable def stateBound (F : Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) : List Bool → ℕ :=
  ModularRecursiveStage.stateBound (IntegralBerkowitzBlockBits.powerFamily (IntegralCriticalFlatCoefficientBits.characteristic F q))

theorem clock_binary (F : Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (h : IntegralCriticalFlatCoefficientBits.Controls F q) : BinaryFn (clock F q) :=
  IntegralBerkowitzBlockBits.RecursiveStage.clock_binary _ (IntegralCriticalFlatCoefficientBits.characteristicAccess F q h)

theorem stateBound_unary (F : Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (h : IntegralCriticalFlatCoefficientBits.Controls F q) : UnaryFn (stateBound F q) :=
  IntegralBerkowitzBlockBits.RecursiveStage.stateBound_unary _ (IntegralCriticalFlatCoefficientBits.characteristicAccess F q h)

theorem halted_after (P : IntegralCriticalHistoryTask.Parameters) (F : Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (h : IntegralCriticalFlatCoefficientBits.Controls F q)
    (answer : List Bool → List Bool) (he : Replies P F q answer) (c : List Bool) :
    (controller P F q h).halted (((controller P F q h).reference answer)^[clock F q c]
      ((controller P F q h).initial c)) = true :=
  IntegralBerkowitzBlockBits.RecursiveStage.halted_after _ _ _ answer he c

theorem output_when_halted (P : IntegralCriticalHistoryTask.Parameters) (F : Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (h : IntegralCriticalFlatCoefficientBits.Controls F q)
    (answer : List Bool → List Bool) (he : Replies P F q answer) (c : List Bool) (t : ℕ)
    (hh : (controller P F q h).halted (((controller P F q h).reference answer)^[t] ((controller P F q h).initial c)) = true) :
    (controller P F q h).output (((controller P F q h).reference answer)^[t] ((controller P F q h).initial c)) =
      (IntegralCriticalFlatCoefficientBits.characteristic F q).value c :=
  IntegralBerkowitzBlockBits.RecursiveStage.output_when_halted _ _ _ answer he c t hh

theorem state_length (P : IntegralCriticalHistoryTask.Parameters) (F : Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (h : IntegralCriticalFlatCoefficientBits.Controls F q)
    (answer : List Bool → List Bool) (he : Replies P F q answer) (c : List Bool) (t : ℕ) :
    (((controller P F q h).reference answer)^[t] ((controller P F q h).initial c)).length ≤ stateBound F q c :=
  IntegralBerkowitzBlockBits.RecursiveStage.state_length _ _ _ answer he c t

theorem requests_rank (P : IntegralCriticalHistoryTask.Parameters) (F : Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) (h : IntegralCriticalFlatCoefficientBits.Controls F q)
    (answer : List Bool → List Bool) (he : Replies P F q answer) (budget : List Bool → ℕ) (c child : List Bool)
    (hp : IntegralCriticalHistoryTask.isPhase .relativePower c)
    (hc : (controller P F q h).Requests answer budget c child) :
    IntegralCriticalHistoryTask.rank P child < IntegralCriticalHistoryTask.rank P c := by
  obtain ⟨i, j, rfl⟩ := IntegralBerkowitzBlockBits.RecursiveStage.requests_in_bounds _ _ _ answer he budget c child hc
  have HL := IntegralCriticalFlatMatrixQuery.writer_lower_rank P .relativeFactor
    (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))
  simp only [pairFst_pair] at HL
  apply HL
  change IntegralCriticalHistoryTask.phase c = 24 at hp
  change 23 < IntegralCriticalHistoryTask.phase c
  omega

end LeanCanny.Algebra.IntegralCriticalFlatRelativeBits
