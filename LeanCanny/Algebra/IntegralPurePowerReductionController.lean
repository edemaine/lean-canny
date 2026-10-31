/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralPurePowerReductionSpace
public import LeanCanny.Algebra.PurePowerReductionController

/-! # Resumable reduction entries over an actual retained parameter algebra

The existing writer transposes spatial indices and retains both old basis
ranks. Normal diagonal entries use the FP integer-leading reader; each
other nonzero entry suspends for one original lower coefficient.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralPurePowerReductionBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open IntegralPurePowerActionBits (Source reductionSource)
open IntegralBerkowitzBlockBits (original basisRowCode basisColCode)
set_option backward.isDefEq.respectTransparency false

theorem constant_FP (S : Source) (a : Access S) (h : a.leading ∈ FP) : constant a ∈ FP := by
  have HG := (BinaryFn.fromBits IntegralBerkowitzBlockBits.basisRowCode_FP).eq
    (BinaryFn.fromBits IntegralBerkowitzBlockBits.basisColCode_FP)
  exact HG.ite_mem_FP
    (mem_FP_comp (f := original) (g := a.leading) IntegralBerkowitzBlockBits.original_FP h) (constFn_mem_FP [])

noncomputable def program (S : Source) (a : Access S) (task : List Bool → List Bool) : SingleCall.Program :=
  PurePowerReductionBits.program (layout S) (fun z => S.layout.bound (pairFst z))
    (constant a) (writer S) (task ∘ lowQuery)

theorem program_controls (S : Source) (a : Access S) (h : a.leading ∈ FP)
    (task : List Bool → List Bool) (ht : task ∈ FP) : (program S a task).Controls := by
  have HB : BinaryFn (fun z => S.layout.bound (pairFst z)) := a.bound.comp pairFst_mem_FP
  exact PurePowerReductionBits.program_controls (layout S) (layout_polyTime S a) _ HB
    (constant a) (writer S) (task ∘ lowQuery) (constant_FP S a h) (writer_FP S a) (mem_FP_comp lowQuery_FP ht)

theorem program_value (S : Source) (a : Access S) (task answer : List Bool → List Bool)
    (he : ∀ p, answer (task p) = a.low p) (p : List Bool) :
    (program S a task).value answer p = entryProgram S a p :=
  PurePowerReductionBits.program_value (layout S) (fun z => S.layout.bound (pairFst z))
    (constant a) (a.low ∘ lowQuery) (writer S) (task ∘ lowQuery) answer (fun q => he (lowQuery q)) p

theorem program_packet (S : Source) (a : Access S) (task answer : List Bool → List Bool)
    (he : ∀ p, answer (task p) = a.low p) (c : List Bool)
    (i j : Fin ((reductionSource S).dimension c)) (r t : Fin (S.rank c)) :
    (program S a task).value answer (IntegralReductionActionBits.packet c i.val j.val r.val t.val) =
      residueBits ((((reductionSource S).toSource.entryMatrix c i j r t) : ℤ) : ZMod (S.modulus c)) :=
  (program_value S a task answer he _).trans (entry_correct S a c i j r t)

theorem program_requests_iff (S : Source) (a : Access S) (task answer : List Bool → List Bool)
    (budget : List Bool → ℕ) (p child : List Bool) :
    (program S a task).controller.Requests answer budget p child ↔
      PurePowerReductionBits.request (layout S) (fun z => S.layout.bound (pairFst z)) (writer S p) ∧
        child = task (lowQuery (PurePowerReductionBits.sourceQuery (layout S) (writer S p))) :=
  PurePowerReductionBits.program_requests_iff (layout S) (fun z => S.layout.bound (pairFst z))
    (constant a) (writer S) (task ∘ lowQuery) answer budget p child

end LeanCanny.Algebra.IntegralPurePowerReductionBits
