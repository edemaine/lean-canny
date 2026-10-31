/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralBlockMomentSpace
public import LeanCanny.Algebra.MatrixMomentEntryController

/-! # Resumable entries of actual integer moment blocks

The old basis ranks and outer vertices use the existing binary routing.
Each nonzero entry suspends for exactly one row, column, or interior source
request. Its semantics is the actual constructed integer block matrix.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralBlockMomentBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
set_option backward.isDefEq.respectTransparency false

noncomputable def program (F : Family) (a : Access F) (rowTask columnTask matrixTask : List Bool → List Bool) : SingleCall.Program :=
  MatrixMoment.EntryBits.program (bitsAccess F a) (outerPacket F) rowTask columnTask matrixTask

theorem program_controls (F : Family) (a : Access F) (rowTask columnTask matrixTask : List Bool → List Bool)
    (hr : rowTask ∈ FP) (hc : columnTask ∈ FP) (hm : matrixTask ∈ FP) : (program F a rowTask columnTask matrixTask).Controls := by
  have HD : BinaryFn (fun q => F.dimension (pairFst q)) := a.dimension.comp pairFst_mem_FP
  exact MatrixMoment.EntryBits.program_controls (bitsAccess F a) HD.bits_mem_FP
    (outerPacket F) rowTask columnTask matrixTask (outerPacket_FP F a) hr hc hm

theorem program_value (F : Family) (a : Access F) (rowTask columnTask matrixTask answer : List Bool → List Bool)
    (hr : ∀ p, answer (rowTask p) = a.row p)
    (hc : ∀ p, answer (columnTask p) = a.column p)
    (hm : ∀ p, answer (matrixTask p) = a.entry p) (p : List Bool) :
    (program F a rowTask columnTask matrixTask).value answer p = entryProgram F a p :=
  MatrixMoment.EntryBits.program_value (bitsAccess F a) (outerPacket F) rowTask columnTask matrixTask answer hr hc hm p

theorem program_packet (F : Family) (a : Access F) (rowTask columnTask matrixTask answer : List Bool → List Bool)
    (hr : ∀ p, answer (rowTask p) = a.row p)
    (hc : ∀ p, answer (columnTask p) = a.column p)
    (hm : ∀ p, answer (matrixTask p) = a.entry p) (c : List Bool)
    (i j : Fin ((F.dimension c + 2) * F.rank c)) :
    (program F a rowTask columnTask matrixTask).value answer
      (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) =
        residueBits ((F.powerMatrix c i j : ℤ) : ZMod (F.modulus c)) :=
  (program_value F a rowTask columnTask matrixTask answer hr hc hm _).trans (entry_correct F a c i j)

end LeanCanny.Algebra.IntegralBlockMomentBits
