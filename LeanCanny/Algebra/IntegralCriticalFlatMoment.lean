/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralBlockMomentRequery
public import LeanCanny.Algebra.IntegralBlockMomentRecursiveStage
public import LeanCanny.Algebra.MatrixPowerModularRecursiveStageLocal
public import LeanCanny.Algebra.IntegralCriticalFlatBerkowitzQuery
/-! # Flat trailing moments with native local bounds

Slots eleven and twelve retain the relative factor's spatial indices.
The output old-basis ranks use row/column fields. Matrix-power children
replace those ranks with augmented matrix indices; the moment matrix
itself is independent of the chosen output ranks.
-/
@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatMomentBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM
open IntegralCriticalHistoryTask
set_option backward.isDefEq.respectTransparency false
abbrev Source := IntegralBerkowitzBlockBits.Source

def packet (P : Parameters) (c : List Bool) : List Bool :=
  pair (IntegralBlockMomentBits.context c (get P .row c) (get P .col c))
    (pair (BinaryNatCode.encode (get P .slot11 c)) (BinaryNatCode.encode (get P .slot12 c)))

theorem packet_FP (P : Parameters) (a : Access P) : packet P ∈ FP :=
  mem_FP_pair (mem_FP_pair id_mem_FP (mem_FP_pair (get_binary P a .row).bits_mem_FP (get_binary P a .col).bits_mem_FP))
    (mem_FP_pair (get_binary P a .slot11).bits_mem_FP (get_binary P a .slot12).bits_mem_FP)

theorem packet_parent (P : Parameters) (c : List Bool) : IntegralBerkowitzBlockBits.original (packet P c) = c := by
  simp only [packet, IntegralBerkowitzBlockBits.original, IntegralBlockMomentBits.context, pairFst_pair]

noncomputable def source (P : Parameters) (S : Source) : IntegralBlockMomentBits.Family :=
  (IntegralBerkowitzBlockBits.momentFamily S).requery (packet P)

noncomputable def access (P : Parameters) (a : Access P) (S : Source) (h : IntegralBerkowitzBlockBits.Access S) :
    IntegralBlockMomentBits.Access (source P S) :=
  IntegralBlockMomentBits.Access.requery (IntegralBerkowitzBlockBits.momentFamily S)
    (IntegralBerkowitzBlockBits.momentAccess S h) (packet P) (packet_FP P a)

noncomputable def controller (P : Parameters) (a : Access P) (S : Source) (h : IntegralBerkowitzBlockBits.Access S) :=
  IntegralBlockMomentBits.RecursiveStage.controller (source P S) (access P a S h)
    (IntegralCriticalFlatMatrixQuery.writer P .momentEntry)

theorem certificates (P : Parameters) (a : Access P) (S : Source) (h : IntegralBerkowitzBlockBits.Access S) :
    (controller P a S h).Certificates (encQ := encBits) (encS := encBits) :=
  IntegralBlockMomentBits.RecursiveStage.certificates (source P S) (access P a S h) _
    (IntegralCriticalFlatMatrixQuery.writer_FP P a .momentEntry)

abbrev RepliesAt (P : Parameters) (S : Source) (answer : List Bool → List Bool) (c : List Bool) : Prop :=
  ∀ i j : Fin (((source P S).dimension c + 2) * (source P S).rank c),
    answer (IntegralCriticalFlatMatrixQuery.writer P .momentEntry
      (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
      residueBits (((source P S).powerMatrix c i j : ℤ) : ZMod ((source P S).modulus c))

noncomputable def clock (P : Parameters) (S : Source) := ModularRecursiveStage.clock (IntegralBlockMomentBits.powerFamily (source P S))
noncomputable def stateBound (P : Parameters) (S : Source) := ModularRecursiveStage.stateBound (IntegralBlockMomentBits.powerFamily (source P S))

theorem clock_binary (P : Parameters) (a : Access P) (S : Source) (h : IntegralBerkowitzBlockBits.Access S) : BinaryFn (clock P S) :=
  IntegralBlockMomentBits.RecursiveStage.clock_binary (source P S) (access P a S h)

theorem stateBound_unary (P : Parameters) (a : Access P) (S : Source) (h : IntegralBerkowitzBlockBits.Access S) : UnaryFn (stateBound P S) :=
  IntegralBlockMomentBits.RecursiveStage.stateBound_unary (source P S) (access P a S h)

theorem halted_after (P : Parameters) (a : Access P) (S : Source) (h : IntegralBerkowitzBlockBits.Access S)
    (answer : List Bool → List Bool) (c : List Bool) (he : RepliesAt P S answer c) :
    (controller P a S h).halted (((controller P a S h).reference answer)^[clock P S c] ((controller P a S h).initial c)) = true :=
  ModularRecursiveStage.halted_after_local (IntegralBlockMomentBits.powerAccess (source P S) (access P a S h))
    (IntegralCriticalFlatMatrixQuery.writer P .momentEntry) answer c he

theorem output_when_halted (P : Parameters) (a : Access P) (S : Source) (h : IntegralBerkowitzBlockBits.Access S)
    (answer : List Bool → List Bool) (c : List Bool) (he : RepliesAt P S answer c) (t : ℕ)
    (hh : (controller P a S h).halted (((controller P a S h).reference answer)^[t] ((controller P a S h).initial c)) = true) :
    (controller P a S h).output (((controller P a S h).reference answer)^[t] ((controller P a S h).initial c)) =
      (IntegralBerkowitzBlockBits.momentFamily S).value (packet P c) :=
  (ModularRecursiveStage.output_when_halted_local (IntegralBlockMomentBits.powerAccess (source P S) (access P a S h))
    (IntegralCriticalFlatMatrixQuery.writer P .momentEntry) answer c he t hh).trans
      ((congrFun (IntegralBlockMomentBits.power_value (source P S)) c).trans
        (IntegralBlockMomentBits.Family.requery_value _ _ c))

theorem state_length (P : Parameters) (a : Access P) (S : Source) (h : IntegralBerkowitzBlockBits.Access S)
    (answer : List Bool → List Bool) (c : List Bool) (he : RepliesAt P S answer c) (t : ℕ) :
    (((controller P a S h).reference answer)^[t] ((controller P a S h).initial c)).length ≤ stateBound P S c :=
  ModularRecursiveStage.state_length_local (IntegralBlockMomentBits.powerAccess (source P S) (access P a S h))
    (IntegralCriticalFlatMatrixQuery.writer P .momentEntry) answer c he t

theorem requests_frame (P : Parameters) (a : Access P) (S : Source) (h : IntegralBerkowitzBlockBits.Access S)
    (answer : List Bool → List Bool) (c : List Bool) (he : RepliesAt P S answer c) (budget : List Bool → ℕ) (child : List Bool)
    (hp : isPhase .momentPower c) (hc : (controller P a S h).Requests answer budget c child) :
    RankedHistoryTask.root child = RankedHistoryTask.root c ∧ child.length ≤ wordBudget P c ∧ rank P child < rank P c := by
  obtain ⟨i, j, rfl⟩ := ModularRecursiveStage.requests_in_bounds_local
    (IntegralBlockMomentBits.powerAccess (source P S) (access P a S h))
    (IntegralCriticalFlatMatrixQuery.writer P .momentEntry) answer c he budget child hc
  refine ⟨?_, ?_, ?_⟩
  · simpa only [pairFst_pair] using IntegralCriticalFlatMatrixQuery.writer_root P .momentEntry
      (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))
  · simpa only [pairFst_pair] using IntegralCriticalFlatMatrixQuery.writer_length P .momentEntry
      (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))
  · have H := IntegralCriticalFlatMatrixQuery.writer_lower_rank P .momentEntry
      (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))
    simp only [pairFst_pair] at H
    apply H
    change phase c = 22 at hp
    change 21 < phase c
    omega

end LeanCanny.Algebra.IntegralCriticalFlatMomentBits
