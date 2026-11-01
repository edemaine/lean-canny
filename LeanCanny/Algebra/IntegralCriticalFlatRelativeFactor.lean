/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalFlatBerkowitzQuery
public import LeanCanny.Algebra.IntegralCriticalFlatCoefficient
public import LeanCanny.Computation.SingleCallRequery

/-! # Relative factor entries with flat diagonal and moment children

Zero and unit entries halt locally. The other branches request an actual
source-action entry or trailing block moment at a lower phase. The source
is the same exact relative characteristic matrix used by phase24.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatRelativeFactorBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open IntegralBerkowitzBlockBits
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] IntegralCriticalFlatBerkowitzQuery.entryWriter IntegralCriticalFlatBerkowitzQuery.momentWriter

def packet (P : Parameters) (c : List Bool) : List Bool :=
  pair c (pair (BinaryNatCode.encode (get P .row c)) (BinaryNatCode.encode (get P .col c)))

theorem packet_FP (P : Parameters) (a : IntegralCriticalHistoryTask.Access P) : packet P ∈ FP :=
  mem_FP_pair id_mem_FP (mem_FP_pair (get_binary P a .row).bits_mem_FP (get_binary P a .col).bits_mem_FP)

theorem outer_original (P : Parameters) (S : Source) (c : List Bool) : original (outerPacket S (packet P c)) = c := by
  simp only [outerPacket, original, IntegralBlockMomentBits.context, packet, pairFst_pair]

theorem diagonal_original (S : Source) (p : List Bool) : original (diagonalQuery S p) = original p := by
  simp only [original, diagonalQuery, IntegralBlockMomentBits.context, pairFst_pair]

noncomputable def program (P : Parameters) (S : Source) : SingleCall.Program :=
  (entryController S (IntegralCriticalFlatBerkowitzQuery.entryWriter P S)
    (IntegralCriticalFlatBerkowitzQuery.momentWriter P)).requery (packet P)

theorem controls (P : Parameters) (a : IntegralCriticalHistoryTask.Access P) (S : Source)
    (h : IntegralBerkowitzBlockBits.Access S) : (program P S).Controls :=
  SingleCall.Program.requery_controls
    (entryController S (IntegralCriticalFlatBerkowitzQuery.entryWriter P S) (IntegralCriticalFlatBerkowitzQuery.momentWriter P))
    (entryController_controls S h _ _ (IntegralCriticalFlatBerkowitzQuery.entryWriter_FP P a S h)
      (IntegralCriticalFlatBerkowitzQuery.momentWriter_FP P a)) (packet P) (packet_FP P a)

theorem value (P : Parameters) (S : Source) (a : IntegralBerkowitzBlockBits.Access S)
    (answer : List Bool → List Bool)
    (hd : ∀ p, selector S p = [false, true] → answer (IntegralCriticalFlatBerkowitzQuery.entryWriter P S (diagonalQuery S p)) = a.entry (diagonalQuery S p))
    (hm : ∀ p, selector S p = [true, true] → answer (IntegralCriticalFlatBerkowitzQuery.momentWriter P p) = (momentFamily S).value p)
    (c : List Bool) : (program P S).value answer c = entryProgram S a (packet P c) := by
  rw [program, SingleCall.Program.requery_value]
  exact entryController_value S a _ _ answer hd hm _

theorem value_entry (P : Parameters) (S : Source) (a : IntegralBerkowitzBlockBits.Access S)
    (answer : List Bool → List Bool)
    (hd : ∀ p, selector S p = [false, true] → answer (IntegralCriticalFlatBerkowitzQuery.entryWriter P S (diagonalQuery S p)) = a.entry (diagonalQuery S p))
    (hm : ∀ p, selector S p = [true, true] → answer (IntegralCriticalFlatBerkowitzQuery.momentWriter P p) = (momentFamily S).value p)
    (c : List Bool) (i j : Fin (powerDimension S c)) (hi : get P .row c = i.val) (hj : get P .col c = j.val) :
    (program P S).value answer c = residueBits ((S.powerMatrix c i j : ℤ) : ZMod (S.modulus c)) := by
  rw [value P S a answer hd hm c]
  simp only [packet, hi, hj]
  exact entry_correct S a c i j

theorem requests_rank (P : Parameters) (S : Source) (answer : List Bool → List Bool)
    (budget : List Bool → ℕ) (c child : List Bool) (hp : isPhase .relativeFactor c)
    (hc : (program P S).controller.Requests answer budget c child) : rank P child < rank P c := by
  obtain ⟨_, hchild⟩ := (SingleCall.Program.requery_requests_iff
    (entryController S (IntegralCriticalFlatBerkowitzQuery.entryWriter P S) (IntegralCriticalFlatBerkowitzQuery.momentWriter P))
    (packet P) answer budget c child).mp hc
  simp only [entryController, IntegralBerkowitzBlockBits.program] at hchild
  unfold IntegralBerkowitzBlockBits.child at hchild
  split_ifs at hchild
  · rw [hchild]
    have H := IntegralCriticalFlatBerkowitzQuery.entryWriter_lower_rank P S
      (diagonalQuery S (outerPacket S (packet P c)))
    rw [diagonal_original, outer_original] at H
    apply H
    change phase c = 23 at hp
    omega
  · rw [hchild]
    have H := IntegralCriticalFlatBerkowitzQuery.momentWriter_lower_rank P (outerPacket S (packet P c))
    rw [outer_original] at H
    apply H
    change phase c = 23 at hp
    omega

theorem requests_tasks (P : Parameters) (S : Source) (answer : List Bool → List Bool)
    (budget : List Bool → ℕ) (r c child : List Bool) (ht : Tasks P r c)
    (hc : (program P S).controller.Requests answer budget c child) : Tasks P r child := by
  obtain ⟨_, hchild⟩ := (SingleCall.Program.requery_requests_iff
    (entryController S (IntegralCriticalFlatBerkowitzQuery.entryWriter P S) (IntegralCriticalFlatBerkowitzQuery.momentWriter P))
    (packet P) answer budget c child).mp hc
  simp only [entryController, IntegralBerkowitzBlockBits.program] at hchild
  unfold IntegralBerkowitzBlockBits.child at hchild
  split_ifs at hchild
  · rw [hchild]
    apply IntegralCriticalFlatBerkowitzQuery.entryWriter_tasks
    simpa only [diagonal_original, outer_original] using ht
  · rw [hchild]
    apply IntegralCriticalFlatBerkowitzQuery.momentWriter_tasks
    simpa only [outer_original] using ht

noncomputable def actualProgram (P : Parameters) (F : IntegralCriticalScriptGeneratorBits.Queries)
    (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) : SingleCall.Program :=
  program P (IntegralCriticalFlatCoefficientBits.characteristic F q)

theorem actual_controls (P : Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : IntegralCriticalScriptGeneratorBits.Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (h : IntegralCriticalFlatCoefficientBits.Controls F q) : (actualProgram P F q).Controls :=
  controls P a _ (IntegralCriticalFlatCoefficientBits.characteristicAccess F q h)

end LeanCanny.Algebra.IntegralCriticalFlatRelativeFactorBits
