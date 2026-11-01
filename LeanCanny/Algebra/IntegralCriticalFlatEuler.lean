/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralCriticalScriptEuler
public import LeanCanny.Algebra.IntegralCriticalHistoryTask

/-! # Flat Euler objective stages over actual critical script sources

Retargeting writes a fresh bounded field vector and preserves the original
root, birth, modulus, and source fields. The objective stage requests the
actual frozen lower coefficient and Euler sum at lower phases. Its native
certificate requires only primitive source metadata, and its correctness
uses the semantic replies rather than child space assumptions.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralCriticalFlatEulerBits
open LeanCanny.Encoding LeanCanny.Computation MatrixPower
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def next (P : IntegralCriticalHistoryTask.Parameters) (phase : IntegralCriticalHistoryTask.Phase) : List Bool → List Bool :=
  IntegralCriticalHistoryTask.child P id (IntegralCriticalHistoryTask.birth P) phase
    (RankedHistoryFields.read (IntegralCriticalHistoryTask.numericCap P) 16)

theorem next_FP (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (phase : IntegralCriticalHistoryTask.Phase) : next P phase ∈ FP :=
  IntegralCriticalHistoryTask.child_FP P a id id_mem_FP _
    (BinaryFn.ofUnary (RankedHistoryTask.birth_unary _ (IntegralCriticalHistoryTask.birthCap_unary P a))) phase _
    (RankedHistoryFields.read_FP _ _ (IntegralCriticalHistoryTask.numericCap_binary P a))

theorem next_root (P : IntegralCriticalHistoryTask.Parameters) (phase : IntegralCriticalHistoryTask.Phase) (c : List Bool) :
    RankedHistoryTask.root (next P phase c) = RankedHistoryTask.root c :=
  IntegralCriticalHistoryTask.child_root P _ _ _ _ c

theorem next_birth (P : IntegralCriticalHistoryTask.Parameters) (phase : IntegralCriticalHistoryTask.Phase) (c : List Bool) :
    IntegralCriticalHistoryTask.birth P (next P phase c) = IntegralCriticalHistoryTask.birth P c := by
  unfold next IntegralCriticalHistoryTask.child
  rw [RankedHistoryFields.flatten_eq_pack]
  exact RankedHistoryTask.birth_pack _ _ _ _ _ (min_le_right _ _)

theorem next_phase (P : IntegralCriticalHistoryTask.Parameters) (phase : IntegralCriticalHistoryTask.Phase) (c : List Bool) :
    IntegralCriticalHistoryTask.phase (next P phase c) = phase.code := by
  unfold next IntegralCriticalHistoryTask.child
  rw [RankedHistoryFields.flatten_eq_pack]
  exact RankedHistoryTask.phase_pack _ _ _ _ _ phase.code_lt

theorem next_get (P : IntegralCriticalHistoryTask.Parameters) (phase : IntegralCriticalHistoryTask.Phase)
    (c : List Bool) (f : IntegralCriticalHistoryTask.Field) :
    IntegralCriticalHistoryTask.get P f (next P phase c) = IntegralCriticalHistoryTask.get P f c := by
  rw [next, IntegralCriticalHistoryTask.child_get, RankedHistoryFields.read_packet]
  simp only [BinaryNatCode.encode, Nat.fromBitsLE_bits, id_eq]
  exact min_eq_left (IntegralCriticalHistoryTask.get_le P f c)

theorem next_modulus (P : IntegralCriticalHistoryTask.Parameters) (phase : IntegralCriticalHistoryTask.Phase) (c : List Bool) :
    IntegralCriticalHistoryTask.modulus P (next P phase c) = IntegralCriticalHistoryTask.modulus P c := by
  unfold IntegralCriticalHistoryTask.modulus
  rw [next_get]

theorem next_lower_rank (P : IntegralCriticalHistoryTask.Parameters) (phase : IntegralCriticalHistoryTask.Phase)
    (c : List Bool) (hp : phase.code < IntegralCriticalHistoryTask.phase c) :
    IntegralCriticalHistoryTask.rank P (next P phase c) < IntegralCriticalHistoryTask.rank P c :=
  IntegralCriticalHistoryTask.child_lower_phase P id _ phase _ c rfl hp

theorem next_tasks (P : IntegralCriticalHistoryTask.Parameters) (phase : IntegralCriticalHistoryTask.Phase)
    (r c : List Bool) (h : IntegralCriticalHistoryTask.Tasks P r c) :
    IntegralCriticalHistoryTask.Tasks P r (next P phase c) :=
  IntegralCriticalHistoryTask.child_tasks P id _ phase _ r c h (min_le_right _ _)

noncomputable def objectiveProgram (P : IntegralCriticalHistoryTask.Parameters)
    (F : IntegralCriticalScriptGeneratorBits.Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F) : RecursiveFold.Program :=
  IntegralEulerBits.ObjectiveStage.program (IntegralCriticalScriptEulerBits.source F q)
    (next P .frozenLower) (next P .eulerSum)

theorem objective_certificates (P : IntegralCriticalHistoryTask.Parameters) (a : IntegralCriticalHistoryTask.Access P)
    (F : IntegralCriticalScriptGeneratorBits.Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (h : IntegralCriticalScriptEulerBits.Controls F q) :
    (objectiveProgram P F q).controller.Certificates
      (encQ := Turing.MultiTapeTM.encBits) (encS := RecursiveFold.encState) :=
  IntegralEulerBits.ObjectiveStage.certificates _ (IntegralCriticalScriptEulerBits.access F q h)
    _ _ (next_FP P a .frozenLower) (next_FP P a .eulerSum)

theorem objective_post_packet (S : IntegralEulerBits.Source) (c : List Bool) (x y : ZMod (S.modulus c)) :
    IntegralEulerBits.ObjectiveStage.post S (pair c (pair (residueBits x) (residueBits y))) =
      residueBits (x * (S.allowance c : ZMod (S.modulus c)) - y) := by
  unfold IntegralEulerBits.ObjectiveStage.post
  simp only [pairFst_pair, pairSnd_pair]
  rw [IntegralCriticalLeadingBits.degreePost_packet, IntegralEulerBits.subtractPost_packet]

theorem objective_value (P : IntegralCriticalHistoryTask.Parameters)
    (F : IntegralCriticalScriptGeneratorBits.Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (answer : List Bool → List Bool)
    (hl : ∀ c, answer (next P .frozenLower c) = (IntegralCriticalScriptEulerBits.source F q).toGradient.toFrozen.lowerValue c)
    (hs : ∀ c, answer (next P .eulerSum c) = (IntegralCriticalScriptEulerBits.source F q).sumValue c) (c : List Bool) :
    (objectiveProgram P F q).value answer c = (IntegralCriticalScriptEulerBits.source F q).objectiveValue c :=
  IntegralEulerBits.ObjectiveStage.value_eq _ _ _ answer hl hs c

theorem objective_halted_after (P : IntegralCriticalHistoryTask.Parameters)
    (F : IntegralCriticalScriptGeneratorBits.Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (answer : List Bool → List Bool) (c : List Bool) :
    (objectiveProgram P F q).controller.halted
      (((objectiveProgram P F q).controller.reference answer)^[2] ((objectiveProgram P F q).initial c)) = true :=
  (objectiveProgram P F q).halted_after answer c

theorem objective_output_when_halted (P : IntegralCriticalHistoryTask.Parameters)
    (F : IntegralCriticalScriptGeneratorBits.Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (answer : List Bool → List Bool)
    (hl : ∀ c, answer (next P .frozenLower c) = (IntegralCriticalScriptEulerBits.source F q).toGradient.toFrozen.lowerValue c)
    (hs : ∀ c, answer (next P .eulerSum c) = (IntegralCriticalScriptEulerBits.source F q).sumValue c)
    (c : List Bool) (t : ℕ)
    (hh : (objectiveProgram P F q).controller.halted
      (((objectiveProgram P F q).controller.reference answer)^[t] ((objectiveProgram P F q).initial c)) = true) :
    (objectiveProgram P F q).controller.output
      (((objectiveProgram P F q).controller.reference answer)^[t] ((objectiveProgram P F q).initial c)) =
        (IntegralCriticalScriptEulerBits.source F q).objectiveValue c :=
  IntegralEulerBits.ObjectiveStage.output_when_halted _ _ _ answer hl hs c t hh

theorem objective_state_length (P : IntegralCriticalHistoryTask.Parameters)
    (F : IntegralCriticalScriptGeneratorBits.Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (answer : List Bool → List Bool)
    (hl : ∀ c, answer (next P .frozenLower c) = (IntegralCriticalScriptEulerBits.source F q).toGradient.toFrozen.lowerValue c)
    (hs : ∀ c, answer (next P .eulerSum c) = (IntegralCriticalScriptEulerBits.source F q).sumValue c)
    (c : List Bool) (t : ℕ) :
    (RecursiveFold.encState (((objectiveProgram P F q).controller.reference answer)^[t]
      ((objectiveProgram P F q).initial c))).length ≤
        2 * c.length + 2 * (Turing.MultiTapeTM.encNat 2).length + (BinaryNatCode.encode (F.modulus c)).length + 2 :=
  IntegralEulerBits.ObjectiveStage.state_length _ _ _ answer hl hs c t

theorem objective_requests_iff (P : IntegralCriticalHistoryTask.Parameters)
    (F : IntegralCriticalScriptGeneratorBits.Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (answer : List Bool → List Bool) (c child : List Bool) :
    (objectiveProgram P F q).controller.Requests answer (fun _ => 2) c child ↔
      child = next P .frozenLower c ∨ child = next P .eulerSum c :=
  IntegralEulerBits.ObjectiveStage.requests_iff _ _ _ answer c child

theorem objective_requests_rank (P : IntegralCriticalHistoryTask.Parameters)
    (F : IntegralCriticalScriptGeneratorBits.Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (answer : List Bool → List Bool) (c child : List Bool)
    (hp : IntegralCriticalHistoryTask.isPhase .eulerObjective c)
    (hc : (objectiveProgram P F q).controller.Requests answer (fun _ => 2) c child) :
    IntegralCriticalHistoryTask.rank P child < IntegralCriticalHistoryTask.rank P c := by
  rcases (IntegralEulerBits.ObjectiveStage.requests_iff _ _ _ answer c child).mp hc with rfl | rfl
  · apply next_lower_rank
    change 12 < IntegralCriticalHistoryTask.phase c
    change IntegralCriticalHistoryTask.phase c = 15 at hp
    omega
  · apply next_lower_rank
    change 14 < IntegralCriticalHistoryTask.phase c
    change IntegralCriticalHistoryTask.phase c = 15 at hp
    omega

theorem objective_requests_tasks (P : IntegralCriticalHistoryTask.Parameters)
    (F : IntegralCriticalScriptGeneratorBits.Queries) (q : IntegralCriticalScriptQueryBits.GeneratorQueries F)
    (answer : List Bool → List Bool) (r c child : List Bool) (ht : IntegralCriticalHistoryTask.Tasks P r c)
    (hc : (objectiveProgram P F q).controller.Requests answer (fun _ => 2) c child) :
    IntegralCriticalHistoryTask.Tasks P r child := by
  rcases (IntegralEulerBits.ObjectiveStage.requests_iff _ _ _ answer c child).mp hc with rfl | rfl
  · exact next_tasks P .frozenLower r c ht
  · exact next_tasks P .eulerSum r c ht

end LeanCanny.Algebra.IntegralCriticalFlatEulerBits
