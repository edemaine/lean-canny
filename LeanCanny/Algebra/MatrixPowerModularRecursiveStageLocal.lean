/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.MatrixPowerModularRecursiveStage
/-! # Matrix-power correctness on the current context

A guarded stage only needs matrix replies for its actual input word.
No reply condition is imposed on skipped or invalid source contexts.
-/
@[expose] public section
namespace LeanCanny.Algebra.MatrixPower.ModularRecursiveStage
open LeanCanny.Encoding LeanCanny.Computation Controller
open Turing.MultiTapeTM
set_option backward.isDefEq.respectTransparency false
variable {F : ModularFamily}
theorem correctAt_local (a : ModularAccess F) (task answer : List Bool → List Bool)
    (c : List Bool)
    (he : ∀ (i j : Fin (F.dimension c)), answer (task (pair c
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) = residueBits (F.matrix c i j))
    : CorrectAt (RecursiveStage.oracleCallbacks (ops a) task answer) c (F.matrix c) residueBits := by
  let : NeZero (F.modulus c) := ⟨F.modulus_ne_zero c⟩
  exact modularCallbacks_correctAt a.dimension a.modulus (answer ∘ task) c (F.modulus c)
    (F.matrix c) (a.dimension_eq c) (a.modulus_eq c) he

theorem halted_after_local (a : ModularAccess F) (task answer : List Bool → List Bool)
    (c : List Bool)
    (he : ∀ (i j : Fin (F.dimension c)), answer (task (pair c
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) = residueBits (F.matrix c i j))
    : (stage a task).halted
      (((stage a task).reference answer)^[clock F c] ((stage a task).initial c)) = true := by
  have HS := RecursiveStage.halted_after (ops a) (initial a) task answer c (F.matrix c) residueBits
    (correctAt_local a task answer c he) (F.exponent c) (F.row c) (F.col c) (initial_eq a c)
  let n := work (F.dimension c) (F.exponent c).size (F.exponent c) + 1
  have HL : n ≤ clock F c := work_le_clock c
  change (stage a task).halted (((stage a task).reference answer)^[n] (initial a c)) = true at HS
  have HF : (stage a task).reference answer (((stage a task).reference answer)^[n] (initial a c)) =
      ((stage a task).reference answer)^[n] (initial a c) := by
    simp only [RecursiveController.Controller.reference, HS, ite_true]
  change (stage a task).halted (((stage a task).reference answer)^[clock F c] (initial a c)) = true
  rw [← Nat.sub_add_cancel HL, Function.iterate_add_apply, Function.iterate_fixed HF]
  exact HS

theorem output_when_halted_local (a : ModularAccess F) (task answer : List Bool → List Bool)
    (c : List Bool)
    (he : ∀ (i j : Fin (F.dimension c)), answer (task (pair c
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) = residueBits (F.matrix c i j))
    (t : ℕ)
    (hh : (stage a task).halted (((stage a task).reference answer)^[t] ((stage a task).initial c)) = true) :
    (stage a task).output (((stage a task).reference answer)^[t] ((stage a task).initial c)) = F.value c :=
  RecursiveStage.output_when_halted (ops a) (initial a) task answer c (F.matrix c) residueBits
    (correctAt_local a task answer c he) (F.exponent c) t (F.row c) (F.col c) (initial_eq a c) hh

theorem state_length_local (a : ModularAccess F) (task answer : List Bool → List Bool)
    (c : List Bool)
    (he : ∀ (i j : Fin (F.dimension c)), answer (task (pair c
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) = residueBits (F.matrix c i j))
    (t : ℕ) :
    (((stage a task).reference answer)^[t] ((stage a task).initial c)).length ≤ stateBound F c := by
  let : NeZero (F.modulus c) := ⟨F.modulus_ne_zero c⟩
  exact RecursiveStage.modular_state_length a.dimension a.modulus (initial a) task answer c
    (F.modulus c) (F.matrix c) (correctAt_local a task answer c he) (F.exponent c) t (F.row c) (F.col c) (initial_eq a c)

theorem requests_in_bounds_local (a : ModularAccess F) (task answer : List Bool → List Bool)
    (c : List Bool)
    (he : ∀ (i j : Fin (F.dimension c)), answer (task (pair c
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) = residueBits (F.matrix c i j))
    (budget : List Bool → ℕ) (child : List Bool)
    (hreq : (stage a task).Requests answer budget c child) :
    ∃ i j : Fin (F.dimension c), child = task (pair c
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) := by
  obtain ⟨t, _ht, _hh, hn, hchild⟩ := hreq
  let s : State (ZMod (F.modulus c)) (F.dimension c) :=
    (MatrixPower.step (F.matrix c))^[t]
      (.eval ⟨(F.exponent c).size, F.exponent c, F.row c, F.col c⟩ [])
  have HO : ((stage a task).reference answer)^[t] ((stage a task).initial c) = pair c (stateBits residueBits s) := by
    change ((RecursiveStage.controller (ops a) (initial a) task).reference answer)^[t] (initial a c) = _
    rw [initial_eq]
    exact RecursiveStage.reference_iterate (ops a) (initial a) task answer c (F.matrix c) residueBits
      (correctAt_local a task answer c he) t _
  change needsEntry (((stage a task).reference answer)^[t] ((stage a task).initial c)) = true at hn
  change child = task (entryInput (((stage a task).reference answer)^[t] ((stage a task).initial c))) at hchild
  rw [HO] at hn hchild
  obtain ⟨i, j, hq⟩ := RecursiveStage.entry_query_indices c residueBits s hn
  exact ⟨i, j, hchild.trans (congrArg task hq)⟩

theorem context_iterate_local (a : ModularAccess F) (task answer : List Bool → List Bool)
    (c : List Bool)
    (he : ∀ (i j : Fin (F.dimension c)), answer (task (pair c
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) = residueBits (F.matrix c i j))
    (t : ℕ) :
    pairFst (((stage a task).reference answer)^[t] ((stage a task).initial c)) = c := by
  change pairFst (((RecursiveStage.controller (ops a) (initial a) task).reference answer)^[t] (initial a c)) = c
  rw [initial_eq, RecursiveStage.reference_iterate (ops a) (initial a) task answer c (F.matrix c) residueBits
    (correctAt_local a task answer c he), pairFst_pair]

end LeanCanny.Algebra.MatrixPower.ModularRecursiveStage
