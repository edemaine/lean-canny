/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.IntegralPowerProductSpace
public import LeanCanny.Algebra.MatrixProductRecursiveStage

/-! # Recursive products and powers of retained algebra elements

The product uses the layered matrix of actual old multiplication matrices.
The factor-power stage routes each matrix entry to the original factor and
old basis ranks. Metadata and task writers suffice for both certificates;
there is no factor evaluator among their native assumptions.
-/

@[expose] public section
namespace LeanCanny.Algebra.IntegralPowerProductBits.ProductStage
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM
set_option backward.isDefEq.respectTransparency false

noncomputable def controller (F : Family) (a : Access F) (task : List Bool → List Bool) :=
  MatrixProductBits.RecursiveStage.controller (productFamily F) (productAccess F a) task

theorem certificates (F : Family) (a : Access F) (task : List Bool → List Bool) (ht : task ∈ FP) :
    (controller F a task).Certificates (encQ := encBits) (encS := encBits) :=
  MatrixProductBits.RecursiveStage.certificates (productFamily F) (productAccess F a) task ht

theorem clock_binary (F : Family) (a : Access F) : BinaryFn (ModularRecursiveStage.clock (productFamily F).power) :=
  MatrixProductBits.RecursiveStage.clock_binary (productFamily F) (productAccess F a)

theorem stateBound_unary (F : Family) (a : Access F) : UnaryFn (ModularRecursiveStage.stateBound (productFamily F).power) :=
  MatrixProductBits.RecursiveStage.stateBound_unary (productFamily F) (productAccess F a)

noncomputable def entryProgram (F : Family) (task : List Bool → List Bool) :=
  MatrixProductBits.RecursiveStage.entryProgram (productFamily F) task

theorem entry_controls (F : Family) (a : Access F) (task : List Bool → List Bool) (ht : task ∈ FP) :
    (entryProgram F task).Controls :=
  MatrixProductBits.RecursiveStage.entry_controls (productFamily F) (productAccess F a) task ht

theorem entry_value (F : Family) (a : Access F) (task answer : List Bool → List Bool)
    (he : ∀ q, answer (task q) = (powerFamily F).value q) (p : List Bool) :
    (entryProgram F task).value answer p = MatrixProductBits.powerEntry (productFamily F) (productAccess F a) p :=
  MatrixProductBits.RecursiveStage.entry_value (productFamily F) (productAccess F a) task answer he p

theorem entry_requests_in_bounds (F : Family) (task answer : List Bool → List Bool)
    (budget : List Bool → ℕ) (c child : List Bool) (i j : Fin ((F.count c + 1) * F.rank c))
    (hreq : (entryProgram F task).controller.Requests answer budget
      (pair c (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) child) :
    ∃ s : Fin (F.count c), ∃ r t : Fin (F.rank c), child = task (pair c
      (pair (BinaryNatCode.encode s.val) (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))) :=
  MatrixProductBits.RecursiveStage.entry_requests_in_bounds (productFamily F) task answer budget c child i j hreq

variable (F : Family) (a : Access F) (task answer : List Bool → List Bool)
    (he : ∀ c (i j : Fin ((productFamily F).power.dimension c)), answer (task (pair c
      (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
        residueBits ((productFamily F).power.matrix c i j))
include he

theorem halted_after (c : List Bool) :
    (controller F a task).halted (((controller F a task).reference answer)^[ModularRecursiveStage.clock (productFamily F).power c]
      ((controller F a task).initial c)) = true :=
  MatrixProductBits.RecursiveStage.halted_after (productFamily F) (productAccess F a) task answer he c

theorem output_when_halted (c : List Bool) (t : ℕ)
    (hh : (controller F a task).halted (((controller F a task).reference answer)^[t] ((controller F a task).initial c)) = true) :
    (controller F a task).output (((controller F a task).reference answer)^[t] ((controller F a task).initial c)) = F.value c :=
  (MatrixProductBits.RecursiveStage.output_when_halted (productFamily F) (productAccess F a) task answer he c t hh).trans
    (congrFun (product_value F) c)

theorem state_length (c : List Bool) (t : ℕ) :
    (((controller F a task).reference answer)^[t] ((controller F a task).initial c)).length ≤
      ModularRecursiveStage.stateBound (productFamily F).power c :=
  MatrixProductBits.RecursiveStage.state_length (productFamily F) (productAccess F a) task answer he c t

end LeanCanny.Algebra.IntegralPowerProductBits.ProductStage

namespace LeanCanny.Algebra.IntegralPowerProductBits.FactorStage
open LeanCanny.Encoding LeanCanny.Computation MatrixPower Turing.MultiTapeTM
set_option backward.isDefEq.respectTransparency false

noncomputable def controller (F : Family) (a : Access F) (task : List Bool → List Bool) :=
  ModularRecursiveStage.stage (powerAccess F a) (task ∘ entryQuery)

theorem certificates (F : Family) (a : Access F) (task : List Bool → List Bool) (ht : task ∈ FP) :
    (controller F a task).Certificates (encQ := encBits) (encS := encBits) :=
  ModularRecursiveStage.certificates (powerAccess F a) (power_controls F a) _ (mem_FP_comp entryQuery_FP ht)

theorem reply_correct (F : Family) (a : Access F) (task answer : List Bool → List Bool)
    (he : ∀ p, answer (task p) = a.entry p) :
    ∀ q (r t : Fin ((powerFamily F).dimension q)),
      answer ((task ∘ entryQuery) (pair q (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))) =
        residueBits ((powerFamily F).matrix q r t) := by
  intro q r t
  rw [Function.comp_apply, he]
  exact (powerAccess F a).entry_eq q r t

theorem clock_binary (F : Family) (a : Access F) : BinaryFn (ModularRecursiveStage.clock (powerFamily F)) :=
  ModularRecursiveStage.clock_binary (powerAccess F a) (power_controls F a)

theorem stateBound_unary (F : Family) (a : Access F) : UnaryFn (ModularRecursiveStage.stateBound (powerFamily F)) :=
  ModularRecursiveStage.stateBound_unary (powerAccess F a) (power_controls F a)

variable (F : Family) (a : Access F) (task answer : List Bool → List Bool) (he : ∀ p, answer (task p) = a.entry p)
include he

theorem halted_after (q : List Bool) :
    (controller F a task).halted (((controller F a task).reference answer)^[ModularRecursiveStage.clock (powerFamily F) q]
      ((controller F a task).initial q)) = true :=
  ModularRecursiveStage.halted_after (powerAccess F a) _ answer (reply_correct F a task answer he) q

theorem output_when_halted (q : List Bool) (t : ℕ)
    (hh : (controller F a task).halted (((controller F a task).reference answer)^[t] ((controller F a task).initial q)) = true) :
    (controller F a task).output (((controller F a task).reference answer)^[t] ((controller F a task).initial q)) = (powerFamily F).value q :=
  ModularRecursiveStage.output_when_halted (powerAccess F a) _ answer (reply_correct F a task answer he) q t hh

theorem state_length (q : List Bool) (t : ℕ) :
    (((controller F a task).reference answer)^[t] ((controller F a task).initial q)).length ≤
      ModularRecursiveStage.stateBound (powerFamily F) q :=
  ModularRecursiveStage.state_length (powerAccess F a) _ answer (reply_correct F a task answer he) q t

theorem requests_in_bounds (budget : List Bool → ℕ) (q child : List Bool)
    (hreq : (controller F a task).Requests answer budget q child) :
    ∃ r t : Fin (F.rank (pairFst q)), child = task (pair (pairFst q)
      (pair (BinaryNatCode.encode (Nat.fromBitsLE (factorWord q)))
        (pair (BinaryNatCode.encode r.val) (BinaryNatCode.encode t.val)))) := by
  obtain ⟨r, t, h⟩ := ModularRecursiveStage.requests_in_bounds (powerAccess F a) _ answer
    (reply_correct F a task answer he) budget q child hreq
  exact ⟨r, t, h.trans (congrArg task (entryQuery_packet q r.val t.val))⟩

end LeanCanny.Algebra.IntegralPowerProductBits.FactorStage
