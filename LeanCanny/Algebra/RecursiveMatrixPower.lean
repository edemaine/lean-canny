/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.MatrixPowerRecursiveController

/-! # Ranked graphs of matrix-power tasks and base computations

The entry of one matrix can be the answer of another task. The task rank will
bound this nesting uniformly; leaf answers have a separate native certificate.
-/

@[expose] public section

namespace LeanCanny.Algebra.RecursiveMatrixPower
open MatrixPower MatrixPower.Controller
open LeanCanny.Encoding LeanCanny.Computation

structure Source where
  family : ModularFamily
  access : ModularAccess family
  leaf : List Bool → Bool
  base : List Bool → List Bool
  entryTask : List Bool → List Bool
  answer : List Bool → List Bool
  base_eq : ∀ q, leaf q = true → base q = answer q
  power_eq : ∀ q, leaf q = false → family.value q = answer q
  entry_eq : ∀ q, leaf q = false → ∀ i j,
    answer (entryTask (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val)))) =
      MatrixPower.residueBits (family.matrix q i j)

namespace Source
variable (S : Source)

def ops : Callbacks := modularCallbacks S.access.dimension S.access.modulus (fun _ => [])

def initial (q : List Bool) : List Bool :=
  if S.leaf q then pair q (doneBits (S.base q))
  else initialPacket S.access.exponent S.access.row S.access.col q

def controller : RecursiveController.Controller (List Bool) (List Bool) :=
  RecursiveStage.controller S.ops S.initial S.entryTask

def budget (q : List Bool) : ℕ :=
  if S.leaf q then 0 else work (S.family.dimension q) (S.family.exponent q).size (S.family.exponent q) + 1

theorem initial_power (q : List Bool) (hq : S.leaf q = false) :
    S.initial q = pair q (stateBits (residueBits (m := S.family.modulus q))
      (.eval ⟨(S.family.exponent q).size, S.family.exponent q, S.family.row q, S.family.col q⟩ [])) := by
  simp only [initial, hq, Bool.false_eq_true, ite_false]
  exact initialPacket_encode _ _ _ q _ _ _ _ (S.access.exponent_eq q) (S.access.row_eq q) (S.access.col_eq q)

theorem correctAt (q : List Bool) (hq : S.leaf q = false) :
    CorrectAt (RecursiveStage.oracleCallbacks S.ops S.entryTask S.answer) q (S.family.matrix q) residueBits := by
  let : NeZero (S.family.modulus q) := ⟨S.family.modulus_ne_zero q⟩
  exact modularCallbacks_correctAt _ _ _ q _ _ (S.access.dimension_eq q) (S.access.modulus_eq q) (S.entry_eq q hq)

theorem reference_leaf (q : List Bool) (hq : S.leaf q = true) (t : ℕ) :
    (S.controller.reference S.answer)^[t] (S.initial q) = pair q (doneBits (S.base q)) := by
  induction t with
  | zero => simp only [initial, hq, ite_true, Function.iterate_zero, id_eq]
  | succ t ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [RecursiveController.Controller.reference, controller, RecursiveStage.controller,
      halted, pairSnd_pair, doneBits, List.getElem?_cons_zero, Option.getD_some, ite_true]

theorem budget_halts (q : List Bool) :
    S.controller.halted ((S.controller.reference S.answer)^[S.budget q] (S.initial q)) = true := by
  cases hq : S.leaf q with
  | true =>
    rw [S.reference_leaf q hq]
    simp only [controller, RecursiveStage.controller, halted, pairSnd_pair, doneBits,
      List.getElem?_cons_zero, Option.getD_some]
  | false =>
    have h := RecursiveStage.halted_after S.ops S.initial S.entryTask S.answer q (S.family.matrix q)
      residueBits (S.correctAt q hq) (S.family.exponent q) (S.family.row q) (S.family.col q) (S.initial_power q hq)
    simpa only [budget, hq, Bool.false_eq_true, ite_false, controller] using h

theorem output_correct (q : List Bool) (t : ℕ)
    (hh : S.controller.halted ((S.controller.reference S.answer)^[t] (S.initial q)) = true) :
    S.controller.output ((S.controller.reference S.answer)^[t] (S.initial q)) = S.answer q := by
  cases hq : S.leaf q with
  | true =>
    rw [S.reference_leaf q hq]
    simpa only [controller, RecursiveStage.controller, ModularAccess.valueBits, pairSnd_pair, doneBits,
      List.drop_succ_cons, List.drop_zero] using S.base_eq q hq
  | false =>
    exact (RecursiveStage.output_when_halted S.ops S.initial S.entryTask S.answer q (S.family.matrix q)
      residueBits (S.correctAt q hq) (S.family.exponent q) t (S.family.row q) (S.family.col q)
      (S.initial_power q hq) hh).trans (S.power_eq q hq)

theorem query_indices (q : List Bool) (t : ℕ)
    (hn : S.controller.needs ((S.controller.reference S.answer)^[t] (S.initial q)) = true) :
    S.leaf q = false ∧ ∃ i j : Fin (S.family.dimension q),
      S.controller.query ((S.controller.reference S.answer)^[t] (S.initial q)) =
        S.entryTask (pair q (pair (BinaryNatCode.encode i.val) (BinaryNatCode.encode j.val))) := by
  cases hq : S.leaf q with
  | true =>
    rw [S.reference_leaf q hq] at hn
    simp only [controller, RecursiveStage.controller, needsEntry, pairSnd_pair, doneBits,
      List.getElem?_cons_zero, Option.getD_some, ite_true, Bool.false_eq_true] at hn
  | false =>
    have he := RecursiveStage.reference_iterate S.ops S.initial S.entryTask S.answer q (S.family.matrix q)
      residueBits (S.correctAt q hq) t
      (.eval ⟨(S.family.exponent q).size, S.family.exponent q, S.family.row q, S.family.col q⟩ [])
    rw [← S.initial_power q hq] at he
    change (S.controller.reference S.answer)^[t] (S.initial q) = _ at he
    rw [he] at hn ⊢
    obtain ⟨i, j, hij⟩ := RecursiveStage.entry_query_indices q residueBits _ hn
    exact ⟨rfl, i, j, congrArg S.entryTask hij⟩

theorem state_length (q : List Bool) (t : ℕ) :
    ((S.controller.reference S.answer)^[t] (S.initial q)).length ≤
      2 * q.length + 3 + (S.base q).length +
        64 * ((S.family.dimension q).size + (S.family.exponent q).size + (S.family.modulus q).size + 1) ^ 2 := by
  cases hq : S.leaf q with
  | true =>
    rw [S.reference_leaf q hq]
    simp only [pair_length, doneBits, List.length_cons]
    omega
  | false =>
    let : NeZero (S.family.modulus q) := ⟨S.family.modulus_ne_zero q⟩
    have h := RecursiveStage.modular_state_length S.access.dimension S.access.modulus S.initial S.entryTask
      S.answer q (S.family.modulus q) (S.family.matrix q) (S.correctAt q hq) (S.family.exponent q) t
      (S.family.row q) (S.family.col q) (S.initial_power q hq)
    exact h.trans (by omega)

end Source
end LeanCanny.Algebra.RecursiveMatrixPower
