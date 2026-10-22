/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BerkowitzTaskStorage

/-! # Storage bounds for reachable mixed-stage tasks

Query closure supplies the answer bound for a factor's selected child. No
bound is needed for an unrequested diagonal or moment answer.
-/

@[expose] public section

namespace LeanCanny.Algebra.BerkowitzPolynomial.TaskDispatch
open LeanCanny.Encoding LeanCanny.Computation
open Turing.MultiTapeTM

variable {F : ModularFamily} (a : ModularAccess F)
variable {S : Type} [Inhabited S] (source : RecursiveController.Controller (List Bool) S)
attribute [local irreducible] FactorStage.program ModularAccess.factorValue ModularFamily.value
  PolynomialMoment.ModularFamily.value MatrixPower.Controller.halted MatrixPower.Controller.needsEntry
  payload isZero isDeterminant isFactor isMoment
  BinaryNat.div BinaryNat.mod BinaryNat.normalize BinaryNat.mul BinaryNat.add BinaryNat.sub BinaryNat.succ

def QueriesClosed (sourceBudget : List Bool → ℕ) (tasks : List Bool → List Bool → Prop) : Prop :=
  ∀ root q t, tasks root q → t ≤ budget (F := F) sourceBudget q →
    (controller a source).halted (((controller a source).reference (answer a))^[t] ((controller a source).initial q)) = false →
    (controller a source).needs (((controller a source).reference (answer a))^[t] ((controller a source).initial q)) = true →
    tasks root ((controller a source).query
      (((controller a source).reference (answer a))^[t] ((controller a source).initial q)))

theorem factor_reply_bound (sourceBudget : List Bool → ℕ) (tasks : List Bool → List Bool → Prop)
    (hclosed : QueriesClosed a source sourceBudget tasks) (K : List Bool → ℕ)
    (ha : ∀ root q, tasks root q → (answer a q).length ≤ K root)
    (root q : List Bool) (hq : tasks root q) (hf : SelectedFactor q)
    (hr : (FactorStage.program a sourceTask momentTask).request (payload q) = true) :
    (answer a ((FactorStage.program a sourceTask momentTask).query (payload q))).length ≤ K root := by
  have hh : (controller a source).halted
      (((controller a source).reference (answer a))^[0] ((controller a source).initial q)) = false := by
    rw [halted_iterate]
    simp only [hf.1, hf.2.1, hf.2.2, Bool.false_eq_true, ite_false, ite_true, Function.iterate_zero, id_eq]
    change Bool.not ((FactorStage.program a sourceTask momentTask).request (payload q)) = false
    rw [hr]
    rfl
  have hn : (controller a source).needs
      (((controller a source).reference (answer a))^[0] ((controller a source).initial q)) = true := by
    rw [needs_iterate]
    simpa only [hf.1, hf.2.1, hf.2.2, Bool.false_eq_true, ite_false, ite_true, Function.iterate_zero,
      id_eq, SingleCall.Program.controller, SingleCall.Program.initial] using hr
  have he : (controller a source).query
      (((controller a source).reference (answer a))^[0] ((controller a source).initial q)) =
        (FactorStage.program a sourceTask momentTask).query (payload q) := by
    rw [query_iterate]
    simp only [hf.1, hf.2.1, hf.2.2, Bool.false_eq_true, ite_false, ite_true, Function.iterate_zero,
      id_eq, SingleCall.Program.controller, SingleCall.Program.initial]
  have hc := hclosed root q 0 hq (Nat.zero_le _) hh hn
  rw [he] at hc
  exact ha root _ hc

def stageBound (K M V : ℕ) : ℕ := 3 * K + 4 + 64 * (M + 1) ^ 2 + V

private theorem payload_length (q : List Bool) : (payload q).length ≤ q.length := by
  simp only [payload, List.length_drop]
  omega

theorem orbit_length_bound (eS : S ↪ List Bool)
    (sourceBudget : List Bool → ℕ) (tasks : List Bool → List Bool → Prop)
    (hclosed : QueriesClosed a source sourceBudget tasks) (K M V : List Bool → ℕ)
    (hword : ∀ root q, tasks root q → q.length ≤ K root)
    (hanswer : ∀ root q, tasks root q → (answer a q).length ≤ K root)
    (hdet : ∀ root q, tasks root q → SelectedDeterminant q → determinantFields (F := F) (payload q) ≤ M root)
    (hmoment : ∀ root q, tasks root q → SelectedMoment q → momentFields (F := F) (payload q) ≤ M root)
    (hsource : ∀ root q, tasks root q → SelectedSource q → ∀ t ≤ sourceBudget (payload q),
      (eS ((source.reference (answer a))^[t] (source.initial (payload q)))).length ≤ V root)
    (root q : List Bool) (hq : tasks root q) (t : ℕ) (ht : t ≤ budget (F := F) sourceBudget q) :
    (encState eS (((controller a source).reference (answer a))^[t] ((controller a source).initial q))).length ≤
      32 + 2 * stageBound (K root) (M root) (V root) + (eS default).length := by
  have hq' := hword root q hq
  have hp := (payload_length q).trans hq'
  apply encoded_length_le a eS source (answer a) q t (stageBound (K root) (M root) (V root))
  · intro _
    have hz := zeroProgram.state_length_of_bound (answer a) q t 0 (by
      intro hh
      simp only [zeroProgram, Bool.false_eq_true] at hh)
    dsimp only [stageBound]
    omega
  · intro hd
    have hs := DeterminantStage.state_length a factorTask (answer a) [] (answer_factor a) (answer_zero a) (payload q) t
    have hb := hdet root q hq hd
    have hw := Nat.mul_le_mul_left 64 (Nat.pow_le_pow_left (Nat.add_le_add_right hb 1) 2)
    change _ ≤ 2 * (payload q).length + 2 + 64 * (determinantFields (F := F) (payload q) + 1) ^ 2 at hs
    dsimp only [stageBound]
    omega
  · intro hf
    have hs := (FactorStage.program a sourceTask momentTask).state_length_of_bound (answer a) (payload q) t (K root)
      (factor_reply_bound a source sourceBudget tasks hclosed K hanswer root q hq hf)
    dsimp only [stageBound]
    omega
  · intro hm
    have hs := MomentStage.state_length a sourceTask (answer a) [] (answer_source a) (answer_zero a) (payload q) t
    have hb := hmoment root q hq hm
    have hw := Nat.mul_le_mul_left 64 (Nat.pow_le_pow_left (Nat.add_le_add_right hb 1) 2)
    change _ ≤ 2 * (payload q).length + 2 + 64 * (momentFields (F := F) (payload q) + 1) ^ 2 at hs
    dsimp only [stageBound]
    omega
  · intro hs
    have ht' : t ≤ sourceBudget (payload q) := by
      simpa only [budget, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2, Bool.false_eq_true, ite_false] using ht
    have hv := hsource root q hq hs t ht'
    dsimp only [stageBound]
    omega

end LeanCanny.Algebra.BerkowitzPolynomial.TaskDispatch
