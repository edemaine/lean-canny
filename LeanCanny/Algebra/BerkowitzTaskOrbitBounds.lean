/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BerkowitzTaskStorage
public import LeanCanny.Computation.ControllerRequests

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

theorem queriesClosed_request (sourceBudget : List Bool → ℕ) (tasks : List Bool → List Bool → Prop)
    (hclosed : QueriesClosed a source sourceBudget tasks) (root q child : List Bool)
    (hq : tasks root q)
    (hr : (controller a source).Requests (answer a) (budget (F := F) sourceBudget) q child) :
    tasks root child := by
  obtain ⟨t, ht, hh, hn, he⟩ := hr
  rw [he]
  exact hclosed root q t hq ht hh hn

theorem factor_requests_iff (g : List Bool → List Bool) (B : List Bool → ℕ)
    (q child : List Bool) (hf : SelectedFactor q) :
    (controller a source).Requests g B q child ↔
      (FactorStage.program a sourceTask momentTask).request (payload q) = true ∧
        child = (FactorStage.program a sourceTask momentTask).query (payload q) := by
  simp only [controller, RecursiveController.Controller.choose_requests_iff,
    hf.1, hf.2.1, hf.2.2, Bool.false_eq_true, ite_false, ite_true,
    RecursiveController.Controller.prepare_requests_iff, SingleCall.Program.requests_iff]

theorem source_requests_iff (g : List Bool → List Bool) (B : List Bool → ℕ)
    (q child : List Bool) (hs : SelectedSource q) :
    (controller a source).Requests g B q child ↔
      source.Requests g (fun _ => B q) (payload q) child := by
  simp only [controller, RecursiveController.Controller.choose_requests_iff,
    hs.1, hs.2.1, hs.2.2.1, hs.2.2.2, Bool.false_eq_true, ite_false,
    RecursiveController.Controller.prepare_requests_iff]

theorem factor_reply_bound (sourceBudget : List Bool → ℕ) (tasks : List Bool → List Bool → Prop)
    (hclosed : QueriesClosed a source sourceBudget tasks) (K : List Bool → ℕ)
    (ha : ∀ root q, tasks root q → (answer a q).length ≤ K root)
    (root q : List Bool) (hq : tasks root q) (hf : SelectedFactor q)
    (hr : (FactorStage.program a sourceTask momentTask).request (payload q) = true) :
    (answer a ((FactorStage.program a sourceTask momentTask).query (payload q))).length ≤ K root := by
  apply ha root _
  apply queriesClosed_request a source sourceBudget tasks hclosed root q _ hq
  exact (factor_requests_iff a source (answer a) (budget (F := F) sourceBudget) q _ hf).mpr ⟨hr, rfl⟩

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
