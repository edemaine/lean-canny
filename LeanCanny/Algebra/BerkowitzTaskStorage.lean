/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BerkowitzTaskDispatch

/-! # Exact dispatch overhead and common logical budgets

Only the selected stage evolves. Inactive encodings are constants, including
the supplied source-state default, and every stage appears in at most two
copies under framing.
-/

@[expose] public section

namespace LeanCanny.Algebra.BerkowitzPolynomial.TaskDispatch
open LeanCanny.Encoding LeanCanny.Computation
open RecursiveController.Controller Turing.MultiTapeTM

private theorem choice_length {A B : Type} [Inhabited A] [Inhabited B]
    (eA : A ↪ List Bool) (eB : B ↪ List Bool) (select : List Bool → Bool)
    (C : RecursiveController.Controller (List Bool) A) (D : RecursiveController.Controller (List Bool) B)
    (g : List Bool → List Bool) (q : List Bool) (t : ℕ) :
    (encChoice eA eB (((choose select C D).reference g)^[t] ((choose select C D).initial q))).length =
      if select q then 4 + 2 * (eA ((C.reference g)^[t] (C.initial q))).length + (eB default).length
      else 4 + 2 * (eA default).length + (eB ((D.reference g)^[t] (D.initial q))).length := by
  cases hs : select q with
  | true =>
    have hi : (choose select C D).initial q = (true, C.initial q, default) := by simp only [choose, hs, ite_true]
    rw [hi, choose_iterate_true]
    simp only [ite_true, encChoice, length_encPair, encBool_apply, List.length_singleton]
    omega
  | false =>
    have hi : (choose select C D).initial q = (false, default, D.initial q) := by
      simp only [choose, hs, Bool.false_eq_true, ite_false]
    rw [hi, choose_iterate_false]
    simp only [Bool.false_eq_true, ite_false, encChoice, length_encPair, encBool_apply, List.length_singleton]
    omega

private theorem prepared_orbit {S : Type}
    (C : RecursiveController.Controller (List Bool) S) (input g : List Bool → List Bool) (q : List Bool) (t : ℕ) :
    ((prepare C input).reference g)^[t] ((prepare C input).initial q) =
      (C.reference g)^[t] (C.initial (input q)) := rfl

private theorem default_single : (SingleCall.encState default).length = 4 := rfl
private theorem default_word : (default : List Bool).length = 0 := rfl

private theorem choice_pair_length {A B : Type} (eA : A ↪ List Bool) (eB : B ↪ List Bool)
    (flag : Bool) (a : A) (b : B) :
    (encChoice eA eB (flag, a, b)).length = 4 + 2 * (eA a).length + (eB b).length := by
  simp only [encChoice, length_encPair, encBool_apply, List.length_singleton]
  omega

private theorem default_remainder {S : Type} [Inhabited S] (eS : S ↪ List Bool) :
    (encChoice encBits eS default).length = 4 + (eS default).length := by
  simp only [encChoice, length_encPair, encBool_apply, List.length_singleton, encBits_apply]
  change 2 * 1 + 1 + (2 * 0 + 1 + (eS default).length) = _
  omega

private theorem default_factor {S : Type} [Inhabited S] (eS : S ↪ List Bool) :
    (encChoice SingleCall.encState (encChoice encBits eS) default).length = 16 + (eS default).length := by
  change (encChoice SingleCall.encState (encChoice encBits eS) (false, default, default)).length = _
  rw [choice_pair_length, default_single, default_remainder]
  omega

variable {F : ModularFamily} (a : ModularAccess F)
attribute [local irreducible] ModularAccess.factorValue ModularFamily.value PolynomialMoment.ModularFamily.value
  MatrixPower.Controller.halted MatrixPower.Controller.needsEntry MatrixPower.Controller.initialPacket
  FactorStage.program payload isZero isDeterminant isFactor isMoment
  BinaryNat.div BinaryNat.mod BinaryNat.normalize BinaryNat.mul BinaryNat.add BinaryNat.sub BinaryNat.succ

private theorem single_initial (P : SingleCall.Program) : P.controller.initial = SingleCall.Program.initial := rfl
private theorem determinant_initial : (DeterminantStage.controller a factorTask []).initial = DeterminantStage.initial a := rfl
private theorem moment_initial : (MomentStage.controller a sourceTask []).initial = MomentStage.initial a := rfl

theorem encoded_length {S : Type} [Inhabited S] (eS : S ↪ List Bool)
    (source : RecursiveController.Controller (List Bool) S) (g : List Bool → List Bool) (q : List Bool) (t : ℕ) :
    (encState eS (((controller a source).reference g)^[t] ((controller a source).initial q))).length =
      if isZero q then 24 + 2 * (SingleCall.encState
        ((zeroProgram.controller.reference g)^[t] (SingleCall.Program.initial q))).length + (eS default).length
      else if isDeterminant q then 32 + 2 *
        (((DeterminantStage.controller a factorTask []).reference g)^[t] (DeterminantStage.initial a (payload q))).length + (eS default).length
      else if isFactor q then 24 + 2 * (SingleCall.encState
        (((FactorStage.program a sourceTask momentTask).controller.reference g)^[t] (SingleCall.Program.initial (payload q)))).length + (eS default).length
      else if isMoment q then 32 + 2 *
        (((MomentStage.controller a sourceTask []).reference g)^[t] (MomentStage.initial a (payload q))).length + (eS default).length
      else 32 + (eS ((source.reference g)^[t] (source.initial (payload q)))).length := by
  simp only [controller, encState, choice_length, prepared_orbit, single_initial,
    determinant_initial, moment_initial, default_single, default_remainder, default_factor, encBits_apply, default_word]
  split_ifs <;> omega

def SelectedDeterminant (q : List Bool) : Prop := isZero q = false ∧ isDeterminant q = true
def SelectedFactor (q : List Bool) : Prop := isZero q = false ∧ isDeterminant q = false ∧ isFactor q = true
def SelectedMoment (q : List Bool) : Prop := isZero q = false ∧ isDeterminant q = false ∧ isFactor q = false ∧ isMoment q = true
def SelectedSource (q : List Bool) : Prop := isZero q = false ∧ isDeterminant q = false ∧ isFactor q = false ∧ isMoment q = false

theorem encoded_length_le {S : Type} [Inhabited S] (eS : S ↪ List Bool)
    (source : RecursiveController.Controller (List Bool) S) (g : List Bool → List Bool) (q : List Bool) (t L : ℕ)
    (hz : isZero q = true → (SingleCall.encState ((zeroProgram.controller.reference g)^[t] (SingleCall.Program.initial q))).length ≤ L)
    (hd : SelectedDeterminant q → (((DeterminantStage.controller a factorTask []).reference g)^[t]
      (DeterminantStage.initial a (payload q))).length ≤ L)
    (hf : SelectedFactor q → (SingleCall.encState (((FactorStage.program a sourceTask momentTask).controller.reference g)^[t]
      (SingleCall.Program.initial (payload q)))).length ≤ L)
    (hm : SelectedMoment q → (((MomentStage.controller a sourceTask []).reference g)^[t]
      (MomentStage.initial a (payload q))).length ≤ L)
    (hs : SelectedSource q → (eS ((source.reference g)^[t] (source.initial (payload q)))).length ≤ L) :
    (encState eS (((controller a source).reference g)^[t] ((controller a source).initial q))).length ≤
      32 + 2 * L + (eS default).length := by
  rw [encoded_length]
  split_ifs with h0 h1 h2 h3
  · have h := hz h0; omega
  · have h := hd ⟨Bool.eq_false_iff.mpr h0, h1⟩; omega
  · have h := hf ⟨Bool.eq_false_iff.mpr h0, Bool.eq_false_iff.mpr h1, h2⟩; omega
  · have h := hm ⟨Bool.eq_false_iff.mpr h0, Bool.eq_false_iff.mpr h1, Bool.eq_false_iff.mpr h2, h3⟩; omega
  · have h := hs ⟨Bool.eq_false_iff.mpr h0, Bool.eq_false_iff.mpr h1, Bool.eq_false_iff.mpr h2, Bool.eq_false_iff.mpr h3⟩; omega

def determinantFields (c : List Bool) : ℕ :=
  ((F.dimension c + 1) * (F.dimension c + 1) * (F.degree c + 1)).size + (F.dimension c).size + (F.modulus c).size

def momentFields (p : List Bool) : ℕ :=
  ((trailingDimension F (pairFst p) + 2) * (Nat.fromBitsLE (pairSnd p) + 1)).size +
    (momentExponent F (pairFst p) + 2).size + (F.modulus (pairFst (pairFst p))).size

private theorem work_bound (n e M : ℕ) (h : n.size + e.size ≤ M) :
    MatrixPower.work n e.size e + 1 ≤ 2 ^ ((M + 2) * M + 1) := by
  have hw := MatrixPower.work_add_one_le_two_pow n e.size e
  have he : (n.size + 2) * e.size + 1 ≤ (M + 2) * M + 1 :=
    Nat.add_le_add_right (Nat.mul_le_mul (by omega) (by omega)) 1
  exact hw.trans (Nat.pow_le_pow_right (by decide) he)

theorem budget_le (sourceBudget : List Bool → ℕ) (q : List Bool) (M N : ℕ)
    (hd : SelectedDeterminant q → determinantFields (F := F) (payload q) ≤ M)
    (hm : SelectedMoment q → momentFields (F := F) (payload q) ≤ M)
    (hs : SelectedSource q → sourceBudget (payload q) ≤ N) :
    budget (F := F) sourceBudget q ≤ N + 2 ^ ((M + 2) * M + 1) := by
  unfold budget
  split_ifs with h0 h1 h2 h3
  · exact Nat.zero_le _
  · have hb := hd ⟨Bool.eq_false_iff.mpr h0, h1⟩
    have hw := work_bound ((F.dimension (payload q) + 1) * (F.dimension (payload q) + 1) * (F.degree (payload q) + 1))
      (F.dimension (payload q)) M (by dsimp only [determinantFields] at hb; omega)
    exact hw.trans (Nat.le_add_left _ _)
  · have hp : 1 ≤ 2 ^ ((M + 2) * M + 1) := Nat.one_le_pow _ _ (by decide)
    omega
  · have hb := hm ⟨Bool.eq_false_iff.mpr h0, Bool.eq_false_iff.mpr h1, Bool.eq_false_iff.mpr h2, h3⟩
    have hw := work_bound ((trailingDimension F (pairFst (payload q)) + 2) * (Nat.fromBitsLE (pairSnd (payload q)) + 1))
      (momentExponent F (pairFst (payload q)) + 2) M (by dsimp only [momentFields] at hb; omega)
    exact hw.trans (Nat.le_add_left _ _)
  · have hb := hs ⟨Bool.eq_false_iff.mpr h0, Bool.eq_false_iff.mpr h1, Bool.eq_false_iff.mpr h2, Bool.eq_false_iff.mpr h3⟩
    exact hb.trans (Nat.le_add_right _ _)

end LeanCanny.Algebra.BerkowitzPolynomial.TaskDispatch
