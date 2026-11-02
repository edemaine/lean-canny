/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Encoding.FlatAffineExceptionalSuppliedRules
public import LeanCanny.Algebra.IntegralMixedSuppliedHeightCells
/-! # A total supplied-mask full history extends an original integer bank

Arbitrary advice determines its own coarse rule and sweep. No equality to
original level flags is required by the Data constructor. The cut kind and
written truncation degree are immutable original syntax parameters.
-/
@[expose] public section
namespace LeanCanny.Encoding.FlatAffineExceptionalSuppliedData
open LeanCanny.Algebra LeanCanny.Computation MatrixPower IntegralCriticalHistoryTask
open FlatAffineFullSourceTower (Inputs arity)
open FlatAffineCompleteRootStages (next)
open IntegralMixedHistory IntegralMixedFullHistoryScript
open FlatAffineExceptionalSuppliedRules (Source)
open scoped Classical
set_option backward.isDefEq.respectTransparency false

def parameters (P : Parameters) {F : Inputs} (S : Source F) : Parameters :=
  { P with ambient root := F.source.dim (S.input root) + 3 }

theorem parameters_access (P : Parameters) (a : Access P) {F : Inputs} (hF : F.Access)
    (S : Source F) (hS : FlatAffineExceptionalSuppliedRules.Access S) : Access (parameters P S) where
  cap := a.cap
  width := a.width
  ambient := (((FlatAffineFullSourceTower.arity_unary hF).comp hS.input).sub (UnaryFn.const 1)).of_eq
    (fun root => by simp only [arity, parameters]; omega)
  sourceWidth := a.sourceWidth
  degree := a.degree
  height := a.height
  modulusBound := a.modulusBound

noncomputable def selection (P : Parameters) {F : Inputs} (S : Source F)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (base : IntegralMixedFullHistoryFamilyBits.Data (parameters P S))
    (kind : (root : List Bool) → IntegralMixedRelativeCuts.Kind (base.spatial root) (FlatAffineExceptionalSuppliedRules.sweep S C root))
    (degree : List Bool → ℕ)
    (hd : ∀ root, degree root ≤ IntegralMixedExceptionalBounds.auxiliaryCap ((parameters P S).ambient root + 1) (base.spatial root).degree)
    (root : List Bool) : IntegralMixedFullHistoryFamilyBits.Selection (base.spatial root) :=
  ⟨FlatAffineExceptionalSuppliedRules.sweep S C root, kind root, degree root, hd root⟩

noncomputable def data (P : Parameters) {F : Inputs} (S : Source F)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (base : IntegralMixedFullHistoryFamilyBits.Data (parameters P S))
    (kind : (root : List Bool) → IntegralMixedRelativeCuts.Kind (base.spatial root) (FlatAffineExceptionalSuppliedRules.sweep S C root))
    (degree : List Bool → ℕ)
    (hd : ∀ root, degree root ≤ IntegralMixedExceptionalBounds.auxiliaryCap ((parameters P S).ambient root + 1) (base.spatial root).degree)
    (room : ∀ root, (base.rules root).length + 4 ≤ P.cap root + 1) : IntegralMixedFullHistoryFamilyBits.Data (parameters P S) :=
  { base with
    rules root := .cut (FlatAffineExceptionalSuppliedRules.sweep S C root) (kind root) (degree root) (hd root)
      ((hd root).trans (base.scalar_cap root)) :: .critical (FlatAffineExceptionalSuppliedRules.coarse S root) :: base.rules root
    room root := by simpa only [List.length_cons, parameters] using room root
    fallback key := selection P S C base kind degree hd (pairFst key) }

theorem creating_eq (P : Parameters) {F : Inputs} (S : Source F)
    (C : FlatAffinePowerPositive.ConeCertificate (next F)) (base : IntegralMixedFullHistoryFamilyBits.Data (parameters P S))
    (kind : (root : List Bool) → IntegralMixedRelativeCuts.Kind (base.spatial root) (FlatAffineExceptionalSuppliedRules.sweep S C root))
    (degree : List Bool → ℕ)
    (hd : ∀ root, degree root ≤ IntegralMixedExceptionalBounds.auxiliaryCap ((parameters P S).ambient root + 1) (base.spatial root).degree)
    (room : ∀ root, (base.rules root).length + 4 ≤ P.cap root + 1) (key : List Bool) :
    IntegralMixedFullHistoryFamilyBits.creating (parameters P S) (data P S C base kind degree hd room) key =
      if IntegralMixedFullHistoryFamilyBits.prefixLength (parameters P S) key < (base.rules (pairFst key)).length then
        IntegralMixedFullHistoryFamilyBits.creating (parameters P S) base key
      else if IntegralMixedFullHistoryFamilyBits.prefixLength (parameters P S) key = (base.rules (pairFst key)).length then
        some (.critical (FlatAffineExceptionalSuppliedRules.coarse S (pairFst key)))
      else if IntegralMixedFullHistoryFamilyBits.prefixLength (parameters P S) key = (base.rules (pairFst key)).length + 1 then
        some (.cut (FlatAffineExceptionalSuppliedRules.sweep S C (pairFst key)) (kind (pairFst key)) (degree (pairFst key)) (hd (pairFst key))
          ((hd (pairFst key)).trans (base.scalar_cap (pairFst key)))) else none := by
  let b := IntegralMixedFullHistoryFamilyBits.prefixLength (parameters P S) key
  let n := (base.rules (pairFst key)).length
  change chronological ((data P S C base kind degree hd room).rules (pairFst key)) b = _
  simp only [data, chronological, List.reverse_cons, List.append_assoc]
  by_cases hb : b < n
  · rw [ite_eq_left hb, List.getElem?_append_left (by simpa only [List.length_reverse] using hb)]
    rfl
  · rw [ite_eq_right hb, List.getElem?_append_right (by simpa only [List.length_reverse] using Nat.le_of_not_gt hb)]
    change _ = if b = n then _ else if b = n + 1 then _ else none
    rw [List.length_reverse]
    by_cases h0 : b = n
    · simp only [h0, n, Nat.sub_self, List.singleton_append, List.getElem?_cons_zero, ite_true]
    · rw [ite_eq_right h0]
      by_cases h1 : b = n + 1
      · simp only [h1, n, Nat.add_sub_cancel_left, List.singleton_append, List.getElem?_cons_succ, List.getElem?_cons_zero, ite_true]
      · rw [ite_eq_right h1]
        apply List.getElem?_eq_none
        change 2 ≤ b - n
        omega
end LeanCanny.Encoding.FlatAffineExceptionalSuppliedData
