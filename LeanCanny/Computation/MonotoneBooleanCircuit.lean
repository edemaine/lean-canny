/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Computation.BooleanCircuitValues
public import Mathlib.Data.List.Forall2
/-! # AND/OR circuits are monotone in their indexed atomic predicates -/
@[expose] public section
namespace LeanCanny.Computation.MonotoneBooleanCircuit
open BooleanCircuitSpace LeanCanny.Encoding
open scoped Classical

def Le (a b : Bool) : Prop := a=true → b=true

theorem operation_mono {k : ℕ} (hk : k≠3) {a b l L r R : Bool}
    (ha : Le a b) (hl : Le l L) (hr : Le r R) : Le (operation k a l r) (operation k b L R) := by
  intro H
  simp only [operation,decide_eq_true_eq] at H ⊢
  rcases H with H | ⟨H,HA⟩ | ⟨H,_⟩ | ⟨H,HL,HR⟩ | ⟨H,HL⟩
  · exact Or.inl H
  · exact Or.inr (Or.inl ⟨H,ha HA⟩)
  · exact (hk H).elim
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨H,hl HL,hr HR⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨H,HL.imp hl hr⟩)))

theorem lookup_mono {a b : List Bool} (H : List.Forall₂ Le a b) (i : ℕ) :
    Le (a[i]?.getD false) (b[i]?.getD false) := by
  induction H generalizing i with
  | nil => simp [Le]
  | @cons x y a b Hxy Htail IH =>
    cases i with
    | zero => exact Hxy
    | succ i => exact IH i

theorem values_mono (F : Family) (a b : List Bool → Bool) (c : List Bool)
    (htags : ∀ i, F.tag (pair c (BinaryNatCode.encode i))≠3)
    (ha : ∀ i, Le (a (pair c (BinaryNatCode.encode i))) (b (pair c (BinaryNatCode.encode i))))
    (n : ℕ) : List.Forall₂ Le (values F a c n) (values F b c n) := by
  induction n with
  | zero => exact .nil
  | succ n IH =>
    apply List.rel_append IH
    exact .cons (operation_mono (htags n) (ha n) (lookup_mono IH _) (lookup_mono IH _)) .nil

theorem value_mono (F : Family) (a b : List Bool → Bool) (c : List Bool)
    (htags : ∀ i, F.tag (pair c (BinaryNatCode.encode i))≠3)
    (ha : ∀ i, Le (a (pair c (BinaryNatCode.encode i))) (b (pair c (BinaryNatCode.encode i)))) :
    Le (value F a c) (value F b c) := lookup_mono (values_mono F a b c htags ha _) _

noncomputable def atom (F : Family) (c : List Bool) (a : Fin (F.count c) → Prop) (q : List Bool) : Bool :=
  decide (if hi : Nat.fromBitsLE (pairSnd q)<F.count c then a ⟨Nat.fromBitsLE (pairSnd q),hi⟩ else False)

noncomputable def predicate (F : Family) (c : List Bool) (a : Fin (F.count c) → Prop) : Prop :=
  value F (atom F c a) c=true

theorem predicate_mono (F : Family) (c : List Bool)
    (htags : ∀ i, F.tag (pair c (BinaryNatCode.encode i))≠3) :
    ∀ a b : Fin (F.count c) → Prop, (∀ i, a i → b i) → predicate F c a → predicate F c b := by
  intro a b H
  apply value_mono F _ _ c htags
  intro i
  simp only [Le,atom,pairSnd_pair,BinaryNatCode.encode,Nat.fromBitsLE_bits,decide_eq_true_eq]
  by_cases hi : i<F.count c
  · simp only [dite_eq_left hi]
    exact H ⟨i,hi⟩
  · simp only [dite_eq_right hi,imp_self]

end LeanCanny.Computation.MonotoneBooleanCircuit
