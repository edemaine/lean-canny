/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.Problem
public import Mathlib.Basic.Sign.Basic
public import Mathlib.Data.Fintype.Pi
/-! # Actual finite sign strata for arbitrary Boolean formula syntax

A sign label refers to the original atomic terms. Arbitrary negation is
interpreted on that label; no existential nonemptiness compiler is used.
-/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignPartition
open ETR Set
open scoped Classical

def terms : Formula → List Term
  | .falsum => []
  | .eqZero t | .ltZero t => [t]
  | .not p => terms p
  | .and p q | .or p q => terms p ++ terms q

abbrev Atom (p : Formula) := {t : Term // t∈terms p}
instance (p : Formula) : Finite (Atom p) := (terms p).finite_toSet.to_subtype
abbrev Pattern (p : Formula) := Atom p → SignType

noncomputable def interpret (σ : Term → SignType) : Formula → Prop
  | .falsum => False
  | .eqZero t => σ t=0
  | .ltZero t => σ t = -1
  | .not p => ¬interpret σ p
  | .and p q => interpret σ p ∧ interpret σ q
  | .or p q => interpret σ p ∨ interpret σ q

noncomputable def complete {p : Formula} (σ : Pattern p) (t : Term) : SignType :=
  if h : t∈terms p then σ ⟨t,h⟩ else 0
noncomputable def accepted {p : Formula} (σ : Pattern p) := interpret (complete σ) p

noncomputable def ofPoint (p : Formula) (env : ℕ → ℝ) : Pattern p :=
  fun t => SignType.sign (t.val.eval env)

def Stratum {p : Formula} (n : ℕ) (σ : Pattern p) : Set (Fin n → ℝ) :=
  {x | ∀ t : Atom p, SignType.sign (t.val.eval (Formula.extend x))=σ t}

theorem interpret_truth (p : Formula) (σ : Term → SignType) (env : ℕ → ℝ)
    (H : ∀ t∈terms p, σ t=SignType.sign (t.eval env)) : interpret σ p ↔ p.Holds env := by
  induction p with
  | falsum => rfl
  | eqZero t =>
    change σ t=0 ↔ t.eval env=0
    rw [H t (by simp [terms]),sign_eq_zero_iff]
  | ltZero t =>
    change σ t = -1 ↔ t.eval env < 0
    rw [H t (by simp [terms]),sign_eq_neg_one_iff]
  | not p IH => exact not_congr (IH H)
  | and p q IHp IHq =>
    exact and_congr (IHp (fun t ht => H t (List.mem_append_left _ ht)))
      (IHq (fun t ht => H t (List.mem_append_right _ ht)))
  | or p q IHp IHq =>
    exact or_congr (IHp (fun t ht => H t (List.mem_append_left _ ht)))
      (IHq (fun t ht => H t (List.mem_append_right _ ht)))

theorem stratum_truth {p : Formula} (n : ℕ) (σ : Pattern p) {x : Fin n → ℝ}
    (hx : x∈Stratum n σ) : accepted σ ↔ p.Holds (Formula.extend x) := by
  apply interpret_truth
  intro t ht
  rw [complete,dite_eq_left ht]
  exact (hx ⟨t,ht⟩).symm

theorem point_stratum (p : Formula) (n : ℕ) (x : Fin n → ℝ) :
    x∈Stratum n (ofPoint p (Formula.extend x)) := fun _ => rfl

theorem realization_union (d : Description) :
    d.realization = ⋃ σ : {σ : Pattern d.formula // accepted σ}, Stratum d.dimension σ.val := by
  ext x
  constructor
  · intro hx
    let σ := ofPoint d.formula (Formula.extend x)
    have HS := point_stratum d.formula d.dimension x
    have HA : accepted σ := (stratum_truth d.dimension σ HS).mpr hx
    exact mem_iUnion.mpr ⟨⟨σ,HA⟩,HS⟩
  · intro hx
    obtain ⟨σ,hσ⟩ := mem_iUnion.mp hx
    exact (stratum_truth d.dimension σ.val hσ).mp σ.property

theorem truth_constant {p : Formula} (n : ℕ) (σ : Pattern p) {x y : Fin n → ℝ}
    (hx : x∈Stratum n σ) (hy : y∈Stratum n σ) :
    p.Holds (Formula.extend x) ↔ p.Holds (Formula.extend y) :=
  (stratum_truth n σ hx).symm.trans (stratum_truth n σ hy)

end LeanCanny.Connectivity.FormulaSignPartition
