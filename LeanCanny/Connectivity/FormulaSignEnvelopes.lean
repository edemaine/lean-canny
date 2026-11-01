/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Connectivity.FormulaSignPartition
public import LeanCanny.Connectivity.ClosedFormulaWitness
public import LeanCanny.Encoding.FormulaConjunctionWriter
/-! # Closed original-atom envelopes of mixed Boolean sign strata

Envelope membership is only a necessary boundary condition. Exact boundary
incidences use relative closures in the original permitted realization.
-/
@[expose] public section
namespace LeanCanny.Connectivity.FormulaSignPartition
open ETR Set LeanCanny.Encoding
open scoped Classical

def weakAtom (s : SignType) (t : Term) : Formula :=
  match s with
  | .zero => .eqZero t
  | .neg => .not (.ltZero (.mul (.const (-1)) t))
  | .pos => .not (.ltZero t)

noncomputable def envelope {p : Formula} (σ : Pattern p) : Formula :=
  FormulaConjunctionWriter.conjunction ((terms p).attach.map (fun t => weakAtom (σ t) t.val))

theorem weakAtom_closed (s : SignType) (t : Term) : ClosedFormulaWitness.Closed (weakAtom s t) := by
  cases s
  · exact .eqZero t
  · exact .nonnegative _
  · exact .nonnegative _

private theorem conjunction_closed (ps : List Formula)
    (H : ∀ p∈ps, ClosedFormulaWitness.Closed p) :
    ClosedFormulaWitness.Closed (FormulaConjunctionWriter.conjunction ps) := by
  induction ps with
  | nil => exact .verum
  | cons p ps IH =>
    exact .and (H p List.mem_cons_self) (IH (fun q hq => H q (List.mem_cons_of_mem _ hq)))

theorem envelope_closed {p : Formula} (σ : Pattern p) : ClosedFormulaWitness.Closed (envelope σ) := by
  apply conjunction_closed
  intro q hq
  obtain ⟨t,_,rfl⟩ := List.mem_map.mp hq
  exact weakAtom_closed _ _

theorem term_arity (p : Formula) (t : Term) (ht : t∈terms p) : t.arity≤p.arity := by
  induction p with
  | falsum => simp [terms] at ht
  | eqZero u =>
    have HE : t=u := List.mem_singleton.mp ht
    subst t
    exact le_refl _
  | ltZero u =>
    have HE : t=u := List.mem_singleton.mp ht
    subst t
    exact le_refl _
  | not p IH => exact IH ht
  | and p q IHp IHq =>
    rcases List.mem_append.mp ht with H | H
    · exact (IHp H).trans (le_max_left _ _)
    · exact (IHq H).trans (le_max_right _ _)
  | or p q IHp IHq =>
    rcases List.mem_append.mp ht with H | H
    · exact (IHp H).trans (le_max_left _ _)
    · exact (IHq H).trans (le_max_right _ _)

theorem weakAtom_arity (s : SignType) (t : Term) : (weakAtom s t).arity=t.arity := by
  cases s <;> simp [weakAtom,Formula.arity,Term.arity]

theorem envelope_arity {p : Formula} (σ : Pattern p) : (envelope σ).arity≤p.arity := by
  apply FormulaConjunctionWriter.arity
  intro q hq
  obtain ⟨t,_,rfl⟩ := List.mem_map.mp hq
  rw [weakAtom_arity]
  exact term_arity p t.val t.property

theorem weakAtom_of_sign (s : SignType) (t : Term) (env : ℕ → ℝ)
    (H : SignType.sign (t.eval env)=s) : (weakAtom s t).Holds env := by
  cases s with
  | zero => exact sign_eq_zero_iff.mp H
  | neg =>
    simp only [weakAtom,Formula.Holds,Term.eval,Int.cast_neg,Int.cast_one]
    change ¬(-1 : ℝ)*t.eval env < 0
    have HE := sign_eq_neg_one_iff.mp H
    nlinarith
  | pos =>
    change ¬t.eval env < 0
    have HE := sign_eq_one_iff.mp H
    linarith

theorem stratum_envelope {p : Formula} (n : ℕ) (σ : Pattern p) :
    Stratum n σ ⊆ {x | (envelope σ).Holds (Formula.extend x)} := by
  intro x hx
  change (envelope σ).Holds (Formula.extend x)
  rw [envelope,FormulaConjunctionWriter.holds]
  intro q hq
  obtain ⟨t,_,rfl⟩ := List.mem_map.mp hq
  exact weakAtom_of_sign _ _ _ (hx t)

theorem closed_holds {p : Formula} (hp : ClosedFormulaWitness.Closed p) (n : ℕ) :
    IsClosed {x : Fin n → ℝ | p.Holds (Formula.extend x)} := by
  induction hp with
  | falsum => exact isClosed_empty
  | verum => simp [Formula.Holds]
  | eqZero t => exact isClosed_eq (FormulaStrictWitness.continuous_eval n t) continuous_const
  | nonnegative t =>
    change IsClosed {x : Fin n → ℝ | ¬t.eval (Formula.extend x) < 0}
    simpa only [not_lt] using isClosed_le continuous_const (FormulaStrictWitness.continuous_eval n t)
  | and hp hq IHp IHq => exact IHp.inter IHq
  | or hp hq IHp IHq => exact IHp.union IHq

theorem closure_stratum_envelope {p : Formula} (n : ℕ) (σ : Pattern p) :
    closure (Stratum n σ) ⊆ {x | (envelope σ).Holds (Formula.extend x)} :=
  (closed_holds (envelope_closed σ) n).closure_subset_iff.mpr (stratum_envelope n σ)

end LeanCanny.Connectivity.FormulaSignPartition
