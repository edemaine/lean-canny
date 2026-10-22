/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BerkowitzTaskRouting

/-! # Deriving mixed-task ranks from source-context levels

Internal stages preserve the original matrix context and decrease their tag
priority. Only a source controller's nonzero child requests must decrease the
context level. A common unary bound on those levels supplies the native space
evaluator's rank bound; the level function itself is proof data.
-/

@[expose] public section

namespace LeanCanny.Algebra.BerkowitzPolynomial.TaskDispatch
open LeanCanny.Encoding LeanCanny.Computation
open Turing.MultiTapeTM

/-- Five priority slots per context level; the zero task has rank zero. -/
def levelRank (level : List Bool → ℕ) (q : List Bool) : ℕ :=
  if isZero q then 0 else 5 * level (origin q) + priority q

theorem levelRank_zero (level : List Bool → ℕ) : levelRank level [] = 0 := rfl

attribute [local irreducible] isZero isDeterminant isFactor isMoment payload
  BinaryNat.div BinaryNat.mod BinaryNat.normalize BinaryNat.mul BinaryNat.add BinaryNat.sub BinaryNat.succ

theorem levelRank_pos (level : List Bool → ℕ) (q : List Bool) (hq : isZero q = false) :
    0 < levelRank level q := by
  have hp := priority_pos q hq
  simp only [levelRank, hq, Bool.false_eq_true, ite_false]
  omega

theorem levelRank_le (level : List Bool → ℕ) (q : List Bool) (H : ℕ)
    (h : level (origin q) ≤ H) : levelRank level q ≤ 5 * H + 4 := by
  have hp := priority_le q
  unfold levelRank
  split_ifs <;> omega

theorem levelRank_lt_of_origin (level : List Bool → ℕ) (p q : List Bool)
    (hq : isZero q = false) (hp : priority p < priority q)
    (ho : p = [] ∨ origin p = origin q) : levelRank level p < levelRank level q := by
  rcases ho with rfl | ho
  · rw [levelRank_zero]
    exact levelRank_pos level q hq
  · simp only [levelRank, hq, Bool.false_eq_true, ite_false, ho]
    split_ifs <;> omega

theorem levelRank_lt_of_level (level : List Bool → ℕ) (p q : List Bool)
    (hq : isZero q = false) (h : level (origin p) < level (origin q)) :
    levelRank level p < levelRank level q := by
  have hp := priority_le p
  have hq' := priority_pos q hq
  simp only [levelRank, hq, Bool.false_eq_true, ite_false]
  split_ifs <;> omega

variable {F : ModularFamily} (a : ModularAccess F)
variable {S : Type} [Inhabited S] (source : RecursiveController.Controller (List Bool) S)

/-- Source-local requests are the only calls that need a context-level
decrease proof. Zero children are exempt. No execution-clock or child-space
certificate occurs in this contract. -/
def SourceLevels (sourceBudget : List Bool → ℕ) (tasks : List Bool → List Bool → Prop)
    (level : List Bool → ℕ) : Prop :=
  ∀ root q t, tasks root q → SelectedSource q → t ≤ sourceBudget (payload q) →
    source.halted ((source.reference (answer a))^[t] (source.initial (payload q))) = false →
    source.needs ((source.reference (answer a))^[t] (source.initial (payload q))) = true →
    isZero (source.query ((source.reference (answer a))^[t] (source.initial (payload q)))) = false →
    level (origin (source.query ((source.reference (answer a))^[t] (source.initial (payload q))))) < level (origin q)

theorem ranked_queries_of_source_levels (sourceBudget : List Bool → ℕ)
    (tasks : List Bool → List Bool → Prop) (level : List Bool → ℕ)
    (hclosed : QueriesClosed a source sourceBudget tasks)
    (hlevel : SourceLevels a source sourceBudget tasks level) :
    RankedQueries a source sourceBudget tasks (levelRank level) := by
  intro root q t hq ht hh hn
  refine ⟨hclosed root q t hq ht hh hn, ?_⟩
  have hz := requested_nonzero a source (answer a) q t hn
  by_cases hs : SelectedSource q
  · by_cases hc : isZero ((controller a source).query
        (((controller a source).reference (answer a))^[t] ((controller a source).initial q))) = true
    · have hp := levelRank_pos level q hz
      simpa only [levelRank, hc, ite_true] using hp
    · have hc' := Bool.eq_false_iff.mpr hc
      apply levelRank_lt_of_level level _ q hz
      rcases hs with ⟨hz, hd, hf, hm⟩
      rw [query_iterate] at hc' ⊢
      rw [halted_iterate] at hh
      rw [needs_iterate] at hn
      simp only [budget, hz, hd, hf, hm, Bool.false_eq_true, ite_false] at ht
      simp only [hz, hd, hf, hm, Bool.false_eq_true, ite_false] at hc' hh hn ⊢
      exact hlevel root q t hq ⟨hz, hd, hf, hm⟩ ht hh hn hc'
  · exact levelRank_lt_of_origin level _ q hz
      (internal_query_priority a source (answer a) q t hn hs)
      (internal_query_origin a source (answer a) q t hn hs)

/-- Native uniform evaluation with source-context levels. All internal rank
and context-preservation obligations are discharged by concrete routing. -/
theorem evaluator_of_source_levels {eS : S ↪ List Bool} (ha : a.ControlsPolyTime)
    (hC : source.Certificates (encQ := encBits) (encS := eS)) (sourceBudget : List Bool → ℕ)
    (hstop : ∀ p, source.halted ((source.reference (answer a))^[sourceBudget p] (source.initial p)) = true)
    (hcorrect : ∀ p t, source.halted ((source.reference (answer a))^[t] (source.initial p)) = true →
      source.output ((source.reference (answer a))^[t] (source.initial p)) = a.entry p)
    (tasks : List Bool → List Bool → Prop) (level H K M V N : List Bool → ℕ)
    (hH : UnaryFn H) (hK : UnaryFn K) (hM : UnaryFn M) (hV : UnaryFn V) (hN : BinaryFn N)
    (hroot : ∀ q, tasks q q)
    (hlevelBound : ∀ root q, tasks root q → level (origin q) ≤ H root)
    (hword : ∀ root q, tasks root q → q.length ≤ K root)
    (hanswer : ∀ root q, tasks root q → (answer a q).length ≤ K root)
    (hclosed : QueriesClosed a source sourceBudget tasks)
    (hlevel : SourceLevels a source sourceBudget tasks level)
    (hdet : ∀ root q, tasks root q → SelectedDeterminant q → determinantFields (F := F) (payload q) ≤ M root)
    (hmoment : ∀ root q, tasks root q → SelectedMoment q → momentFields (F := F) (payload q) ≤ M root)
    (hsourceBudget : ∀ root q, tasks root q → SelectedSource q → sourceBudget (payload q) ≤ N root)
    (hsourceState : ∀ root q, tasks root q → SelectedSource q → ∀ t ≤ sourceBudget (payload q),
      (eS ((source.reference (answer a))^[t] (source.initial (payload q)))).length ≤ V root) :
    SpaceFunction (answer a) :=
  evaluator a source ha hC sourceBudget hstop hcorrect tasks (levelRank level) (fun root => 5 * H root + 4) K M V N
    (((UnaryFn.const 5).mul hH).add (UnaryFn.const 4)) hK hM hV hN hroot
    (fun root q hq => levelRank_le level q (H root) (hlevelBound root q hq)) hword hanswer
    (ranked_queries_of_source_levels a source sourceBudget tasks level hclosed hlevel)
    hdet hmoment hsourceBudget hsourceState

end LeanCanny.Algebra.BerkowitzPolynomial.TaskDispatch
