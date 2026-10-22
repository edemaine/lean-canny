/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.Encoding
public import LeanCanny.Computation.PolyTime

/-!
# The complexity class ∃ℝ

`ExistsReal` is the downward closure of the explicitly encoded ETR language under
Complexitylib2's polynomial-time many-one reductions. These are reductions on every binary
string, including malformed inputs. This module proves the basic closure and completeness
laws. It does not assert Canny's polynomial-space upper bound.
-/

@[expose] public section

namespace LeanCanny
open Turing.MultiTapeTM

/-- The class ∃ℝ: languages polynomial-time many-one reducible to existential real arithmetic. -/
def ExistsReal : Set Language := {L | PolyTimeReduces L ETR.language}

/-- Hardness for every language in ∃ℝ under polynomial-time many-one reductions. -/
def ExistsRealHard (L : Language) : Prop := ∀ K ∈ ExistsReal, PolyTimeReduces K L

/-- Both membership and hardness for ∃ℝ. -/
def ExistsRealComplete (L : Language) : Prop := L ∈ ExistsReal ∧ ExistsRealHard L

@[simp] theorem mem_existsReal_iff (L : Language) :
    L ∈ ExistsReal ↔ PolyTimeReduces L ETR.language := Iff.rfl

/-- ETR belongs to ∃ℝ by the identity reduction. -/
theorem etr_mem_existsReal : ETR.language ∈ ExistsReal :=
  Cslib.Complexity.PolyTimeReducible.refl encBits _

/-- Every ∃ℝ problem reduces to ETR, by the definition of the class. -/
theorem etr_existsRealHard : ExistsRealHard ETR.language := fun _ h => h

/-- ETR is the defining complete language for ∃ℝ. -/
theorem etr_existsRealComplete : ExistsRealComplete ETR.language :=
  ⟨etr_mem_existsReal, etr_existsRealHard⟩

/-- Membership pulls back along a polynomial-time many-one reduction. -/
theorem existsReal_of_reduction {L K : Language} (h : PolyTimeReduces L K) (hK : K ∈ ExistsReal) :
    L ∈ ExistsReal := h.trans hK

/-- A language is ∃ℝ-hard exactly when ETR reduces to it. -/
theorem existsRealHard_iff (L : Language) :
    ExistsRealHard L ↔ PolyTimeReduces ETR.language L := by
  constructor
  · exact fun h => h _ etr_mem_existsReal
  · exact fun h _ hK => hK.trans h

/-- Completeness is precisely polynomial-time many-one equivalence with ETR. -/
theorem existsRealComplete_iff (L : Language) :
    ExistsRealComplete L ↔ PolyTimeReduces L ETR.language ∧ PolyTimeReduces ETR.language L := by
  simp only [ExistsRealComplete, mem_existsReal_iff, existsRealHard_iff]

/-- Hardness transfers forward along a polynomial-time reduction. -/
theorem ExistsRealHard.of_reduction {L K : Language}
    (hL : ExistsRealHard L) (h : PolyTimeReduces L K) : ExistsRealHard K :=
  fun M hM => (hL M hM).trans h

/-- Any complete language can serve as the defining target for ∃ℝ. -/
theorem mem_existsReal_iff_reduces_to_complete {K : Language}
    (hK : ExistsRealComplete K) (L : Language) :
    L ∈ ExistsReal ↔ PolyTimeReduces L K := by
  constructor
  · exact fun h => hK.2 L h
  · exact fun h => existsReal_of_reduction h hK.1

/-- For any class closed under polynomial-time many-one reductions, containing ETR is
equivalent to containing all of ∃ℝ. The closure hypothesis is explicit. -/
theorem existsReal_subset_iff {C : Set Language}
    (hclosed : ∀ {L K : Language}, PolyTimeReduces L K → K ∈ C → L ∈ C) :
    ExistsReal ⊆ C ↔ ETR.language ∈ C := by
  constructor
  · exact fun h => h etr_mem_existsReal
  · exact fun h _ hL => hclosed hL h

/-- A nontrivial target language admits a reduction from every polynomial-time language. -/
theorem reduces_to_nontrivial_of_mem_P {L K : Language} (hL : L ∈ P)
    (yes no : List Bool) (hyes : yes ∈ K) (hno : no ∉ K) : PolyTimeReduces L K := by
  obtain ⟨g, hgTime, hg⟩ := hL
  let reduce := fun x => if g x then yes else no
  refine ⟨reduce, hgTime.cond (.const yes) (.const no), ?_⟩
  intro x
  rw [hg x]
  by_cases h : g x = true <;> simp [reduce, h, hyes, hno]

/-- As a first unconditional lower inclusion, polynomial-time languages belong to ∃ℝ. -/
theorem P_subset_existsReal : P ⊆ ExistsReal := by
  intro L hL
  apply reduces_to_nontrivial_of_mem_P hL
    (ETR.Formula.eqZero (.const 0)).encode ETR.Formula.falsum.encode
  · exact (ETR.encode_mem_language _).mpr ETR.Formula.satisfiable_eqZero_zero
  · simp

end LeanCanny
