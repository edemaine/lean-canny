/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedJointCriticalSlab
public import LeanCanny.Encoding.IntegralMixedCriticalRecordBounds
public import LeanCanny.Algebra.IntegralMixedCommandClearing
/-! # The actual three-record midpoint construction has a fixed target budget -/
@[expose] public section
namespace LeanCanny.Encoding.IntegralMixedJointCriticalBudget
open LeanCanny.Algebra LeanCanny.Geometry IntegralMixedFrozenFrame IntegralMixedHistory
open IntegralMixedCriticalRecordConstructor
open scoped Classical
variable {n m : ℕ} {F : Frame n}

noncomputable def codes (HA : AtomicRows F m) (h g j : Fin (n+1))
    (hh : h∉F.frozen) (hg : g∉(line F h).frozen) (hj : j∉(line F h).frozen) : List (List Bool) :=
  [(HA.pointData h h hh hh).code,(HA.retained.pointData h h hh hh).code,
    (midpointData HA h g j hg hj).code]

theorem count (HA : AtomicRows F m) (h g j : Fin (n+1))
    (hh : h∉F.frozen) (hg : g∉(line F h).frozen) (hj : j∉(line F h).frozen) :
    (codes HA h g j hh hg hj).length=3:=rfl

def byteBound (n m : ℕ) :=
  (2*(codeBudget n m+codeBudget n (m+1)+codeBudget n (m+2))+2)*3

theorem bytes (HA : AtomicRows F m) (h g j : Fin (n+1))
    (hh : h∉F.frozen) (hg : g∉(line F h).frozen) (hj : j∉(line F h).frozen) :
    (WordList.encode (codes HA h g j hh hg hj)).length≤byteBound n m :=by
  let V:=codeBudget n m+codeBudget n (m+1)+codeBudget n (m+2)
  have HA0:=(HA.pointData h h hh hh).code_length
  have HB0:=(HA.retained.pointData h h hh hh).code_length
  have HM0:=(midpointData HA h g j hg hj).code_length
  have HB : ∀ w∈codes HA h g j hh hg hj,w.length≤V:=by
    intro w hw
    simp only [codes,List.mem_cons,List.not_mem_nil,or_false] at hw
    rcases hw with rfl|rfl|rfl <;> dsimp only [V] <;> omega
  simpa only [count,byteBound,V] using WordList.length_le _ V HB

theorem target_room (m S : ℕ) : m+3≤S+1↔m+2≤S:=by omega

theorem physical_columns (ι : Type) [Fintype ι] :
    Fintype.card (CriticalIndex n (CriticalIndex n (CriticalIndex n ι)))=
      Fintype.card ι+3*(2*n+4):=by
  simp only [CriticalIndex,FlatAffineCriticalStage.Variables,Fintype.card_sum,Fintype.card_fin,
    Fintype.card_unit]
  omega

end LeanCanny.Encoding.IntegralMixedJointCriticalBudget
