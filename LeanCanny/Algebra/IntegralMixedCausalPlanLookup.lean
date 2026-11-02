/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedCausalPlan
/-! # Each causal record is instantiated at its exact actual older prefix -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedCausalPlanBits
open LeanCanny.Encoding LeanCanny.Computation IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedCausalRecordBits
open scoped Classical
set_option backward.isDefEq.respectTransparency false

private theorem run_denominator_congr {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State P S B 0 ι) (cs ds : List (Instruction n B))
    (hc : cs.length≤S+1) (hd : ds.length≤S+1) (he : cs=ds) :
    commonDenominator (run initial cs hc)=commonDenominator (run initial ds hd) := by
  subst ds
  rfl

theorem chosen_instantiate {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State P S B 0 ι) (rs : List (Record n B)) (h : rs.length≤S+1) (i : Fin rs.length) :
    chosen (commands initial rs h) ⟨i.val,by rw [commands_length]; exact i.isLt⟩=
      instantiate (run initial (older (commands initial rs h) ⟨i.val,by rw [commands_length]; exact i.isLt⟩)
        ((older_bound (commands initial rs h) (by rw [commands_length]; exact h) _).trans (Nat.le_succ _))) rs[i] := by
  induction rs with
  | nil => exact Fin.elim0 i
  | cons r rs ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [commands_cons,chosen,older,List.getElem_cons_zero,Fin.val_zero]
      rfl
    · have ht : rs.length≤S+1 := by simp only [List.length_cons] at h; omega
      have HR : (r::rs)[j.succ]=rs[j] := rfl
      have HL : chosen (commands initial (r::rs) h) ⟨j.succ.val,by rw [commands_length]; exact j.succ.isLt⟩=
          chosen (commands initial rs ht) ⟨j.val,by rw [commands_length]; exact j.isLt⟩ := rfl
      let ic : Fin (commands initial (r::rs) h).length := ⟨j.succ.val,by rw [commands_length]; exact j.succ.isLt⟩
      let y := run initial (older (commands initial (r::rs) h) ic)
        ((older_bound _ (by rw [commands_length]; exact h) ic).trans (Nat.le_succ _))
      have Hrec : instantiate y rs[j]=instantiate y (r::rs)[j.succ] := congrArg (instantiate y) HR.symm
      refine HL.trans ((ih ht j).trans ?_)
      refine (instantiate_congr _ y (rs[j]) ?_).trans Hrec
      dsimp only [y]
      apply run_denominator_congr
      simp only [older,commands_cons,ic,Fin.val_succ,List.drop_succ_cons]

theorem commands_bodies {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State P S B 0 ι) (rs : List (Record n B)) (h : rs.length≤S+1) :
    (commands initial rs h).map (fun c => commandBody c.command)=rs.map (fun r => r.template.body) := by
  induction rs with
  | nil => rfl
  | cons r rs ih => rw [commands_cons,List.map_cons,instantiate_body,List.map_cons,ih]

/-- Original source metadata is read at the same index, without evaluating Q. -/
theorem chronological_source {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State P S B 0 ι) (rs : List (Record n B)) (h : rs.length≤S+1) (b : ℕ) :
    (chronological (commands initial rs h) b).map Instruction.source=
      rs.reverse[b]?.map Record.source := by
  unfold chronological
  have H := congrArg (fun sources => sources.reverse[b]?) (commands_sources initial rs h)
  rw [← List.map_reverse,← List.map_reverse,List.getElem?_map,List.getElem?_map] at H
  exact H

/-- The native creator birth is the actual scalar-prefix arity, not a
physical-variable count. Older source changes remain in the literal run. -/
theorem older_eq_padded {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State P S B 0 ι) (rs : List (Record n B)) (h : rs.length≤S+1)
    (default : Instruction n B) (i : Fin (commands initial rs h).length) :
    older (commands initial rs h) i=paddedPast default (commands initial rs h) ((commands initial rs h).length-1-i.val) := by
  have H := paddedPast_older default (commands initial rs h) (commands initial rs h).length
    ⟨i.val,by rw [paddedPast_length]; exact i.isLt⟩
  simpa only [older,paddedPast_full] using H
theorem chronological_instantiate {n S B : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]
    (initial : State P S B 0 ι) (rs : List (Record n B)) (h : rs.length≤S+1)
    (fallback : Instruction n B) (b : Fin rs.length) :
    chronological (commands initial rs h) b.val=some (instantiate
      (run initial (paddedPast fallback (commands initial rs h) b.val)
        (by rw [paddedPast_length]; exact b.isLt.le.trans h))
      rs.reverse[b.val]) := by
  let i : Fin rs.length := ⟨rs.length-1-b.val,by have H:=b.isLt; omega⟩
  let ic : Fin (commands initial rs h).length := ⟨i.val,by rw [commands_length]; exact i.isLt⟩
  have HL : (commands initial rs h).length-1-ic.val=b.val := by
    dsimp only [ic,i]
    rw [commands_length]
    have H:=b.isLt
    omega
  have HA := chronological_older (commands initial rs h) ic
  rw [older_length,HL] at HA
  refine HA.trans (congrArg some ?_)
  have HR : rs[i]=rs.reverse[b.val] := by
    have H := List.getElem?_reverse' (l:=rs) (i:=b.val) (j:=i.val) (by dsimp only [i]; omega)
    rw [List.getElem?_eq_getElem (by rw [List.length_reverse]; exact b.isLt),List.getElem?_eq_getElem i.isLt] at H
    exact (Option.some.inj H).symm
  have HC := chosen_instantiate initial rs h i
  refine HC.trans ?_
  have HE := older_eq_padded initial rs h fallback ic
  rw [HL] at HE
  let y := run initial (paddedPast fallback (commands initial rs h) b.val) (by rw [paddedPast_length]; exact b.isLt.le.trans h)
  have Hrec : instantiate y rs[i]=instantiate y rs.reverse[b.val] := congrArg (instantiate y) HR
  refine (instantiate_congr _ y rs[i] ?_).trans Hrec
  apply run_denominator_congr
  exact HE

end LeanCanny.Algebra.IntegralMixedCausalPlanBits
