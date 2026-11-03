/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedPointCompanionTrace
public import LeanCanny.Algebra.IntegralMixedFramedPhysicalAncestry
/-! # The companion trace is an actual script with explicit physical columns -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedPointCompanion
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedFullHistoryScript
open IntegralMixedCausalRowConstructor IntegralMixedChosenLocalRealization
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

private theorem step_heq {a b : ℕ} (x : State P S B a ι) (y : State P S B b ι)
    (he : a=b) (hxy : HEq x y) (ha : a≤S) (hb : b≤S) (c : Command P B) :
    HEq (step x ha c) (step y hb c) :=by
  subst b
  cases hxy
  rfl

variable (x : State P S B m ι) (frozen : Finset (Fin (n+1))) (double : Fin (n+1)→Bool)
    (rows : Fin (n+1)→Row m) (g : Free frozen)

theorem run_continue (js : List (Free frozen)) (room : m+js.length≤S+1) :
    HEq (run x frozen double rows g js room)
      (continueRun x (commands (P:=P) (B:=B) frozen double rows g js) (by simpa only [commands_length] using room)) :=by
  induction js with
  | nil=>rfl
  | cons j js ih=>
    apply step_heq _ _ (congrArg (m+·) (commands_length (P:=P) (B:=B) frozen double rows g js).symm)
      (ih _) _ _ (command frozen double rows g js.length j)

variable {L : ℕ} (e : ι≃Fin L)

noncomputable def columns : (js : List (Free frozen))→
    Index ι (commands (P:=P) (B:=B) frozen double rows g js)≃Fin (L+(2*n+4)*js.length)
  | []=>e
  | j::js=>(IntegralMixedFramedPhysicalIndex.stepEquiv (command frozen double rows g js.length j)
      (columns js)).trans (finCongr (by
        simp only [command,IntegralMixedFramedPhysicalIndex.added,Command.isCritical,ite_true,
          IntegralMixedFramedPhysicalIndex.block,List.length_cons]
        ring))

omit [Fintype ι] in
theorem columns_old (js : List (Free frozen)) (i : ι) :
    (columns (P:=P) (B:=B) frozen double rows g e js
      (IntegralMixedOptionalEndpoints.oldColumns (commands (P:=P) (B:=B) frozen double rows g js) i)).val=(e i).val :=by
  induction js with
  | nil=>rfl
  | cons j js ih=>exact ih

omit [Fintype ι] in
theorem columns_block (js : List (Free frozen)) (k : Fin js.length) (i : Fin (n+1)) :
    (columns (P:=P) (B:=B) frozen double rows g e js (blockColumn (P:=P) (B:=B) frozen double rows g js k i)).val=
      L+(2*n+4)*(js.length-1-k.val)+i.val :=by
  induction js with
  | nil=>exact Fin.elim0 k
  | cons j js ih=>
    refine Fin.cases ?_ (fun k=>?_) k
    · change L+(2*n+4)*js.length+i.val=_
      simp only [List.length_cons,Fin.val_zero,Nat.add_sub_cancel_right,Nat.sub_zero]
    · change (columns (P:=P) (B:=B) frozen double rows g e js (blockColumn (P:=P) (B:=B) frozen double rows g js k i)).val=_
      rw [ih k]
      have HE : (j::js).length-1-k.succ.val=js.length-1-k.val:=by
        simp only [List.length_cons,Fin.val_succ]
        omega
      rw [HE]

theorem physical_columns (js : List (Free frozen)) :
    Fintype.card (Index ι (commands (P:=P) (B:=B) frozen double rows g js))=
      Fintype.card ι+(2*n+4)*js.length :=by
  have HE:=Fintype.card_congr (columns (P:=P) (B:=B) frozen double rows g (Fintype.equivFin ι) js)
  simpa only [Fintype.card_fin] using HE

end LeanCanny.Geometry.IntegralMixedPointCompanion
