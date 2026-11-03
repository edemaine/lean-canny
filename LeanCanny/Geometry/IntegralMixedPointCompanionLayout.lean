/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedPrefixOriginalPointRealization
public import LeanCanny.Geometry.IntegralMixedOptionalEndpointTrace
/-! # Literal fixed-objective companion records

Lists of selected free coordinates and commands are newest first. Every
retained frame reference is shifted once for every preceding scalar birth.
-/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedPointCompanion
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory
open IntegralMixedFullHistoryScript IntegralMixedCausalRowConstructor
open IntegralMixedFrozenFrame
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n m B : ℕ} {P : SpatialSource n}

def shiftRows (rows : Fin (n+1)→Row m) : (k : ℕ)→Fin (n+1)→Row (m+k)
  | 0=>rows
  | k+1=>fun i=>laterRow (shiftRows rows k i)

noncomputable def frame (frozen : Finset (Fin (n+1))) (double : Fin (n+1)→Bool)
    (rows : Fin (n+1)→Row m) (k : ℕ) :=originalFrame frozen double (shiftRows rows k)

theorem frame_succ (frozen : Finset (Fin (n+1))) (double : Fin (n+1)→Bool)
    (rows : Fin (n+1)→Row m) (k : ℕ) :
    frame frozen double rows (k+1)=retained (frame frozen double rows k) :=by
  unfold frame originalFrame retained
  congr 1
  funext i
  exact laterRow_value _

theorem slice_succ (frozen : Finset (Fin (n+1))) (double : Fin (n+1)→Bool)
    (rows : Fin (n+1)→Row m) (k : ℕ) (values : Fin (m+k)→ℝ) (a : ℝ) :
    slice P (frame frozen double rows (k+1)) (Fin.cons a values)=
      slice P (frame frozen double rows k) values :=by
  rw [frame_succ,slice_retained]

abbrev Free (frozen : Finset (Fin (n+1))) :={j : Fin (n+1)//j∉frozen}

noncomputable def pointData (frozen : Finset (Fin (n+1))) (double : Fin (n+1)→Bool)
    (rows : Fin (n+1)→Row m) (g : Free frozen) (k : ℕ) (j : Free frozen) :=
  originalPointData frozen double (shiftRows rows k) g.val j.val g.property j.property

noncomputable def command (frozen : Finset (Fin (n+1))) (double : Fin (n+1)→Bool)
    (rows : Fin (n+1)→Row m) (g : Free frozen) (k : ℕ) (j : Free frozen) : Command P B :=
  .critical (pointData frozen double rows g k j).rule

noncomputable def commands (frozen : Finset (Fin (n+1))) (double : Fin (n+1)→Bool)
    (rows : Fin (n+1)→Row m) (g : Free frozen) : List (Free frozen)→List (Command P B)
  | []=>[]
  | j::js=>command frozen double rows g js.length j::commands frozen double rows g js

@[simp] theorem commands_length (frozen : Finset (Fin (n+1))) (double : Fin (n+1)→Bool)
    (rows : Fin (n+1)→Row m) (g : Free frozen) (js : List (Free frozen)) :
    (commands (P:=P) (B:=B) frozen double rows g js).length=js.length :=by
  induction js with
  | nil=>rfl
  | cons j js ih=>simp only [commands,List.length_cons,ih]

noncomputable def codes (frozen : Finset (Fin (n+1))) (double : Fin (n+1)→Bool)
    (rows : Fin (n+1)→Row m) (g : Free frozen) : List (Free frozen)→List (List Bool)
  | []=>[]
  | j::js=>(pointData frozen double rows g js.length j).code::codes frozen double rows g js

@[simp] theorem codes_length (frozen : Finset (Fin (n+1))) (double : Fin (n+1)→Bool)
    (rows : Fin (n+1)→Row m) (g : Free frozen) (js : List (Free frozen)) :
    (codes frozen double rows g js).length=js.length :=by
  induction js with
  | nil=>rfl
  | cons j js ih=>simp only [codes,List.length_cons,ih]

noncomputable def values {frozen : Finset (Fin (n+1))} (p : Fin (n+1)→ℝ) (old : Fin m→ℝ) :
    (js : List (Free frozen))→(Fin (m+js.length)→ℝ)
  | []=>old
  | j::js=>Fin.cons (p j.val) (values p old js)

variable {S : ℕ} {ι : Type} [Fintype ι]

noncomputable def run (x : State P S B m ι) (frozen : Finset (Fin (n+1))) (double : Fin (n+1)→Bool)
    (rows : Fin (n+1)→Row m) (g : Free frozen) : (js : List (Free frozen))→
    m+js.length≤S+1→State P S B (m+js.length) (Index ι (commands (P:=P) (B:=B) frozen double rows g js))
  | [],_=>x
  | j::js,room=>step (run x frozen double rows g js (by simp only [List.length_cons] at room;omega))
      (by simp only [List.length_cons] at room;omega) (command frozen double rows g js.length j)

noncomputable def blockColumn (frozen : Finset (Fin (n+1))) (double : Fin (n+1)→Bool)
    (rows : Fin (n+1)→Row m) (g : Free frozen) : (js : List (Free frozen))→
    Fin js.length→Fin (n+1)→Index ι (commands (P:=P) (B:=B) frozen double rows g js)
  | [],k=>Fin.elim0 k
  | _::js,k=>Fin.cases (fun i=>Sum.inl (FlatAffineCriticalStage.ambient i))
      (fun k i=>Sum.inl (Sum.inl (blockColumn frozen double rows g js k i))) k

end LeanCanny.Geometry.IntegralMixedPointCompanion
