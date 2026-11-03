/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Geometry.IntegralMixedDecodedAppend
public import LeanCanny.Geometry.IntegralMixedPointCompanionColumns

/-! # Local capture receipts are decoder receipts for the literal flat command list -/
@[expose] public section
namespace LeanCanny.Geometry.IntegralMixedPointCompanion
open LeanCanny.Algebra LeanCanny.Encoding IntegralMixedHistory IntegralMixedFullHistoryScript
open IntegralMixedFrozenFrame IntegralMixedCausalRowConstructor
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n S B m : ℕ} {P : SpatialSource n} {ι : Type} [Fintype ι]

theorem decoded_decodes (x : State P S B m ι) (frozen : Finset (Fin (n+1))) (double : Fin (n+1)→Bool)
    (rows : Fin (n+1)→Row m) (g : Free frozen) (hn : 0<n)
    (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (js : List (Free frozen)) (room : m+js.length≤S+1)
    (HD : Decoded x frozen double rows g hn hcap js room) :
    IntegralMixedOptionalEndpoints.Decodes x hn hcap (commands frozen double rows g js)
      (by simpa only [commands_length] using room) (codes frozen double rows g js) :=by
  induction js with
  | nil=>rfl
  | cons j js ih=>
    refine ⟨ih (by simp only [List.length_cons] at room;omega) HD.1,?_⟩
    have HS:=run_continue x frozen double rows g js (by simp only [List.length_cons] at room;omega)
    have HT : m+js.length=m+(commands (P:=P) (B:=B) frozen double rows g js).length:=by rw [commands_length]
    have HQ:=IntegralMixedOptionalEndpoints.commonDenominator_heq _ _ HT rfl HS
    exact (IntegralMixedOptionalEndpoints.decoded_command_congr hn _ _ _ hcap _ _ _ _ HT.symm HQ.symm).trans HD.2

theorem decodes_append {u : ℕ} (x : State P S B m ι)
    (frozen : Finset (Fin (n+1))) (double : Fin (n+1)→Bool) (rows : Fin (n+1)→Row u) (g : Free frozen)
    (hn : 0<n) (hcap : IntegralMixedExceptionalBounds.auxiliaryCap (n+1) P.degree≤2^B)
    (ds : List (Command P B)) (hd : m+ds.length≤S+1) (oldCodes : List (List Bool))
    (HD : IntegralMixedOptionalEndpoints.Decodes x hn hcap ds hd oldCodes) (hu : u=m+ds.length)
    (js : List (Free frozen)) (h : m+(commands frozen double rows g js++ds).length≤S+1) :
    IntegralMixedOptionalEndpoints.Decodes x hn hcap (commands frozen double rows g js++ds) h
      (codes frozen double rows g js++oldCodes) :=by
  induction js with
  | nil=>exact HD
  | cons j js ih=>
    have HB : u+js.length=m+(commands (P:=P) (B:=B) frozen double rows g js++ds).length:=by
      rw [List.length_append,commands_length]
      omega
    exact IntegralMixedOptionalEndpoints.Decodes.prepend_critical x hn hcap _
      (by simp only [commands,List.cons_append,List.length_cons] at h
          omega) _
      (ih (by simp only [commands,List.cons_append,List.length_cons] at h;omega))
      (pointData frozen double rows g js.length j) HB h

end LeanCanny.Geometry.IntegralMixedPointCompanion
