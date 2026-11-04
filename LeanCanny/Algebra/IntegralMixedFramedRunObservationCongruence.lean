/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedRunObservation
/-! # Equal typed programs preserve every natural row and bank observation -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedRunObservation
open IntegralMixedHistory IntegralMixedFramedHistoryScript

theorem ofCommands_heq {n m S T B C :ℕ} {P :SpatialSource n} {Q :SpatialSource m}
    (x :State P S B 0 (Fin 0)) (y :State Q T C 0 (Fin 0))
    (cs :List (Instruction n B)) (ds :List (Instruction m C))
    (hc :cs.length≤S+1) (hd :ds.length≤T+1)
    (en :n=m) (eS :S=T) (eB :B=C) (eP :HEq P Q) (ex :HEq x y) (hcs :HEq cs ds) :
    ofCommands x cs hc=ofCommands y ds hd:=by
  subst m
  subst T
  subst C
  cases eq_of_heq eP
  cases eq_of_heq ex
  cases eq_of_heq hcs
  rfl

end LeanCanny.Algebra.IntegralMixedFramedRunObservation
