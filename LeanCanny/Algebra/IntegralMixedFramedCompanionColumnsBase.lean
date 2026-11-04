/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedCompanionColumns
/-! # Companion columns respect an already identified older index -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedFixedContinuation
open LeanCanny.Geometry LeanCanny.Encoding IntegralMixedHistory IntegralMixedFramedHistoryScript
open IntegralMixedFramedPhysicalIndex IntegralMixedPointCompanion IntegralMixedCausalRowConstructor
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {n B m : ℕ} {Q : SpatialSource n}

theorem columns_base_heq (frozen : Finset (Fin (n+1))) (double : Fin (n+1)→Bool)
    (rows : Fin (n+1)→Row m) (g : Free frozen) (js : List (Free frozen))
    {ι κ : Type} {a b : ℕ} (e : ι≃Fin a) (f : κ≃Fin b)
    (hi : ι=κ) (hab : a=b) (he : HEq e f) :
    HEq (columns (P:=Q) (B:=B) frozen double rows g e js)
      (columns (P:=Q) (B:=B) frozen double rows g f js):=by
  cases hi
  cases hab
  have HE : e=f:=eq_of_heq he
  subst f
  rfl

theorem companion_columns_from
    (hQ : PurePowerReductionBounds.dimension (n+1) Q.degree≤2^B)
    (older : List (Instruction n B)) (frozen : Finset (Fin (n+1))) (double : Fin (n+1)→Bool)
    (rows : Fin (n+1)→Row m) (g : Free frozen) (js : List (Free frozen))
    {κ : Type} {L : ℕ} (e : κ≃Fin L)
    (hi : Index (Fin 0) older=κ) (hL : arity older=L) (he : HEq (enumerate older) e) :
    HEq (enumerate ((commands (P:=Q) (B:=B) frozen double rows g js).map (wrap Q hQ)++older))
      (columns (P:=Q) (B:=B) frozen double rows g e js):=
  (companion_columns hQ older frozen double rows g js).trans
    (columns_base_heq frozen double rows g js (enumerate older) e hi hL he)

end LeanCanny.Algebra.IntegralMixedFramedFixedContinuation
