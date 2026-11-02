/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Algebra.IntegralMixedFramedStateTransport
public import LeanCanny.Algebra.IntegralMixedFramedHistoryFamily
/-! # Heterogeneous replay transport of an actual empty-bank framed run -/
@[expose] public section
namespace LeanCanny.Algebra.IntegralMixedFramedRunTransport
open IntegralMixedHistory IntegralMixedFramedHistoryScript
set_option backward.isDefEq.respectTransparency false

theorem base_zero_heq {A A' S S' B B' : ℕ} {P : SpatialSource A} {Q : SpatialSource A'}
    (hA : A=A') (hS : S=S') (hB : B=B') (hP : HEq P Q)
    (hc : PurePowerReductionBounds.dimension (A+1) P.degree≤2^B)
    (hc' : PurePowerReductionBounds.dimension (A'+1) Q.degree≤2^B') :
    HEq (IntegralMixedHistory.base P (IntegralHistorySampler.base S (2^B)) hc)
      (IntegralMixedHistory.base Q (IntegralHistorySampler.base S' (2^B')) hc') := by
  cases hA
  cases hS
  cases hB
  have HP : P=Q := eq_of_heq hP
  cases HP
  rfl

theorem index_zero_eq {A A' B B' : ℕ} (hA : A=A') (hB : B=B')
    (cs : List (Instruction A B)) (ds : List (Instruction A' B')) (hLists : HEq cs ds) :
    Index (Fin 0) cs=Index (Fin 0) ds := by
  cases hA
  cases hB
  have HL : cs=ds := eq_of_heq hLists
  cases HL
  rfl

theorem reframe_run_zero_heq {A A' S S' B B' Rdim : ℕ} {P : SpatialSource A} {Q : SpatialSource A'}
    (hA : A=A') (hS : S=S') (hB : B=B') (hP : HEq P Q)
    (x : State P S B 0 (Fin 0)) (y : State Q S' B' 0 (Fin 0)) (hState : HEq x y)
    (cs : List (Instruction A B)) (ds : List (Instruction A' B')) (hLists : HEq cs ds)
    (hc : cs.length≤S+1) (hd : ds.length≤S'+1) (R : SpatialSource Rdim)
    (hR : PurePowerReductionBounds.dimension (Rdim+1) R.degree≤2^B)
    (hR' : PurePowerReductionBounds.dimension (Rdim+1) R.degree≤2^B') :
    HEq (reframe (run x cs hc) R hR) (reframe (run y ds hd) R hR') := by
  cases hA
  cases hS
  cases hB
  have HP : P=Q := eq_of_heq hP
  cases HP
  have HX : x=y := eq_of_heq hState
  cases HX
  have HL : cs=ds := eq_of_heq hLists
  cases HL
  rfl
end LeanCanny.Algebra.IntegralMixedFramedRunTransport
