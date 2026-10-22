/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.CannyBalancedTaskRequests

/-! # Common address and context-field bounds

A nonleaf descent decreases the reconstructed node length, even when its
input is malformed. Taking the maximum with the original word length gives
a measure that never increases on the actual task graph. Original input and
modulus words also have nonincreasing lengths.
-/

@[expose] public section

namespace LeanCanny.Algebra.BalancedParameterContext
open LeanCanny.Encoding

def footprint (p : List Bool) : ℕ :=
  max p.length (2 * (original p).length + 2 * height p + (indexWord p).length + 4)

theorem footprint_ge_four (p : List Bool) : 4 ≤ footprint p := by
  have h := Nat.le_max_right p.length (2 * (original p).length + 2 * height p + (indexWord p).length + 4)
  dsimp only [footprint]
  omega

theorem footprint_eq_length (p : List Bool) (hp : Paired p) : footprint p = p.length := by
  have h := congrArg List.length hp
  simp only [pair_length] at h
  have he : 2 * (original p).length + 2 * height p + (indexWord p).length + 4 = p.length := by
    dsimp only [height] at ⊢
    omega
  simp only [footprint, he, Nat.max_self]

theorem footprint_le (p : List Bool) : footprint p ≤ 5 * p.length + 4 := by
  have ho := pairFst_length_le p
  have hh := height_le_length p
  have hi := (pairSnd_length_le (pairSnd p)).trans (pairSnd_length_le p)
  dsimp only [footprint, original, indexWord]
  omega

theorem child_footprint_le (right : Bool) (p : List Bool) (hh : 0 < height p) :
    footprint (child right p) ≤ footprint p := by
  rw [footprint_eq_length _ (paired_child right p)]
  have hi := BinaryNat.normalize_length_le (right :: indexWord p)
  simp only [List.length_cons] at hi
  have hm := Nat.le_max_right p.length (2 * (original p).length + 2 * height p + (indexWord p).length + 4)
  simp only [child, pair_length, List.length_drop]
  dsimp only [height] at hh hm
  dsimp only [footprint, height]
  omega

end LeanCanny.Algebra.BalancedParameterContext

namespace LeanCanny.Algebra.CannyBalancedTaskRouting
open LeanCanny.Encoding LeanCanny.Computation
open BerkowitzPolynomial.TaskDispatch
open BalancedParameterContext (original footprint)

theorem childInput_nodeContext (right : Bool) (p : List Bool) :
    nodeContext (childInput right p) = BalancedParameterContext.child right (nodeContext (pairFst p)) := by
  simp only [nodeContext, childInput, matrixPacket, pairFst_pair]

theorem nodeContext_length_le (c : List Bool) : (nodeContext c).length ≤ c.length :=
  (pairFst_length_le (pairFst c)).trans (pairFst_length_le c)

variable (L : SeparableBits.Family) {F : CannyResultantBits.Family} {leftOrder rightOrder : List Bool → ℕ}
  (a : CannyResultantBits.Access F leftOrder rightOrder)

theorem reachable_node_length_le (root q : List Bool) (hq : tasks L a root q) :
    (nodeContext (origin q)).length ≤ 5 * root.length + 4 := by
  have hm := reachable_measure_le L a (fun c => footprint (nodeContext c))
    (fun c => by change 4 ≤ footprint (nodeContext c); exact BalancedParameterContext.footprint_ge_four _)
    (fun right p hh => by
      rw [childInput_nodeContext]
      exact BalancedParameterContext.child_footprint_le right _ hh) root q hq
  have hp : (nodeContext (origin q)).length ≤ footprint (nodeContext (origin q)) := Nat.le_max_left _ _
  have hr := (nodeContext_length_le (origin root)).trans (origin_length_le root)
  exact (hp.trans hm).trans ((BalancedParameterContext.footprint_le _).trans (by omega))

theorem reachable_original_length_le (root q : List Bool) (hq : tasks L a root q) :
    (original (nodeContext (origin q))).length ≤ root.length := by
  have hm := reachable_measure_le L a (fun c => (original (nodeContext c)).length)
    (fun _ => Nat.zero_le _)
    (fun right p _ => by rw [childInput_nodeContext, BalancedParameterContext.original_child]) root q hq
  exact hm.trans ((pairFst_length_le _).trans ((nodeContext_length_le _).trans (origin_length_le root)))

theorem reachable_modulusWord_length_le (root q : List Bool) (hq : tasks L a root q) :
    (pairSnd (origin q)).length ≤ root.length := by
  have hm := reachable_measure_le L a (fun c => (pairSnd c).length)
    (fun _ => Nat.zero_le _)
    (fun right p _ => by simp only [childInput, matrixPacket, pairSnd_pair]; exact le_refl _) root q hq
  exact hm.trans ((pairSnd_length_le _).trans (origin_length_le root))

end LeanCanny.Algebra.CannyBalancedTaskRouting
