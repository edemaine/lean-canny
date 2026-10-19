/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Algebra.BerkowitzSuspended

/-!
# Reachable parent and child bounds for modular determinants

These bounds include the retained original context and the child query packet.
They require original-entry correctness, without assuming FP access to the
layered matrix or bounding the original dimension in unary.
-/

@[expose] public section

namespace LeanCanny.Algebra.Berkowitz.Suspended
open Complexity
open LeanCanny.Encoding
open MatrixPower
open LeanCanny.Computation

theorem parent_length (a : FactorChild.Access) (c : List Bool) (m n : ℕ) [NeZero m]
    (A : Matrix (Fin n) (Fin n) (ZMod m)) (hb : FactorChild.CorrectAt a c m A) (u : ℕ) :
    ((SubroutineIteration.abstractStep (program a) (childTime a))^[u] (init a c)).length ≤
      2 * c.length + 2 + 64 * (3 * n.size + m.size + 2) ^ 2 := by
  rw [iterate_eq, init_encode a c m n hb.dimension]
  exact controller_residue_length _ c m A (ops_correctAt a c m n A hb) 0 u

theorem requested_length (a : FactorChild.Access) (c : List Bool) (m n : ℕ) [NeZero m]
    (A : Matrix (Fin n) (Fin n) (ZMod m)) (hb : FactorChild.CorrectAt a c m A) (u : ℕ)
    (hr : (program a).request
      ((SubroutineIteration.abstractStep (program a) (childTime a))^[u] (init a c)) = true)
    (v : ℕ) (hv : v ≤ childTime a
      ((SubroutineIteration.abstractStep (program a) (childTime a))^[u] (init a c))) :
    let p := (SubroutineIteration.abstractStep (program a) (childTime a))^[u] (init a c)
    ((program a).advance^[v] ((program a).start p)).length ≤
      2 * (Controller.entryInput p).length + 2 + 64 * (2 * (n + 2).size + m.size + 1) ^ 2 := by
  obtain ⟨i, j, hp⟩ := requested_packet a c m n A hb u hr
  dsimp only
  generalize (SubroutineIteration.abstractStep (program a) (childTime a))^[u] (init a c) = parent
    at hp hv ⊢
  simp only [childTime, hp] at hv
  simp only [program, Controller.entryProgram, hp]
  exact FactorChild.run_length a _ m n _ _ _ _ A (by simpa only [pairFst_pair] using hb)
    (FactorChild.decoded_packet a c n i.val j.val hb.dimension) v hv

theorem requested_time_le (a : FactorChild.Access) (c : List Bool) (m n : ℕ) [NeZero m]
    (A : Matrix (Fin n) (Fin n) (ZMod m)) (hb : FactorChild.CorrectAt a c m A) (u : ℕ)
    (hr : (program a).request
      ((SubroutineIteration.abstractStep (program a) (childTime a))^[u] (init a c)) = true) :
    childTime a ((SubroutineIteration.abstractStep (program a) (childTime a))^[u] (init a c)) ≤
      2 ^ (((n + 2).size + 2) * (n + 2).size + 1) := by
  obtain ⟨i, j, hp⟩ := requested_packet a c m n A hb u hr
  generalize (SubroutineIteration.abstractStep (program a) (childTime a))^[u] (init a c) = parent
    at hp ⊢
  simp only [childTime, hp]
  exact FactorChild.time_le a _ m n _ _ _ _ A (by simpa only [pairFst_pair] using hb)
    (FactorChild.decoded_packet a c n i.val j.val hb.dimension)

end LeanCanny.Algebra.Berkowitz.Suspended
