/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.RecursiveFoldController

/-! # Uniform space evaluation of ranked recursive folds

The global recursive-stack compiler receives exact entry requests and the
fold's derived orbit bound. Clients provide a decreasing task rank and
bounds in the original root word, without an assumed child space bound.
-/

@[expose] public section
namespace LeanCanny.Computation.RecursiveFold.Program
open LeanCanny.Encoding Turing.MultiTapeTM
set_option backward.isDefEq.respectTransparency false

variable (P : RecursiveFold.Program)

theorem evaluator (hc : BinaryFn P.count) (hs : P.seed ∈ FP) (he : P.entryTask ∈ FP) (hf : P.finish ∈ FP)
    (answer : List Bool → List Bool) (tasks : List Bool → List Bool → Prop) (rank N R K V : List Bool → ℕ)
    (hN : BinaryFn N) (hR : UnaryFn R) (hK : UnaryFn K) (hV : UnaryFn V)
    (hroot : ∀ q, tasks q q)
    (hcount : ∀ root q, tasks root q → P.count q ≤ N root)
    (hvalue : ∀ root q, tasks root q → P.value answer q = answer q)
    (hchild : ∀ root q, tasks root q → ∀ i < P.count q,
      tasks root (P.child q i) ∧ rank (P.child q i) < rank q)
    (hrank : ∀ root q, tasks root q → rank q ≤ R root)
    (hword : ∀ root q, tasks root q → q.length ≤ K root)
    (hacc : ∀ root q, tasks root q → ∀ i ≤ P.count q, (P.partialValue answer q i).length ≤ V root)
    (hanswer : ∀ root q, tasks root q → (answer q).length ≤ K root) : SpaceFunction answer := by
  let B := fun root => 2 * K root + 2 * (encNat (N root)).length + V root + 2
  have HK : PolyBounded List.length K := by
    simpa only [encBits_apply, encUnary_apply, List.length_replicate] using hK.polyBounded_length
  have HV : PolyBounded List.length V := by
    simpa only [encBits_apply, encUnary_apply, List.length_replicate] using hV.polyBounded_length
  have HN : PolyBounded List.length (fun root => (encNat (N root)).length) := by
    simpa only [encBits_apply] using hN.polyBounded_length
  have HB : PolyBounded (fun q => (encBits q).length) B := by
    simpa only [encBits_apply] using
      ((((PolyBounded.const 2).mul HK).add ((PolyBounded.const 2).mul HN)).add HV).add (PolyBounded.const 2)
  refine ⟨P.controller.evaluatorOfOrbits (P.certificates hc hs he hf) answer rank P.count tasks N R B
    hN hR HB hroot (fun _ q _ => P.halted_after answer q) hcount ?_ ?_ hrank ?_ ?_ ?_⟩
  · intro root q t hq _ht hh
    exact (P.output_when_halted answer q t hh).trans (hvalue root q hq)
  · intro root q t hq ht hh hn
    have HR : P.controller.Requests answer P.count q
        (P.controller.query ((P.controller.reference answer)^[t] (P.controller.initial q))) :=
      ⟨t, ht, hh, hn, rfl⟩
    obtain ⟨i, hi, HE⟩ := (P.requests_iff answer q _).mp HR
    rw [HE]
    exact hchild root q hq i hi
  · intro root q hq
    have H := hword root q hq
    change q.length ≤ B root
    dsimp only [B]
    omega
  · intro root q hq t _ht
    have HS := P.orbit_length answer q t (V root) (hacc root q hq)
    have HI := ComputableTidilyInO.length_encNat_mono (hcount root q hq)
    have HW := hword root q hq
    change (RecursiveFold.encState ((P.controller.reference answer)^[t] (P.initial q))).length ≤ B root
    dsimp only [B]
    omega
  · intro root q hq
    have H := hanswer root q hq
    dsimp only [B]
    omega

end LeanCanny.Computation.RecursiveFold.Program
