/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import LeanCanny.Computation.NativeFixedWidthVectorPass
/-! # Polynomial state bounds and current-coordinate frames of reply tables -/
@[expose] public section
namespace LeanCanny.Computation.FixedWidthVectorPass
open LeanCanny.Encoding Turing.MultiTapeTM
set_option backward.isDefEq.respectTransparency false

def stateBound (A W : List Bool → ℕ) (q : List Bool) :=
  2 * q.length + 2 * (A q * W q).size + A q * W q + 2

theorem stateBound_unary (A W : List Bool → ℕ) (ha : UnaryFn A) (hw : UnaryFn W) : UnaryFn (stateBound A W) := by
  have HC : UnaryFn (fun q => (A q * W q).size) :=
    (UnaryFn.length (BinaryFn.ofUnary (ha.mul hw)).bits_mem_FP).of_eq (fun _ => BinaryNatCode.length_encode _)
  exact ((((UnaryFn.const 2).mul (UnaryFn.length id_mem_FP)).add ((UnaryFn.const 2).mul HC)).add (ha.mul hw)).add (UnaryFn.const 2)

theorem state_length (A W : List Bool → ℕ) (task answer : List Bool → List Bool) (q : List Bool) (t : ℕ) :
    (RecursiveFold.encState (((program A W task).controller.reference answer)^[t] ((program A W task).initial q))).length ≤
      stateBound A W q := by
  have H := (program A W task).orbit_length answer q t (A q * W q)
    (fun k hk => (partial_length A W task answer q k).trans_le hk)
  simpa only [program, stateBound, encNat_apply, Nat.size_eq_bits_len] using H

theorem requests_count (A W : List Bool → ℕ) (task answer : List Bool → List Bool)
    (budget : List Bool → ℕ) (q c : List Bool)
    (hc : (program A W task).controller.Requests answer budget q c) :
    (program A W task).controller.Requests answer (program A W task).count q c := by
  obtain ⟨t, ht, hh, hn, he⟩ := hc
  have HH := hh
  change (program A W task).controller.halted
    (((program A W task).controller.reference answer)^[t] ((program A W task).initial q)) = false at HH
  rw [(program A W task).reference_iterate] at HH
  have HH' : ¬ (program A W task).count q ≤ min t ((program A W task).count q) := of_decide_eq_false HH
  have HT : t < (program A W task).count q := by omega
  exact ⟨t, HT.le, hh, hn, he⟩

theorem requests_coordinate_any (A W : List Bool → ℕ) (task answer : List Bool → List Bool)
    (budget : List Bool → ℕ) (q c : List Bool)
    (hc : (program A W task).controller.Requests answer budget q c) :
    ∃ i < A q, c = task (pair q (BinaryNatCode.encode i)) :=
  requests_coordinate A W task answer q c (requests_count A W task answer budget q c hc)

end LeanCanny.Computation.FixedWidthVectorPass
