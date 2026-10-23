/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.Computation.PolyTimeIteration

/-! # Captured parameters for existing raw-packet loops

A commuting equation moves an unchanged packet field into the native loop's
captured parameter. Growth is measured against the original input.
-/

@[expose] public section
namespace LeanCanny.CapturedIteration
open Turing.MultiTapeTM

/-- The total pair parser cannot create more payload bits than it consumes. -/
theorem pair_components_length_le (z : List Bool) :
    2 * (pairFst z).length + (pairSnd z).length ≤ z.length := by
  have hf : 2 * (pairFst z).length ≤ z.length := by
    induction z using pairFst.induct <;> simp [pairFst] <;> omega
  rcases hu : unpair? z with _ | ⟨p, q⟩
  · simp only [pairSnd, hu, List.length_nil, Nat.add_zero]
    exact hf
  · have hz := unpair?_eq_some_iff.mp hu
    rw [hz, pairFst_pair, pairSnd_pair, pair_length]
    omega

theorem iterate_pair (F : List Bool → List Bool) (next : List Bool → List Bool → List Bool)
    (hstep : ∀ p s, F (pair p s) = pair p (next p s)) (p s : List Bool) (n : ℕ) :
    F^[n] (pair p s) = pair p ((next p)^[n] s) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, hstep, Function.iterate_succ_apply']

/-- Certify a raw loop through its evolving accumulator, retaining its wire format. -/
theorem mem_FP {F par seed : List Bool → List Bool} {count growth : List Bool → ℕ}
    (next : List Bool → List Bool → List Bool)
    (hF : F ∈ FP) (hp : par ∈ FP) (hs : seed ∈ FP) (hn : UnaryFn count)
    (hstep : ∀ p s, F (pair p s) = pair p (next p s))
    (hgrowth : PolyBounded List.length growth)
    (hle : ∀ x s, (next (par x) s).length ≤ s.length + growth x) :
    (fun x => F^[count x] (pair (par x) (seed x))) ∈ FP := by
  have hraw := pairSnd_mem_FP.comp
    (hF.comp (pair_computable (ComputableTidilyInPolyTime.fst encBits encBits)
      (ComputableTidilyInPolyTime.snd encBits encBits)))
  have hnext : ComputableTidilyInPolyTime (fun p : List Bool × List Bool => next p.1 p.2)
      (encPair encBits encBits) encBits := hraw.of_enc_eq fun p => by
    simpa only [encBits_apply, pairSnd_pair, Function.comp_apply] using (congrArg pairSnd (hstep p.1 p.2)).symm
  have hloop := ComputableTidilyInPolyTime.iterateWith_of_bounded_growth
    hp hn hs hnext hgrowth hle
  exact (pair_computable hp hloop).of_enc_eq fun x =>
    iterate_pair F next hstep (par x) (seed x) (count x)

end LeanCanny.CapturedIteration
