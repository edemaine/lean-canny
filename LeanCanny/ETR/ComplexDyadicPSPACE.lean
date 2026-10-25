/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.ETR.ComplexDyadicCircuit
public import LeanCanny.ETR.ComplexCircuitPSPACE

/-! # Native tests for a shared denominator-cleared equation

Appending the dyadic network to an existing source network preserves all its
constraints. The normalized equation is tested by the completed complex ETR
procedure, with a polynomial-time query writer and a binary exponent.
-/

@[expose] public section
namespace LeanCanny.ETR.ComplexCircuit.Dyadic
open LeanCanny.Encoding.Brackets LeanCanny.Computation
open scoped Classical

def zeroQuery (prior : List Gate) (source start : ℕ) (bits : List Bool) : List Gate :=
  prior ++ gates source start bits ++ [.zero (output start bits)]

theorem zeroQuery_satisfiable (prior : List Gate) (source start : ℕ) (bits : List Bool)
    (hsource : source < start) (hprior : ∀ g ∈ prior, g.arity ≤ start) :
    Satisfiable (zeroQuery prior source start bits) ↔
      ∃ env : ℕ → ℂ, (∀ g ∈ prior, g.Holds env) ∧
        (2 : ℂ) ^ Nat.fromBitsLE bits * env source - 1 = 0 := by
  constructor
  · rintro ⟨env, h⟩
    have hp : ∀ g ∈ prior, g.Holds env := by
      intro g hg
      exact h g (by simp only [zeroQuery, List.mem_append]; exact Or.inl (Or.inl hg))
    have hn : ∀ g ∈ gates source start bits, g.Holds env := by
      intro g hg
      exact h g (by simp only [zeroQuery, List.mem_append]; exact Or.inl (Or.inr hg))
    have hz := h (.zero (output start bits)) (by simp [zeroQuery])
    exact ⟨env, hp, (sound source start bits env hn).symm.trans hz⟩
  · rintro ⟨env, hp, hz⟩
    obtain ⟨out, he, hn, hv⟩ := exists_completion source start hsource bits env
    refine ⟨out, ?_⟩
    intro g hg
    simp only [zeroQuery, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with (hg | hg) | rfl
    · apply (Gate.holds_congr g env out (fun i hi => (he i (hi.trans_le (hprior g hg))).symm)).mp (hp g hg)
    · exact hn g hg
    · exact hv.trans hz

theorem zeroQuery_encode_mem_FP {prior : List Bool → List Gate}
    {source start : List Bool → ℕ} {bits : List Bool → List Bool}
    (hq : (fun c => encode (prior c)) ∈ FP) (hp : UnaryFn source) (hs : UnaryFn start)
    (he : bits ∈ FP) :
    (fun c => encode (zeroQuery (prior c) (source c) (start c) (bits c))) ∈ FP := by
  have hprior := mem_FP_comp hq contents_mem_FP
  have hnew := mem_FP_comp (encode_mem_FP hp hs he) contents_mem_FP
  have hzero := zeroGateBits_mem_FP ((productWire_unary hs he).add (UnaryFn.const 2))
  have h := mem_FP_comp (appendFn_mem_FP (appendFn_mem_FP hprior hnew) hzero) wrap_mem_FP
  apply mem_FP_of_eq h
  intro c
  simp only [Function.comp_apply, contents_encode, zeroGateBits_encode]
  simp only [encode_eq_wrap,
    zeroQuery, forest_append, forest_cons, forest_nil, List.append_nil, output]

theorem zeroQuery_evaluator {prior : List Bool → List Gate}
    {source start : List Bool → ℕ} {bits : List Bool → List Bool}
    (hq : (fun c => encode (prior c)) ∈ FP) (hp : UnaryFn source) (hs : UnaryFn start)
    (he : bits ∈ FP) (hsource : ∀ c, source c < start c)
    (hprior : ∀ c g, g ∈ prior c → g.arity ≤ start c) :
    SpaceFunction (fun c => [decide (∃ env : ℕ → ℂ, (∀ g ∈ prior c, g.Holds env) ∧
      (2 : ℂ) ^ Nat.fromBitsLE (bits c) * env (source c) - 1 = 0)]) := by
  have h := feasible_generated (zeroQuery_encode_mem_FP hq hp hs he)
  apply h.congr
  funext c
  simp only [zeroQuery_satisfiable _ _ _ _ (hsource c) (hprior c)]

end LeanCanny.ETR.ComplexCircuit.Dyadic
