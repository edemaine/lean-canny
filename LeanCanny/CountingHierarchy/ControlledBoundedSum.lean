/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.Controlled
public import LeanCanny.CountingHierarchy.NativeBinaryBounds
public import CslibFrontier.Computability.Complexity.Classes.CountingHierarchy.Range

/-! # Uniform binary-indexed sums of controlled polynomial families -/

@[expose] public section

namespace LeanCanny.CountingHierarchy.Controlled

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial
open scoped BigOperators Classical

noncomputable def boundedSum {α : Type} {n : α → ℕ}
    {P : (w : α) → ℕ → MvPolynomial (Fin (n w)) ℤ} {enc : α ↪ List Bool} {a : ℕ}
    (C : Controlled (fun q : α × ℕ => P q.1 q.2) (encPair enc encNat) a) (E : Decoder enc)
    (hn : ComputableInPolyTime n enc encUnary) (N D b cutoff : α → ℕ)
    (hN : ComputableInPolyTime N enc encNat) (hD : ComputableInPolyTime D enc encNat)
    (hb : ComputableInPolyTime b enc encNat) (hcut : ComputableInPolyTime cutoff enc encNat)
    (hdeg : ∀ w i, i < N w → (P w i).totalDegree ≤ D w)
    (hmass : ∀ w i, i < N w → LeanCanny.Algebra.MvMass.mass (P w i) ≤ 2 ^ b w)
    (hcutoff : ∀ w i, i < N w → C.cutoff (w, i) ≤ cutoff w) :
    Controlled (fun w => ∑ i ∈ Finset.range (N w), P w i) enc (a + 1) where
  arity_computable := hn
  degreeBound := D
  degree_computable := hD
  degree_le w := totalDegree_finsetSum_le (fun i hi => hdeg w i (Finset.mem_range.mp hi))
  massExponent w := b w + (N w).size
  mass_computable := ComputableInPolyTime.binary_add' hb (binarySize_polyTime hN)
  mass_le w := by
    apply (LeanCanny.Algebra.MvMass.sum_le _ _).trans
    calc
      _ ≤ ∑ _i ∈ Finset.range (N w), 2 ^ b w :=
        Finset.sum_le_sum (fun i hi => hmass w i (Finset.mem_range.mp hi))
      _ = N w * 2 ^ b w := by simp
      _ ≤ 2 ^ (N w).size * 2 ^ b w := Nat.mul_le_mul_right _ (Nat.lt_size_self _).le
      _ = 2 ^ (b w + (N w).size) := by rw [pow_add, Nat.mul_comm]
  cutoff := cutoff
  cutoff_computable := hcut
  evaluate q := (∑ i ∈ Finset.range (N q.1), C.evaluate ((q.1, i), q.2)) % q.2.1
  evaluate_mem := by
    have hterms : (fun q : (α × (ℕ × List ℕ)) × ℕ => C.evaluate ((q.1.1, q.2), q.1.2)) ∈
        CountingFunction a (encPair (encEvaluation enc) encNat) encNat :=
      CountingFunction.preprocess C.evaluate_mem (by fun_prop)
    have hN' := hN.comp (ComputableInPolyTime.fst enc (encPair encNat (encList encNat)))
    have hsum := CountingFunction.sum_range (Decoder.pair E (Decoder.pair Decoder.nat (Decoder.list Decoder.nat))) hterms hN'
    have hp : ComputableInPolyTime (fun q : α × (ℕ × List ℕ) => q.2.1)
        (encEvaluation enc) encNat := (ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.snd _ _)
    simpa only [Function.comp_apply] using CountingFunction.nat_mod hsum (CountingFunction.of_polyTime hp)
  evaluate_eq w p z hp hc := by
    let : NeZero p := ⟨hp.ne_zero⟩
    have hcast : ((∑ i ∈ Finset.range (N w), C.evaluate ((w, i), p, z)) % p : ZMod p) =
        eval₂ (Int.castRingHom (ZMod p)) (fun i : Fin (n w) => (z[i.val]?.getD 0 : ZMod p))
          (∑ i ∈ Finset.range (N w), P w i) := by
      rw [ZMod.natCast_mod, Nat.cast_sum, MvPolynomial.eval₂_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [C.evaluate_eq (w, i) p z hp ((hcutoff w i (Finset.mem_range.mp hi)).trans_lt hc)]
      exact ZMod.natCast_zmod_val _
    have hv := congrArg ZMod.val hcast
    simpa only [ZMod.val_natCast, Nat.mod_mod, evaluation] using hv

end LeanCanny.CountingHierarchy.Controlled
