/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.Controlled
public import LeanCanny.CountingHierarchy.BinaryModularProduct

/-! # Uniform binary-indexed products of controlled polynomial families -/

@[expose] public section

namespace LeanCanny.CountingHierarchy.Controlled

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial
open scoped BigOperators Classical

noncomputable def boundedProduct {α : Type} {n : α → ℕ}
    {P : (w : α) → ℕ → MvPolynomial (Fin (n w)) ℤ} {enc : α ↪ List Bool} {a : ℕ}
    (C : Controlled (fun q : α × ℕ => P q.1 q.2) (encPair enc encNat) a) (E : Decoder enc)
    (hn : ComputableInPolyTime n enc encUnary) (N D b cutoff : α → ℕ)
    (hN : ComputableInPolyTime N enc encNat) (hD : ComputableInPolyTime D enc encNat)
    (hb : ComputableInPolyTime b enc encNat) (hcut : ComputableInPolyTime cutoff enc encNat)
    (hdeg : ∀ w i, i < N w → (P w i).totalDegree ≤ D w)
    (hmass : ∀ w i, i < N w → LeanCanny.Algebra.MvMass.mass (P w i) ≤ 2 ^ b w)
    (hcutoff : ∀ w i, i < N w → C.cutoff (w, i) ≤ cutoff w) :
    Controlled (fun w => ∏ i ∈ Finset.range (N w), P w i) enc (a + 3) where
  arity_computable := hn
  degreeBound w := N w * D w
  degree_computable := ComputableInPolyTime.binary_mul' hN hD
  degree_le w := (totalDegree_finsetProd _ _).trans (by
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_id] using
      Finset.sum_le_sum (fun i hi => hdeg w i (Finset.mem_range.mp hi)))
  massExponent w := N w * b w
  mass_computable := ComputableInPolyTime.binary_mul' hN hb
  mass_le w := by
    apply (LeanCanny.Algebra.MvMass.prod_le _ _).trans
    calc
      _ ≤ ∏ _i ∈ Finset.range (N w), 2 ^ b w :=
        Finset.prod_le_prod (fun i hi => hmass w i (Finset.mem_range.mp hi))
      _ = (2 ^ b w) ^ N w := by simp
      _ = 2 ^ (N w * b w) := by rw [← pow_mul, Nat.mul_comm]
  cutoff := cutoff
  cutoff_computable := hcut
  evaluate q := binaryModularProduct q.2.1 (N q.1) (fun i => C.evaluate ((q.1, i), q.2)) % q.2.1
  evaluate_mem := by
    have hterms : (fun q : (α × (ℕ × List ℕ)) × ℕ => C.evaluate ((q.1.1, q.2), q.1.2)) ∈
        CountingFunction a (encPair (encEvaluation enc) encNat) encNat :=
      CountingFunction.preprocess C.evaluate_mem (by fun_prop)
    have hN' := hN.comp (ComputableInPolyTime.fst enc (encPair encNat (encList encNat)))
    have hp : ComputableInPolyTime (fun q : α × (ℕ × List ℕ) => q.2.1)
        (encEvaluation enc) encNat := (ComputableInPolyTime.fst _ _).comp (ComputableInPolyTime.snd _ _)
    have hprod := binaryModularProduct_mem (Decoder.pair E (Decoder.pair Decoder.nat (Decoder.list Decoder.nat))) hp hN' hterms
    simpa only [Function.comp_apply] using CountingFunction.nat_mod hprod (CountingFunction.of_polyTime hp)
  evaluate_eq w p z hp hc := by
    let : NeZero p := ⟨hp.ne_zero⟩
    let : Fact p.Prime := ⟨hp⟩
    have hcast : ((binaryModularProduct p (N w) (fun i => C.evaluate ((w, i), p, z)) % p : ℕ) : ZMod p) =
        eval₂ (Int.castRingHom (ZMod p)) (fun i : Fin (n w) => (z[i.val]?.getD 0 : ZMod p))
          (∏ i ∈ Finset.range (N w), P w i) := by
      rw [ZMod.natCast_mod, binaryModularProduct_cast, MvPolynomial.eval₂_prod, Finset.prod_range]
      apply Finset.prod_congr rfl
      intro i _
      rw [C.evaluate_eq (w, i.val) p z hp ((hcutoff w i.val i.isLt).trans_lt hc)]
      exact ZMod.natCast_zmod_val _
    have hv := congrArg ZMod.val hcast
    simpa only [ZMod.val_natCast, Nat.mod_mod, evaluation] using hv

end LeanCanny.CountingHierarchy.Controlled
