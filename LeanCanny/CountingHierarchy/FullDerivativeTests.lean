/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.DerivativeEvaluation
public import LeanCanny.CountingHierarchy.FingerprintIntegerRootLabels

/-! # Uniform access to the full derivative family for prescribed-root labels -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM

noncomputable def fullDerivativeTestResidue (p D z : ℕ) (c : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i = 0 then 1 else derivativeResidue p D i z c

theorem fullDerivativeTestResidue_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p D z : α → ℕ} {c : α × ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hD : ComputableInPolyTime D enc encNat)
    (hz : ComputableInPolyTime z enc encNat)
    (hc : c ∈ CountingFunction a (encPair enc encNat) encNat) :
    (fun q : α × ℕ => fullDerivativeTestResidue (p q.1) (D q.1) (z q.1) (fun j => c (q.1, j)) q.2) ∈
      CountingFunction (max a 3 + 1) (encPair enc encNat) encNat := by
  have hf := ComputableInPolyTime.fst enc encNat
  have hc' := CountingFunction.preprocess (input := encPair (encPair enc encNat) encNat)
    hc (g := fun q : (α × ℕ) × ℕ => (q.1.1, q.2)) (by fun_prop)
  have hd := derivativeResidue_mem (Decoder.pair E Decoder.nat) (hp.comp hf) (hD.comp hf)
    (ComputableInPolyTime.snd enc encNat) (hz.comp hf) hc'
  have ht : ComputableInPolyTime (fun q : α × ℕ => decide (q.2 = 0)) (encPair enc encNat) encBool := by fun_prop
  simpa only [fullDerivativeTestResidue, decide_eq_true_eq, Function.comp_apply] using
    CountingFunction.ite (CountingFunction.of_polyTime ht) (CountingFunction.of_polyTime (ComputableInPolyTime.const 1)) hd

theorem fullDerivativeTestResidue_cast {p D : ℕ} [Fact p.Prime] (q : Polynomial ℤ)
    (hD : q.natDegree ≤ D) (hDp : D < p) (z : ℕ) (c : ℕ → ℕ)
    (hc : ∀ j ≤ D, (c j : ZMod p) = (q.coeff j : ZMod p)) (i : Fin (D + 1)) :
    (fullDerivativeTestResidue p D z c i.val : ZMod p) =
      (fingerprintTests q 1 D i).eval₂ (Int.castRingHom (ZMod p)) (z : ZMod p) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [fullDerivativeTestResidue, Fin.val_zero, ite_true, Nat.cast_one,
      fingerprintTests, Fin.cases_zero, Polynomial.eval₂_one]
  · have hi : j.succ.val ≠ 0 := by simp only [Fin.val_succ]; omega
    rw [fullDerivativeTestResidue, ite_eq_right hi]
    have he := derivativeResidue_cast (k := j.val + 1) (z := z) (q.map (Int.castRingHom (ZMod p)))
      (Polynomial.natDegree_map_le.trans hD) hDp c
      (fun k hk => by simpa only [Polynomial.coeff_map, Int.coe_castRingHom] using hc k hk)
    simpa only [fingerprintTests, Fin.cases_succ, Fin.val_succ,
      Polynomial.iterate_derivative_map, Polynomial.eval_map] using he

end LeanCanny.CountingHierarchy
