/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.DerivativeEvaluation
public import LeanCanny.CountingHierarchy.DerivativeRootLabels
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString

/-! # Uniform evaluation of sparse derivative tests

An order of zero encodes a missing test; actual derivative orders are positive.
The distinguished test at index zero is evaluated separately.
-/

public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM

@[expose] noncomputable def binaryDerivativeTestResidue (p D z base : ℕ)
    (c : ℕ → ℕ) (orders : List ℕ) (i : ℕ) : ℕ :=
  if i = 0 then base else
    let k := (orders[i - 1]?).getD 0
    if k = 0 then 0 else derivativeResidue p D k z c

theorem binaryDerivativeTestResidue_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p D z base : α → ℕ} {orders : α → List ℕ}
    {c : α × ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat)
    (hD : ComputableInPolyTime D enc encNat)
    (hz : ComputableInPolyTime z enc encNat)
    (hbase : base ∈ CountingFunction (max a 3 + 1) enc encNat)
    (horders : ComputableInPolyTime orders enc (encList encNat))
    (hc : c ∈ CountingFunction a (encPair enc encNat) encNat) :
    (fun q : α × ℕ => binaryDerivativeTestResidue (p q.1) (D q.1) (z q.1) (base q.1)
      (fun j => c (q.1, j)) (orders q.1) q.2) ∈
        CountingFunction (max a 3 + 1) (encPair enc encNat) encNat := by
  have hf := ComputableInPolyTime.fst enc encNat
  have hindex := ComputableInPolyTime.binary_sub'
    (ComputableInPolyTime.snd enc encNat) (ComputableInPolyTime.const 1)
  have hk : ComputableInPolyTime (fun q : α × ℕ => ((orders q.1)[q.2 - 1]?).getD 0)
      (encPair enc encNat) encNat := by
    simpa only [List.getD_eq_getElem?_getD, Function.comp_apply] using
      ComputableInPolyTime.listGetD_binary 0 (horders.comp hf) hindex
  have hc' := CountingFunction.preprocess
    (input := encPair (encPair enc encNat) encNat) hc
    (g := fun q : (α × ℕ) × ℕ => (q.1.1, q.2)) (by fun_prop)
  have hdval := derivativeResidue_mem (Decoder.pair E Decoder.nat)
    (hp.comp hf) (hD.comp hf) hk (hz.comp hf) hc'
  have hkzero : ComputableInPolyTime
      (fun q : α × ℕ => decide (((orders q.1)[q.2 - 1]?).getD 0 = 0))
      (encPair enc encNat) encBool := by fun_prop
  have hmissing := CountingFunction.ite (CountingFunction.of_polyTime hkzero)
    (CountingFunction.of_polyTime (ComputableInPolyTime.const 0)) hdval
  have hizero : ComputableInPolyTime (fun q : α × ℕ => decide (q.2 = 0))
      (encPair enc encNat) encBool := by fun_prop
  simpa only [binaryDerivativeTestResidue, decide_eq_true_eq, Function.comp_apply] using
    CountingFunction.ite (CountingFunction.of_polyTime hizero)
      (CountingFunction.preprocess hbase hf) hmissing

/-- The list representation is the positive derivative order of each
actual test; absent entries evaluate to the zero polynomial. -/
theorem binaryDerivativeTestResidue_cast {p D N : ℕ} [Fact p.Prime]
    (q b₀ : Polynomial ℤ) (z base : ℕ) (c : ℕ → ℕ)
    (L : List (Fin D × SignType)) (hD : q.natDegree ≤ D) (hprime : D < p)
    (hc : ∀ j ≤ D, (c j : ZMod p) = (q.map (Int.castRingHom (ZMod p))).coeff j)
    (hbase : (base : ZMod p) = b₀.eval₂ (Int.castRingHom (ZMod p)) (z : ZMod p))
    (i : Fin (N + 1)) :
    (binaryDerivativeTestResidue p D z base c (L.map (fun t => t.1.val + 1)) i.val : ZMod p) =
      (derivativeLabelTests q b₀ N L i).eval₂ (Int.castRingHom (ZMod p)) (z : ZMod p) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simpa only [binaryDerivativeTestResidue, Fin.val_zero, ite_true,
      derivativeLabelTests, Fin.cases_zero] using hbase
  · simp only [binaryDerivativeTestResidue, Fin.val_succ, Nat.add_one_ne_zero,
      ite_false, Nat.add_sub_cancel, List.getElem?_map,
      derivativeLabelTests, Fin.cases_succ]
    cases he : L[j.val]? with
    | none => simp [derivativeListTest]
    | some t =>
      simp only [Option.map_some, Option.getD_some, Nat.add_one_ne_zero,
        ite_false, derivativeListTest, Option.elim_some]
      rw [derivativeResidue_cast (q.map (Int.castRingHom (ZMod p)))
        ((Polynomial.natDegree_map_le).trans hD) hprime c hc,
        Polynomial.iterate_derivative_map, Polynomial.eval_map]

end LeanCanny.CountingHierarchy
