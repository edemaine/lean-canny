/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.SourceCriticalCoefficients
public import LeanCanny.CountingHierarchy.SparseRootLabelEvaluation
public import LeanCanny.CountingHierarchy.CodedRootLabelCorrectness
public import LeanCanny.CountingHierarchy.NativeNormBounds

/-! # Sparse root-label evaluation constructed solely from source evaluations -/

public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM

@[expose] noncomputable def sourceRootLabelValue (p n d b z : ℕ) (data : List (ℕ × ℕ))
    (value : List ℕ → ℕ) : ℕ :=
  let D := (d + 1) ^ n
  let N := criticalRootLabelLength n d
  sparseRootLabelResidue p D N (criticalLabelInputMassExponent n d b) z
    (modularSub p (criticalCutoffResidue p n d b) z)
    (fun m => criticalCoefficientValue p n d b m value)
    (codedRootLabelOrders D N data) (codedRootLabelTarget p data)

/-- No coefficient or derivative oracle is supplied: the source evaluator
constructs the critical coefficients, their derivative tests, and the label.
For source level zero the resulting evaluator is in `F_13`. -/
theorem sourceRootLabelValue_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p n d b z : α → ℕ} {data : α → List (ℕ × ℕ)}
    {value : α × List ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hn : ComputableInPolyTime n enc encUnary)
    (hd : ComputableInPolyTime d enc encNat) (hb : ComputableInPolyTime b enc encNat)
    (hz : ComputableInPolyTime z enc encNat)
    (hdata : ComputableInPolyTime data enc encRootLabelCode)
    (hv : value ∈ CountingFunction a (encPair enc (encList encNat)) encNat) :
    (fun w => sourceRootLabelValue (p w) (n w) (d w) (b w) (z w) (data w)
      (fun y => value (w, y))) ∈ CountingFunction (a + 13) enc encNat := by
  have hD := ComputableInPolyTime.binary_pow' (ComputableInPolyTime.binary_add' hd (.const 1)) hn
  have hN := criticalRootLabelLength_polyTime hn hd
  have hM := criticalLabelInputMassExponent_polyTime hn hd hb
  have horders := codedRootLabelOrders_polyTime hD hN hdata
  have hbase := modularSub_polyTime hp (criticalCutoffResidue_polyTime hp hn hd hb) hz
  have hf := ComputableInPolyTime.fst enc encNat
  have hi := ComputableInPolyTime.snd enc encNat
  have hv' := CountingFunction.preprocess
    (input := encPair (encPair enc encNat) (encList encNat)) hv
    (g := fun q : (α × ℕ) × List ℕ => (q.1.1, q.2)) (by fun_prop)
  have hcoeff := criticalCoefficientValue_mem (Decoder.pair E Decoder.nat)
    (hp.comp hf) (hn.comp hf) (hd.comp hf) (hb.comp hf) hi hv'
  have htarget := codedRootLabelTarget_polyTime (hp.comp hf) hi (hdata.comp hf)
  have hlabel := sparseRootLabelResidue_mem E hp hD hN hM hz
    (CountingFunction.of_polyTime hbase) horders hcoeff (CountingFunction.of_polyTime htarget)
  have hmax : max (a + 9) 3 = a + 9 := by omega
  simpa only [sourceRootLabelValue, hmax, Nat.add_assoc, Function.comp_apply] using hlabel

/-- Correctness for the actual bounded integer label in the finite criterion.
Every input code decodes to an allowed list, independently of its raw length. -/
theorem sourceRootLabelValue_cast {p n : ℕ} [Fact p.Prime]
    (d : ℕ) (hd : 1 ≤ d) (b z : ℕ) (F : MvPolynomial (Fin n) ℤ)
    (hF : F.totalDegree ≤ d + 1) (hcut : criticalCoefficientPrimeCutoff n d < p)
    (data : List (ℕ × ℕ)) (value : List ℕ → ℕ)
    (hv : ∀ y, (value y : ZMod p) = MvPolynomial.eval
      (fun i : Fin n => ((y[i.val]?.getD 0 : ℕ) : ZMod p)) (F.map (Int.castRingHom (ZMod p)))) :
    (sourceRootLabelValue p n d b z data value : ZMod p) =
      (sparseIntegerRootLabel (finiteCriticalPolynomial d b F hF)
        (Polynomial.C (criticalIntegerCutoff n d b) - Polynomial.X)
        (criticalRootLabelLength n d) (criticalLabelInputMassExponent n d b)
        (codedRootLabel ((d + 1) ^ n) (criticalRootLabelLength n d) (by positivity) data)).eval₂
          (Int.castRingHom (ZMod p)) (z : ZMod p) := by
  have hD : (finiteCriticalPolynomial d b F hF).natDegree ≤ (d + 1) ^ n := by
    rw [finiteCriticalPolynomial_eq_charpoly d hd b F hF,
      Matrix.charpoly_natDegree_eq_dim, PurePowerResidue.card_normalIndex]
  have hp : (d + 1) ^ n < p := by unfold criticalCoefficientPrimeCutoff at hcut; omega
  have hcoeff (j : ℕ) (_hj : j ≤ (d + 1) ^ n) :
      (criticalCoefficientValue p n d b j value : ZMod p) =
        ((finiteCriticalPolynomial d b F hF).map (Int.castRingHom (ZMod p))).coeff j := by
    rw [Polynomial.coeff_map]
    exact criticalCoefficientValue_cast d hd b j F hF hcut value hv
  have hbase : (modularSub p (criticalCutoffResidue p n d b) z : ZMod p) =
      (Polynomial.C (criticalIntegerCutoff n d b) - Polynomial.X).eval₂
        (Int.castRingHom (ZMod p)) (z : ZMod p) := by
    rw [modularSub_cast (Fact.out : p.Prime).pos, criticalCutoffResidue_cast,
      Polynomial.eval₂_sub, Polynomial.eval₂_C, Polynomial.eval₂_X]
    rfl
  rw [sourceRootLabelValue, ← codedRootLabel_orders _ _ (by positivity) data]
  exact sparseRootLabelResidue_cast _ _ _ z _ _ _ _ hD hp hcoeff hbase
    (fun i => codedRootLabelTarget_cast (by positivity) data i)

end LeanCanny.CountingHierarchy
