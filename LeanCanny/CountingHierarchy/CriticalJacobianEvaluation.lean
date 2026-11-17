/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.CriticalPolynomialEvaluation
public import LeanCanny.CountingHierarchy.ModularMatrixDeterminant
public import LeanCanny.CountingHierarchy.PurePowerTrace

/-! # A uniform small-matrix evaluator for the actual critical Jacobian -/

public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial PurePowerResidue
open scoped Classical

@[expose] noncomputable def criticalJacobianEntryValue (p n ell u i j : ℕ) (z : List ℕ)
    (value : List ℕ → ℕ) : ℕ :=
  ((if i = j then ell * powMod p (z[i]?.getD 0) (ell - 1) else 0) +
    u * secondPartialResidue p n i j z value) % p

@[expose] noncomputable def criticalJacobianValue (p n ell u : ℕ) (z : List ℕ)
    (value : List ℕ → ℕ) : ℕ :=
  modularMatrixDeterminant p n (fun k =>
    criticalJacobianEntryValue p n ell u (k / n) (k % n) z value)

variable {α : Type} {enc : α ↪ List Bool} {a : ℕ}

theorem criticalJacobianEntryValue_mem (E : Decoder enc) {p n ell u i j : α → ℕ}
    {z : α → List ℕ} {value : α × List ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hn : ComputableInPolyTime n enc encUnary)
    (hell : ComputableInPolyTime ell enc encNat) (hu : ComputableInPolyTime u enc encNat)
    (hi : ComputableInPolyTime i enc encNat) (hj : ComputableInPolyTime j enc encNat)
    (hz : ComputableInPolyTime z enc (encList encNat))
    (hv : value ∈ CountingFunction a (encPair enc (encList encNat)) encNat) :
    (fun w => criticalJacobianEntryValue (p w) (n w) (ell w) (u w) (i w) (j w) (z w)
      (fun y => value (w, y))) ∈ CountingFunction (a + 1) enc encNat := by
  have htest := ComputableInPolyTime.decide_eq' hi hj
  have hx : ComputableInPolyTime (fun w => (z w)[i w]?.getD 0) enc encNat := by
    simpa only [List.getD_eq_getElem?_getD] using ComputableInPolyTime.listGetD_binary 0 hz hi
  have hdiagval := ComputableInPolyTime.binary_mul' hell
    (computableInPolyTime_powMod hp hx (ComputableInPolyTime.binary_sub' hell (.const 1)))
  have hdiag : ComputableInPolyTime
      (fun w => if i w = j w then ell w * powMod (p w) ((z w)[i w]?.getD 0) (ell w - 1) else 0)
      enc encNat := by
    simpa only [decide_eq_true_eq] using ComputableInPolyTime.ite' htest hdiagval (.const 0)
  have hsecond := secondPartialResidue_mem E hp hn hi hj hz hv
  have hsum := CountingFunction.map
    (CountingFunction.prod (CountingFunction.of_polyTime hdiag)
      (CountingFunction.nat_mul (CountingFunction.of_polyTime hu) hsecond)) ComputableInPolyTime.binary_add
  exact CountingFunction.nat_mod hsum (CountingFunction.of_polyTime hp)

theorem criticalJacobianValue_mem (E : Decoder enc) {p n ell u : α → ℕ}
    {z : α → List ℕ} {value : α × List ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hn : ComputableInPolyTime n enc encUnary)
    (hell : ComputableInPolyTime ell enc encNat) (hu : ComputableInPolyTime u enc encNat)
    (hz : ComputableInPolyTime z enc (encList encNat))
    (hv : value ∈ CountingFunction a (encPair enc (encList encNat)) encNat) :
    (fun w => criticalJacobianValue (p w) (n w) (ell w) (u w) (z w) (fun y => value (w, y))) ∈
      CountingFunction (a + 1) enc encNat := by
  have hf := ComputableInPolyTime.fst enc encNat
  have hk := ComputableInPolyTime.snd enc encNat
  have hnb := (ComputableInPolyTime.unary_to_binary.comp hn).comp hf
  have hi := ComputableInPolyTime.binary_div' hk hnb
  have hj := ComputableInPolyTime.binary_mod.comp (hk.prod hnb)
  have hv' := CountingFunction.preprocess
    (input := encPair (encPair enc encNat) (encList encNat)) hv
    (g := fun q : (α × ℕ) × List ℕ => (q.1.1, q.2)) (by fun_prop)
  have hentry := criticalJacobianEntryValue_mem (Decoder.pair E Decoder.nat)
    (hp.comp hf) (hn.comp hf) (hell.comp hf) (hu.comp hf) hi hj (hz.comp hf) hv'
  simpa only [criticalJacobianValue, Function.comp_apply] using
    modularMatrixDeterminant_mem hp hn hentry

theorem criticalJacobianEntryValue_cast {p n : ℕ} [Fact p.Prime]
    (F : MvPolynomial (Fin n) (ZMod p)) (ell u : ℕ) (i j : Fin n) (z : List ℕ)
    (value : List ℕ → ℕ) (hF : F.totalDegree < p - 1) (hp : 3 < p)
    (hv : ∀ y, (value y : ZMod p) = eval
      (fun k : Fin n => ((y[k.val]?.getD 0 : ℕ) : ZMod p)) F) :
    (criticalJacobianEntryValue p n ell u i.val j.val z value : ZMod p) =
      eval (fun k : Fin n => ((z[k.val]?.getD 0 : ℕ) : ZMod p))
        (pderiv j (X i ^ ell - criticalLower ell
          (fun k : Fin n => ((separatedCenters ell k : ℕ) : ZMod p)) (u : ZMod p) F i)) := by
  rw [criticalJacobianEntryValue, ZMod.natCast_mod, Nat.cast_add, Nat.cast_mul,
    secondPartialResidue_cast F i j z value hF hp hv]
  by_cases hij : i = j
  · subst j
    simp [criticalLower, pderiv_X,
      powMod_of_ne_zero (Fact.out : p.Prime).ne_zero]
  · have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
    simp [criticalLower, pderiv_X, hij, hval]

theorem criticalJacobianValue_cast {p n : ℕ} [Fact p.Prime]
    (F : MvPolynomial (Fin n) (ZMod p)) (ell u : ℕ) (z : List ℕ)
    (value : List ℕ → ℕ) (hF : F.totalDegree < p - 1) (hp : 3 < p)
    (hv : ∀ y, (value y : ZMod p) = eval
      (fun k : Fin n => ((y[k.val]?.getD 0 : ℕ) : ZMod p)) F) :
    (criticalJacobianValue p n ell u z value : ZMod p) =
      eval (fun k : Fin n => ((z[k.val]?.getD 0 : ℕ) : ZMod p))
        (jacobian ell (criticalLower ell
          (fun k : Fin n => ((separatedCenters ell k : ℕ) : ZMod p)) (u : ZMod p) F)) := by
  let point : Fin n → ZMod p := fun k => ((z[k.val]?.getD 0 : ℕ) : ZMod p)
  let A : Matrix (Fin n) (Fin n) (ZMod p) := fun i j => eval point
    (pderiv j (X i ^ ell - criticalLower ell
      (fun k : Fin n => ((separatedCenters ell k : ℕ) : ZMod p)) (u : ZMod p) F i))
  have hJ : eval point (jacobian ell (criticalLower ell
      (fun k : Fin n => ((separatedCenters ell k : ℕ) : ZMod p)) (u : ZMod p) F)) = A.det := by
    exact RingHom.map_det (eval point) (Matrix.of fun i j =>
      pderiv j (X i ^ ell - criticalLower ell
        (fun k : Fin n => ((separatedCenters ell k : ℕ) : ZMod p)) (u : ZMod p) F i))
  rw [criticalJacobianValue, hJ]
  apply modularMatrixDeterminant_cast A
  intro i j
  have hn : 0 < n := j.isLt.trans_le' (Nat.zero_le _)
  have hdiv : (i.val * n + j.val) / n = i.val := by
    rw [Nat.mul_comm i.val n, Nat.mul_add_div hn, Nat.div_eq_of_lt j.isLt, add_zero]
  have hmod : (i.val * n + j.val) % n = j.val := by
    simp [Nat.add_mod, Nat.mod_eq_of_lt j.isLt]
  rw [hdiv, hmod]
  exact criticalJacobianEntryValue_cast F ell u i j z value hF hp hv

end LeanCanny.CountingHierarchy
