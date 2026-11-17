/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.SourceCoordinateCoefficients
public import LeanCanny.CountingHierarchy.BinaryPolynomialEvaluation

/-! # Actual coordinate characteristic polynomials from the source evaluator -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial

noncomputable def coordinatePolynomialValue (p n d u i t : ℕ) (value : List ℕ → ℕ) : ℕ :=
  binaryPolynomialValue p ((d + 1) ^ n) t
    (fun k => zeroCoordinateCoefficientValue p n d u i k value)

theorem coordinatePolynomialValue_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p n d u i t : α → ℕ} {value : α × List ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hn : ComputableInPolyTime n enc encUnary)
    (hd : ComputableInPolyTime d enc encNat) (hu : ComputableInPolyTime u enc encNat)
    (hi : ComputableInPolyTime i enc encNat) (ht : ComputableInPolyTime t enc encNat)
    (hv : value ∈ CountingFunction a (encPair enc (encList encNat)) encNat) :
    (fun w => coordinatePolynomialValue (p w) (n w) (d w) (u w) (i w) (t w)
      (fun y => value (w, y))) ∈ CountingFunction (a + 10) enc encNat := by
  have hf := ComputableInPolyTime.fst enc encNat
  have hv' := CountingFunction.preprocess (input := encPair (encPair enc encNat) (encList encNat)) hv
    (g := fun q : (α × ℕ) × List ℕ => (q.1.1, q.2)) (by fun_prop)
  have hc := zeroCoordinateCoefficientValue_mem (Decoder.pair E Decoder.nat) (hp.comp hf) (hn.comp hf)
    (hd.comp hf) (hu.comp hf) (hi.comp hf) (ComputableInPolyTime.snd _ _) hv'
  have h := binaryPolynomialValue_mem E hp
    (ComputableInPolyTime.binary_pow' (ComputableInPolyTime.binary_add' hd (.const 1)) hn) ht hc
  simpa only [coordinatePolynomialValue, Function.comp_apply, Nat.add_assoc] using h

theorem coordinatePolynomialValue_cast {p n : ℕ} [Fact p.Prime] (d : ℕ) (hd : 1 ≤ d)
    (F : MvPolynomial (Fin n) ℤ) (hF : F.totalDegree ≤ d + 1) (u t : ℕ) (i : Fin n)
    (hcut : criticalCoefficientPrimeCutoff n d < p) (value : List ℕ → ℕ)
    (hv : ∀ y, (value y : ZMod p) = MvPolynomial.eval₂ (Int.castRingHom (ZMod p))
      (fun j : Fin n => (y[j.val]?.getD 0 : ZMod p)) F) :
    (coordinatePolynomialValue p n d u i.val t value : ZMod p) =
      (parametricCoordinatePolynomial d F hF i).eval₂ (parameterEvaluation (u : ZMod p)) (t : ZMod p) :=
  binaryPolynomialValue_cast _ _ _ t (parametricCoordinatePolynomial_natDegree d F hF i).le _
    (fun k _ => sourceCoordinateCoefficient_cast d hd F hF u k i hcut value hv)

end LeanCanny.CountingHierarchy
