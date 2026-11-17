/-
Copyright (c) 2026 lean-canny contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import LeanCanny.CountingHierarchy.ZeroCenterAccess
public import LeanCanny.CountingHierarchy.SeparatedPotentialDegree

/-! # Native characteristic coefficients for coordinate multiplication -/

@[expose] public section

namespace LeanCanny.CountingHierarchy

open Cslib Cslib.Complexity Turing.MultiTapeTM MvPolynomial PurePowerResidue

noncomputable def zeroCoordinateCoefficientValue (p n d u i k : ℕ) (value : List ℕ → ℕ) : ℕ :=
  quotientCharacteristicValue p n (d + 1) ((d + 1) ^ n * (d + 2) + n * d) k
    (fun z => z[i]?.getD 0 % p)
    (fun z => criticalJacobianValue p n (d + 1) u z value)
    (fun j z => zeroLowerValue p n u j z value)

theorem zeroCoordinateCoefficientValue_mem {α : Type} {enc : α ↪ List Bool} {a : ℕ}
    (E : Decoder enc) {p n d u i k : α → ℕ} {value : α × List ℕ → ℕ}
    (hp : ComputableInPolyTime p enc encNat) (hn : ComputableInPolyTime n enc encUnary)
    (hd : ComputableInPolyTime d enc encNat) (hu : ComputableInPolyTime u enc encNat)
    (hi : ComputableInPolyTime i enc encNat) (hk : ComputableInPolyTime k enc encNat)
    (hv : value ∈ CountingFunction a (encPair enc (encList encNat)) encNat) :
    (fun w => zeroCoordinateCoefficientValue (p w) (n w) (d w) (u w) (i w) (k w)
      (fun y => value (w, y))) ∈ CountingFunction (a + 9) enc encNat := by
  have hell := ComputableInPolyTime.binary_add' hd (.const 1)
  have ha := zeroEvaluationAccess_mem E hp hn hell hu hv
  have hf := ComputableInPolyTime.fst enc (encList encNat)
  have hz := ComputableInPolyTime.snd enc (encList encNat)
  have hread : ComputableInPolyTime (fun q : α × List ℕ => q.2[i q.1]?.getD 0)
      (encPair enc (encList encNat)) encNat := by
    simpa only [List.getD_eq_getElem?_getD, Function.comp_apply] using
      ComputableInPolyTime.listGetD_binary 0 hz (hi.comp hf)
  have hobj := CountingFunction.nat_mod (a := a + 1) (CountingFunction.of_polyTime hread)
    (CountingFunction.of_polyTime (hp.comp hf))
  have hdim := ComputableInPolyTime.binary_pow' hell hn
  have hB := ComputableInPolyTime.binary_add'
    (ComputableInPolyTime.binary_mul' hdim (ComputableInPolyTime.binary_add' hd (.const 2)))
    (ComputableInPolyTime.binary_mul' (ComputableInPolyTime.unary_to_binary.comp hn) hd)
  have hc := quotientCharacteristicValue_mem E hp hn hell hB hk hobj ha.2.1 ha.2.2
  simpa only [zeroCoordinateCoefficientValue, Nat.add_assoc, Function.comp_apply] using hc

theorem zeroCoordinateCoefficientValue_eq {p n : ℕ} [Fact p.Prime] (d : ℕ) (hd : 1 ≤ d)
    (F : MvPolynomial (Fin n) (ZMod p)) (hF : F.totalDegree ≤ d + 1) (u k : ℕ) (i : Fin n)
    (hsmall : F.totalDegree < p - 1) (hp : 3 < p)
    (hcut : (d + 1) * ((d + 1) ^ n * (d + 2) + n * d + 1) + 1 < p)
    (hD : (d + 1) ^ n < p - 1) (hD₂ : (d + 1) ^ n * (d + 1) ^ n < p - 1)
    (value : List ℕ → ℕ)
    (hv : ∀ y, (value y : ZMod p) = eval (fun j : Fin n => (y[j.val]?.getD 0 : ZMod p)) F) :
    zeroCoordinateCoefficientValue p n d u i.val k value =
      ((multiplicationMatrix (by omega : 1 ≤ d + 1) (criticalLower (d + 1) (fun _ => 0) (u : ZMod p) F)
        (criticalLower_degree (d + 1) (by omega) _ _ _ hF) (MvPolynomial.X i)).charpoly.coeff k).val := by
  let r := criticalLower (d + 1) (fun _ : Fin n => (0 : ZMod p)) (u : ZMod p) F
  have hr (j : Fin n) : (r j).totalDegree ≤ d := by
    have := criticalLower_degree (d + 1) (by omega) (fun _ => (0 : ZMod p)) (u : ZMod p) F hF j
    dsimp only [r]
    omega
  have hnum (j : ℕ) (hj : j ≤ (d + 1) ^ n) :
      ((MvPolynomial.X i) ^ j * jacobian (d + 1) r).totalDegree ≤ (d + 1) ^ n * (d + 2) + n * d :=
    quotient_trace_numerator_degree d r hr (MvPolynomial.X i) (d + 2) ((d + 1) ^ n) j
      (by simp) hj
  exact quotientCharacteristicValue_eq d hd r hr (MvPolynomial.X i) hnum hcut hD hD₂
    (fun z => z[i.val]?.getD 0 % p)
    (fun z => criticalJacobianValue p n (d + 1) u z value)
    (fun j z => zeroLowerValue p n u j z value)
    (fun s _ => by simp only [ZMod.natCast_mod, MvPolynomial.eval_X])
    (fun s _ => zeroJacobianValue_cast F (d + 1) u _ value hsmall hp hv)
    (fun j s _ => zeroLowerValue_cast F (d + 1) u (by omega) j _ value hsmall hp hv)

end LeanCanny.CountingHierarchy
